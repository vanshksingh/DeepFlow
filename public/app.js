const $ = selector => document.querySelector(selector);
const board = $('#board');
const world = $('#world');
const scene = $('#scene');
const wires = $('#wires');
const minimap = $('#minimap');
const app = $('#app');

let graph;
let scopeId;
let selectedId;
let layoutAnchorFileId;
let selectedImportEdgeId;
let flowMode = false;
let traceMode = true;
let presentationMode = false;
let trace = new Set();
let traceEdges = new Set();
let sourceMode = 'live';
let autoRevealChanges = true;
let agentRevealDwellMs = 8000;
let agentRevealTimer = 0;
let agentRevealPath = null;
let agentRevealExpandedId = null;
let canvasAnim = 0;
const expandedFiles = new Set();
const expandedFolders = new Set();
const expandedModules = new Set();
const sourceFiles = new Set();
const pinned = new Set();
const offsets = new Map();
// The base map is intentionally independent of expansion state.  Expanding a
// container may make room for itself, but it must not redraw the whole repo.
const basePlacements = new Map();
let basePlacementKey = '';
const layoutMemory = new Map();
const recentPaths = new Map();
const reviewedPaths = new Set();
const activityItems = new Map();
const archivedActivity = [];
const undoStack = [];
const redoStack = [];
const canvas = { x: 0, y: 0, scale: 1 };
let drawFrame = 0;
let miniFrame = 0;
let activityFrame = 0;
let activityTimer = 0;
let directManipulationTimer = 0;
let reflowDrawUntil = 0;
let reflowFrame = 0;
let focusOrigin = null;
let focusedFileId = null;
let draggingTraceAnchorId = null;
let hoverId = null;
let hoverTimer = 0;
const floatPlacements = new Map();
const localOffsets = new Map(); // nested rearrange inside a parent canvas
const pinnedLayout = new Set(); // user-dragged frames skip gravity
let gravityTimer = 0;
let skipFlipOnce = false;
let flipBefore = null;
let clickAnchor = null; // expand under pointer — never camera-center on open

const FLOW_TYPES = new Set(['calls', 'dataflow', 'events', 'inherits', 'imports', 'references', 'reexports']);
const WALK_TYPES = new Set(['calls', 'dataflow', 'events', 'inherits']);
const CONTEXT_TYPES = new Set(['imports', 'references', 'reexports']);
const SOURCE_EXTENSIONS = new Set(['.js', '.mjs', '.cjs', '.ts', '.tsx', '.jsx', '.mts', '.cts', '.py']);
// The map opens with the two relationships people can read at a glance. Other
// semantic edge types remain available to the trace engine without flooding
// the architectural overview.
const edgeVisibility = { calls: true, dataflow: false, events: false, inherits: false, imports: true, references: false, reexports: false };
const edgeTypes = () => graph.edges.filter(edge => FLOW_TYPES.has(edge.type) && edgeVisibility[edge.type] !== false);
const SYNTHETIC_ROOT_ID = 'synthetic:root';
let syntheticRootFiles = []; // loose files under displayRoot, grouped into a "root" island
const layoutModes = new Map(); // parentId -> 'auto' | 'row' | 'column'
/** Real workspace root (unwrap single wrapper folders). Does not include synthetic nodes. */
function displayRootRaw() {
  const root = graph?.nodes.find(item => item.kind === 'folder' && item.depth === 0);
  if (!root) return null;
  const kids = graph.nodes.filter(item => item.parentId === root.id && (item.kind === 'folder' || item.kind === 'file'));
  if (kids.length === 1 && kids[0].kind === 'folder') {
    const inner = graph.nodes.filter(item => item.parentId === kids[0].id && (item.kind === 'folder' || item.kind === 'file'));
    if (inner.length > 2) return kids[0];
  }
  return root;
}
function syntheticRootNode() {
  const root = displayRootRaw();
  return {
    id: SYNTHETIC_ROOT_ID,
    kind: 'folder',
    label: 'root',
    path: `${root?.path || ''}/root`.replace(/\/{2,}/g, '/'),
    parentId: root?.id || null,
    depth: (root?.depth || 0) + 1,
    synthetic: true
  };
}
const node = id => {
  if (id === SYNTHETIC_ROOT_ID) return syntheticRootNode();
  return graph?.nodes.find(item => item.id === id);
};
const rootFolder = () => graph?.nodes.find(item => item.kind === 'folder' && item.depth === 0);
const children = id => {
  if (id === SYNTHETIC_ROOT_ID) return [...syntheticRootFiles];
  return (graph?.nodes || []).filter(item => item.parentId === id);
};
const folder = () => node(scopeId) || rootFolder();
const selected = () => node(selectedId);
const fileOf = item => item?.kind === 'module' ? node(item.fileId) : item?.kind === 'file' ? item : null;
const modules = file => children(file.id).filter(item => item.kind === 'module').sort((a, b) => a.loc.start - b.loc.start);
const filesBelow = item => {
  if (item?.id === SYNTHETIC_ROOT_ID || item?.synthetic) return [...syntheticRootFiles];
  return (graph?.nodes || []).filter(entry => entry.kind === 'file' && ancestors(entry).some(parent => parent.id === item.id));
};
const directItems = item => children(item.id).filter(child => child.kind === 'folder' || child.kind === 'file');
const escape = value => String(value ?? '').replaceAll('&', '&amp;').replaceAll('<', '&lt;').replaceAll('>', '&gt;');
// Distinct folder hues — translucent glass groups share a tint with their files.
const FOLDER_COLORS = [
  '#0d8a72', '#3b6fb8', '#b05a28', '#8f3f72', '#218ea0',
  '#6f8230', '#5a48a8', '#b4474a', '#1f7a62', '#9a6b18',
  '#3f6e8c', '#7a4570', '#177a7a', '#8a5634', '#4658a0',
  '#2d7a48', '#a05538', '#4a5f78'
];
const REGION_COLOR = {
  application: '#0d8a72',
  package: '#5a48a8',
  service: '#218ea0',
  infrastructure: '#9a6b18',
  docs: '#2d7a48',
  test: '#8f3f72',
  generated: '#6f8230',
  context: '#3f6e8c'
};
const hashHue = value => [...String(value || '')].reduce((sum, letter) => sum + letter.charCodeAt(0), 0);
const color = value => FOLDER_COLORS[hashHue(value) % FOLDER_COLORS.length];
function folderTint(item) {
  if (item?.id === SYNTHETIC_ROOT_ID || item?.synthetic) return '#4a5f78';
  const region = mapRegion(item);
  const base = REGION_COLOR[region] || REGION_COLOR.context;
  // Keep region identity, but salt by path so sibling folders stay distinct.
  const salt = hashHue(item.path || item.label);
  if (salt % 3 === 0) return base;
  const baseIndex = Math.max(0, FOLDER_COLORS.indexOf(base));
  return FOLDER_COLORS[(baseIndex + 1 + (salt % (FOLDER_COLORS.length - 1))) % FOLDER_COLORS.length];
}
function folderIcon(item) {
  if (item?.id === SYNTHETIC_ROOT_ID || item?.synthetic) return { g: '▤', c: '#4a5f78', region: 'context' };
  const region = mapRegion(item);
  const glyphs = {
    application: '▣', package: '◫', service: '◎', infrastructure: '⛭',
    docs: '¶', test: '✓', generated: '◇', context: '▤'
  };
  return { g: glyphs[region] || '▤', c: folderTint(item), region };
}
function fileTint(file) {
  const root = displayRootRaw();
  if (file?.parentId === root?.id) return folderTint(syntheticRootNode());
  const parent = node(file.parentId);
  return parent?.kind === 'folder' ? folderTint(parent) : color(file.path);
}
function fileGlyph(file) {
  const ext = String(file?.extension || '').toLowerCase();
  const table = {
    '.ts': { g: 'TS', c: '#3178c6' }, '.tsx': { g: 'TX', c: '#3178c6' },
    '.js': { g: 'JS', c: '#f0db4f' }, '.jsx': { g: 'JX', c: '#61dafb' },
    '.mjs': { g: 'MJ', c: '#f0db4f' }, '.cjs': { g: 'CJ', c: '#f0db4f' },
    '.py': { g: 'PY', c: '#3776ab' }, '.json': { g: '{}', c: '#cbb26a' },
    '.md': { g: 'MD', c: '#6b8cae' }, '.css': { g: 'CS', c: '#563d7c' },
    '.html': { g: 'HT', c: '#e34c26' }, '.sql': { g: 'SQ', c: '#e38c00' },
    '.yml': { g: 'YM', c: '#cb171e' }, '.yaml': { g: 'YM', c: '#cb171e' },
    '.toml': { g: 'TM', c: '#9c4121' }, '.sh': { g: 'SH', c: '#4eaa25' },
    '.go': { g: 'GO', c: '#00add8' }, '.rs': { g: 'RS', c: '#dea584' }
  };
  return table[ext] || { g: (ext.replace('.', '') || '•').slice(0, 2).toUpperCase(), c: fileTint(file) };
}

function ancestors(item) {
  const result = [];
  for (let cursor = item; cursor?.parentId; cursor = node(cursor.parentId)) result.unshift(cursor);
  return result;
}
function entryFile(item = rootFolder()) {
  const ranked = filesBelow(item).filter(file => SOURCE_EXTENSIONS.has(file.extension)).sort((a, b) => (b.entrypoint ? 1000 : 0) + semanticDegree(b) * 10 - ((a.entrypoint ? 1000 : 0) + semanticDegree(a) * 10) || a.path.localeCompare(b.path));
  return ranked[0] || filesBelow(item)[0] || graph.nodes.find(file => file.kind === 'file');
}
function sourceSeeds(item) {
  const file = fileOf(item);
  if (item?.kind === 'module') return [item.id];
  if (file) return [file.id, ...modules(file).map(module => module.id)];
  if (item?.kind === 'folder') {
    const files = filesBelow(item).filter(file => SOURCE_EXTENSIONS.has(file.extension)).slice(0, 180);
    const seeds = files.flatMap(file => [file.id, ...modules(file).map(module => module.id)]);
    if (seeds.length) return seeds;
    const entry = entryFile(item); return entry ? [entry.id, ...modules(entry).map(module => module.id)] : [];
  }
  return [];
}
function collectTrace(item) {
  const found = new Set(), edges = new Set();
  if (!item) return { nodes: found, edges };
  const seeds = sourceSeeds(item);
  seeds.forEach(id => found.add(id));
  const walk = (direction, maxDepth) => {
    const queue = seeds.map(id => ({ id, depth: 0 }));
    const seen = new Set(queue.map(entry => `${direction}:${entry.id}:0`));
    while (queue.length) {
      const current = queue.shift();
      if (current.depth >= maxDepth) continue;
      for (const edge of edgeTypes()) {
        const next = direction === 'out' && edge.from === current.id ? edge.to : direction === 'in' && edge.to === current.id ? edge.from : null;
        if (!next) continue;
        const contextOnly = CONTEXT_TYPES.has(edge.type);
        if (contextOnly && current.depth > 0) continue;
        edges.add(edge.id); found.add(edge.from); found.add(edge.to);
        if (WALK_TYPES.has(edge.type)) {
          const key = `${direction}:${next}:${current.depth + 1}`;
          if (!seen.has(key)) { seen.add(key); queue.push({ id: next, depth: current.depth + 1 }); }
        }
      }
    }
  };
  walk('in', 24); walk('out', 24);
  return { nodes: found, edges };
}
function traceFrom(item) {
  return collectTrace(item).nodes;
}
function mergeTrace(item) {
  const data = collectTrace(item);
  for (const id of data.nodes) trace.add(id);
  for (const id of data.edges) traceEdges.add(id);
}
function rebuildTrace() {
  trace = new Set();
  traceEdges = new Set();
  const item = selected();
  // Root overview stays quiet until hover/select of a real island.
  if (item && !(item.kind === 'folder' && item.depth === 0)) mergeTrace(item);
  for (const pin of pinned) mergeTrace(node(pin));
}
function hasTrace(item) {
  if (!item) return false;
  if (trace.has(item.id)) return true;
  if (item.kind === 'file') return modules(item).some(module => trace.has(module.id));
  if (item.kind === 'folder') return filesBelow(item).some(hasTrace);
  return false;
}
// Selection, pins, or hover preview drive which wires are live.
function traceActive() {
  const item = selected();
  return !!(item && (item.kind === 'file' || item.kind === 'module' || item.kind === 'folder')) || pinned.size > 0 || !!hoverId;
}
function exitFlow() {
  flowMode = false;
  focusOrigin = null;
  focusedFileId = null;
}
function outlineDim() {
  // Keep every frame fully readable — highlight via wires/hot, never fade modules out.
  return false;
}
function hoverPreviewTrace() {
  if (!traceMode || !hoverId || !graph) return null;
  const item = node(hoverId);
  if (!item) return null;
  // Prefer hover when nothing is selected, or when hovering a different node.
  if (selectedId && hoverId === selectedId) return null;
  return collectTrace(item);
}
function activeTraceEdges() {
  const preview = hoverPreviewTrace();
  if (preview) return preview.edges;
  return traceEdges;
}
function activeTraceNodes() {
  const preview = hoverPreviewTrace();
  if (preview) return preview.nodes;
  return trace;
}
function traceFiles() {
  const result = new Map();
  for (const id of trace) { const file = fileOf(node(id)); if (file) result.set(file.id, file); }
  const active = fileOf(selected()); if (active) result.set(active.id, active);
  return [...result.values()];
}
function traceFilesFor(item) {
  const result = new Map();
  for (const id of collectTrace(item).nodes) { const file = fileOf(node(id)); if (file) result.set(file.id, file); }
  const file = fileOf(item); if (file) result.set(file.id, file);
  return [...result.values()];
}
function semanticDegree(item) {
  const file = fileOf(item) || item;
  return edgeTypes().filter(edge => edge.from === item.id || edge.to === item.id || edge.from === file?.id || edge.to === file?.id).length;
}
function isInfrastructure(file) { return /(^|\/)(docs?|config|scripts|infra|assets)(\/|$)|^(README|package|pnpm-lock|yarn\.lock|tsconfig|eslint|docker)/i.test(`${file.path}/${file.label}`); }
function roleFor(item) {
  const path = item.path || item.label || '';
  if (/(^|\/)(apps?|gateway|console)(\/|$)/i.test(path)) return 'application';
  if (/(^|\/)services?(\/|$)/i.test(path)) return 'service';
  if (/(^|\/)packages?(\/|$)/i.test(path)) return 'package';
  if (/(^|\/)(docs?|README)/i.test(path)) return 'docs';
  if (/(^|\/)(config|infra|scripts|assets|generated|vendor)(\/|$)/i.test(path)) return 'support';
  if (isInfrastructure(item)) return 'support';
  return item.kind || 'context';
}
function mapRegion(item) {
  const path = `${item.path || ''}/${item.label || ''}`.toLowerCase();
  if (/(^|\/)(apps?|gateway|console|web|api|frontend|backend)(\/|$)/.test(path)) return 'application';
  if (/(^|\/)(services?|workers?|server|tasks?)(\/|$)/.test(path)) return 'service';
  if (/(^|\/)(packages?|shared|common|lib|core|utils?)(\/|$)/.test(path)) return 'package';
  if (/(^|\/)(tests?|__tests__|specs?|fixtures)(\/|$)/.test(path)) return 'test';
  if (/(^|\/)(generated|dist|build|coverage|vendor)(\/|$)/.test(path)) return 'generated';
  if (/(^|\/)(docs?|readme|examples?)(\/|$)/.test(path)) return 'docs';
  if (/(^|\/)(config|infra|scripts|assets|docker|deploy|migrations?)(\/|$)/.test(path) || isInfrastructure(item)) return 'infrastructure';
  if (/\.py$/.test(path) && /(^|\/)(main|manage|asgi|wsgi)\.py$/.test(path)) return 'application';
  return 'context';
}
const mapRegionPriority = { application: 0, package: 1, service: 2, infrastructure: 3, docs: 4, test: 5, generated: 6, context: 7 };
const RAIL_COPY = {
  application: { title: 'Apps', subtitle: 'entry points & UI' },
  package: { title: 'Packages', subtitle: 'shared libraries' },
  service: { title: 'Services', subtitle: 'runtime workers' },
  infrastructure: { title: 'Platform', subtitle: 'config & ops' },
  docs: { title: 'Docs', subtitle: 'guides & notes' },
  test: { title: 'Tests', subtitle: 'specs & fixtures' },
  generated: { title: 'Generated', subtitle: 'build artifacts' },
  context: { title: 'Workspace', subtitle: 'everything else' },
  upstream: { title: 'Calls in', subtitle: 'who reaches here' },
  focus: { title: 'Signal', subtitle: 'you are here' },
  downstream: { title: 'Calls out', subtitle: 'where it goes next' }
};
function railCopy(key) {
  return RAIL_COPY[key] || { title: key, subtitle: '' };
}
function relationshipCount(item) {
  if (item.kind === 'folder') {
    const ids = new Set(filesBelow(item).flatMap(file => [file.id, ...modules(file).map(module => module.id)]));
    return edgeTypes().filter(edge => ids.has(edge.from) || ids.has(edge.to)).length;
  }
  return semanticDegree(item);
}
function externalRelationshipCount(item) {
  if (item.kind !== 'folder') return semanticDegree(item);
  const ids = new Set(filesBelow(item).flatMap(file => [file.id, ...modules(file).map(module => module.id)]));
  return edgeTypes().filter(edge => ids.has(edge.from) !== ids.has(edge.to)).length;
}
function recentFor(file) {
  const at = recentPaths.get(file.path);
  if (!at || reviewedPaths.has(file.path) || Date.now() - at > 45_000) return false;
  return true;
}
function recentDescendants(folder) {
  return filesBelow(folder).filter(recentFor);
}
function fileOrder(a, b) {
  const rank = file => (file.entrypoint ? 60 : 0) + semanticDegree(file) * 5 + (isInfrastructure(file) ? 8 : 0) - (file.orphan ? 35 : 0);
  return rank(b) - rank(a) || a.path.localeCompare(b.path);
}
function folderItems(item) {
  // This is a document outline, not a trace-derived list: hierarchy and source
  // relevance stay predictable even when the selected trace changes.
  if (item?.id === SYNTHETIC_ROOT_ID || item?.synthetic) {
    return [...syntheticRootFiles].sort((a, b) => fileOrder(a, b));
  }
  // Hide loose files at display-root — they live inside the synthetic "root" island.
  const root = displayRootRaw();
  const list = item?.id === root?.id
    ? directItems(item).filter(child => child.kind === 'folder')
    : directItems(item);
  return list.sort((a, b) => {
    if (a.kind !== b.kind) return a.kind === 'folder' ? -1 : 1;
    if (a.kind === 'folder') return (mapRegionPriority[mapRegion(a)] ?? 9) - (mapRegionPriority[mapRegion(b)] ?? 9) || a.label.localeCompare(b.label);
    return fileOrder(a, b);
  });
}
function primaryTraceScore(item) {
  const score = hasTrace(item) ? 1000 : 0;
  const external = externalRelationshipCount(item);
  const local = Math.min(relationshipCount(item), 18);
  return score + external * 64 + local * 3 + (item.entrypoint ? 140 : 0) + (isInfrastructure(item) ? -28 : 0) - (item.orphan ? 140 : 0);
}
function connectionPressure(item, anchor) {
  const empty = { incoming: 0, outgoing: 0, total: 0, ratio: .5, role: 'context' };
  if (!anchor || !hasTrace(item)) return empty;
  const ids = item.kind === 'folder'
    ? new Set(filesBelow(item).flatMap(file => [file.id, ...modules(file).map(module => module.id)]))
    : new Set(item.kind === 'file' ? [item.id, ...modules(item).map(module => module.id)] : [item.id]);
  let incoming = 0, outgoing = 0;
  for (const edge of edgeTypes()) {
    if (!traceEdges.has(edge.id)) continue;
    if (ids.has(edge.to) && !ids.has(edge.from)) incoming++;
    if (ids.has(edge.from) && !ids.has(edge.to)) outgoing++;
  }
  const total = incoming + outgoing;
  const ratio = total ? incoming / total : .5;
  const isFocus = (item.kind === 'file' && item.id === anchor.id) || ids.has(anchor.id);
  return { incoming, outgoing, total, ratio, role: isFocus ? 'focus' : total ? 'connected' : 'context' };
}
function visibleOwnerForFile(file, items) {
  if (!file) return null;
  const direct = items.find(item => item.id === file.id);
  if (direct) return direct;
  return items.find(item => item.kind === 'folder' && ancestors(file).some(parent => parent.id === item.id)) || null;
}
function traceSpringPairs(items) {
  const pairs = new Map();
  for (const edge of edgeTypes()) {
    if (!traceEdges.has(edge.id)) continue;
    const fromFile = fileOf(node(edge.from));
    const toFile = fileOf(node(edge.to));
    const from = visibleOwnerForFile(fromFile, items);
    const to = visibleOwnerForFile(toFile, items);
    if (!from || !to || from.id === to.id) continue;
    const key = `${from.id}->${to.id}`;
    const value = pairs.get(key) || { from, to, weight: 0 };
    value.weight += edge.type === 'calls' ? 1.4 : edge.type === 'imports' ? .75 : 1;
    pairs.set(key, value);
  }
  return [...pairs.values()].sort((a, b) => b.weight - a.weight);
}
function entryItem(item = rootFolder()) {
  const direct = directItems(item);
  const ranked = direct.sort((a, b) => primaryTraceScore(b) - primaryTraceScore(a) || a.label.localeCompare(b.label));
  const bestFile = ranked.find(entry => entry.kind === 'file' && relationshipCount(entry) > 0);
  const bestFolder = ranked.find(entry => entry.kind === 'folder' && externalRelationshipCount(entry) > 0);
  return bestFile || bestFolder || ranked[0] || entryFile(item) || item;
}
function snapshot() {
  return { scopeId, selectedId, selectedImportEdgeId, layoutAnchorFileId, flowMode, focusedFileId, traceMode, presentationMode, expanded: [...expandedFiles], expandedFolders: [...expandedFolders], expandedModules: [...expandedModules], source: [...sourceFiles], pinned: [...pinned], offsets: [...offsets.entries()].map(([id, value]) => [id, { ...value }]), canvas: { ...canvas }, edgeVisibility: { ...edgeVisibility } };
}
function updateHistory() { $('#history-back').disabled = !undoStack.length; $('#history-forward').disabled = !redoStack.length; }
function remember() { if (!graph) return; undoStack.push(snapshot()); if (undoStack.length > 70) undoStack.shift(); redoStack.length = 0; updateHistory(); }
function restore(state) {
  scopeId = state.scopeId; selectedId = state.selectedId; selectedImportEdgeId = state.selectedImportEdgeId; layoutAnchorFileId = state.layoutAnchorFileId; flowMode = state.flowMode; focusedFileId = state.focusedFileId || null; focusOrigin = null; traceMode = state.traceMode ?? true; presentationMode = !!state.presentationMode;
  Object.assign(edgeVisibility, state.edgeVisibility || {});
  expandedFiles.clear(); state.expanded.forEach(id => expandedFiles.add(id)); expandedFolders.clear(); (state.expandedFolders || []).forEach(id => expandedFolders.add(id)); expandedModules.clear(); (state.expandedModules || []).forEach(id => expandedModules.add(id)); sourceFiles.clear(); state.source.forEach(id => sourceFiles.add(id)); pinned.clear(); state.pinned.forEach(id => pinned.add(id)); offsets.clear(); state.offsets.forEach(([id, value]) => offsets.set(id, value)); Object.assign(canvas, state.canvas);
  rebuildTrace(); render(); updateInspector();
}
function moveHistory(backward) {
  const from = backward ? undoStack : redoStack; const to = backward ? redoStack : undoStack; const state = from.pop();
  if (!state) return; to.push(snapshot()); restore(state); updateHistory();
}

function directedSets(file) {
  const forward = new Set(), backward = new Set();
  const walk = (direction, found) => {
    const seeds = [file?.id, ...modules(file || {}).map(module => module.id)].filter(Boolean);
    const queue = seeds.map(id => ({ id, depth: 0 })); queue.forEach(entry => found.add(entry.id));
    while (queue.length) {
      const current = queue.shift();
      if (current.depth >= 3) continue;
      for (const edge of edgeTypes()) {
        const next = direction === 'out' && edge.from === current.id ? edge.to : direction === 'in' && edge.to === current.id ? edge.from : null;
        if (!next || (CONTEXT_TYPES.has(edge.type) && current.depth > 0)) continue;
        found.add(edge.from); found.add(edge.to);
        if (WALK_TYPES.has(edge.type) && !queue.some(entry => entry.id === next)) queue.push({ id: next, depth: current.depth + 1 });
      }
    }
  };
  if (file) { walk('in', backward); walk('out', forward); }
  return { forward, backward };
}
function groupFolder(item, current) {
  let cursor = item.kind === 'folder' ? item : node(item.parentId);
  while (cursor?.parentId && cursor.parentId !== current.id) cursor = node(cursor.parentId);
  return cursor?.kind === 'folder' ? cursor : current;
}
function shouldInlineExpandFile(file) {
  return expandedFiles.has(file.id);
}
function folderContentHeight(item, depth = 0) {
  if (!expandedFolders.has(item.id) || depth > 4) return 0;
  const rows = folderItems(item).slice(0, 18).map(child => {
    if (child.kind === 'folder') return 52 + folderContentHeight(child, depth + 1) + (expandedFolders.has(child.id) ? 16 : 0);
    const expanded = shouldInlineExpandFile(child);
    const imports = expanded ? importSummaries(child).length : 0;
    const moduleRows = expanded ? Math.max(1, modules(child).length) : 0;
    const sourceRows = expanded ? modules(child).filter(module => expandedModules.has(module.id)).reduce((height, module) => height + moduleSourceHeight(child, module), 0) : 0;
    return 50 + (expanded ? 20 + imports * 40 + moduleRows * 42 + sourceRows : 0);
  });
  if (!rows.length) return 34;
  const columns = depth > 1 ? 1 : rows.length > 6 ? 3 : 2;
  return rows.reduce((sum, height, index) => index % columns ? sum : sum + Math.max(height, rows[index + 1] || 0), 0) + Math.max(0, Math.ceil(rows.length / columns) - 1) * 14;
}
function moduleSourceHeight(file, module) {
  const lineCount = Math.max(1, Math.min(80, (module.loc?.end || module.loc?.start || 1) - (module.loc?.start || 1) + 1));
  return 46 + lineCount * 21;
}
function displayModules(file) {
  return modules(file);
}
function cardSize(item, collapsed = false) {
  if (item.kind === 'folder') {
    const contentHeight = collapsed ? 0 : folderContentHeight(item);
    return { w: !collapsed && expandedFolders.has(item.id) ? 700 : 318, h: 108 + contentHeight + (contentHeight ? 34 : 0) };
  }
  const sourceHeight = !collapsed && expandedFiles.has(item.id) ? modules(item).filter(module => expandedModules.has(module.id)).reduce((height, module) => height + moduleSourceHeight(item, module), 0) : 0;
  const importHeight = !collapsed && expandedFiles.has(item.id) ? importSummaries(item).length * 40 + (importSummaries(item).length ? 12 : 0) : 0;
  const moduleHeight = !collapsed && expandedFiles.has(item.id) ? Math.max(0, modules(item).length * 44 + 46 + sourceHeight + importHeight) : 0;
  const liveHeight = recentFor(item) && item.git?.change ? 88 : 0;
  return { w: expandedFiles.has(item.id) ? 408 : 318, h: 108 + moduleHeight + liveHeight + (item.git?.change ? 22 : 0) };
}
function focusTraceFiles(item) {
  const owner = fileOf(item);
  if (!owner) return [];
  const files = new Map([[owner.id, owner]]);
  // Prefer the relationships directly owned by the selected module. This is
  // the useful first hop, rather than exploding into an entire call graph.
  for (const edge of edgeTypes()) {
    if (edge.from !== item.id && edge.to !== item.id && edge.from !== owner.id && edge.to !== owner.id) continue;
    const other = edge.from === item.id || edge.from === owner.id ? edge.to : edge.from;
    const file = fileOf(node(other)); if (file) files.set(file.id, file);
  }
  if (files.size === 1) for (const file of traceFilesFor(item).slice(0, 7)) files.set(file.id, file);
  return [...files.values()].slice(0, 9);
}
function captureFocusOrigin(file) {
  const element = scene.querySelector(`.card[data-id="${CSS.escape(file.id)}"], [data-inline-file="${CSS.escape(file.id)}"]`);
  if (!element) return null;
  const worldRect = world.getBoundingClientRect(), rect = element.getBoundingClientRect();
  return { id: file.id, x: (rect.left - worldRect.left) / canvas.scale, y: (rect.top - worldRect.top) / canvas.scale };
}
function captureItemOrigin(item) {
  if (!item) return null;
  const file = fileOf(item);
  const selector = item.kind === 'module'
    ? `[data-module="${CSS.escape(item.id)}"]`
    : file
    ? `.card[data-id="${CSS.escape(file.id)}"], [data-inline-file="${CSS.escape(file.id)}"]`
    : `.card[data-id="${CSS.escape(item.id)}"], [data-inline="${CSS.escape(item.id)}"]`;
  const element = scene.querySelector(selector);
  if (!element) return null;
  const worldRect = world.getBoundingClientRect(), rect = element.getBoundingClientRect();
  return { id: file?.id || item.id, x: (rect.left - worldRect.left) / canvas.scale, y: (rect.top - worldRect.top) / canvas.scale };
}
function captureCardOrigin(id) {
  const element = scene.querySelector(`.card[data-id="${CSS.escape(id)}"]`);
  if (!element) return null;
  const worldRect = world.getBoundingClientRect(), rect = element.getBoundingClientRect();
  return { id, x: (rect.left - worldRect.left) / canvas.scale, y: (rect.top - worldRect.top) / canvas.scale };
}
function rememberLayoutPositions() {
  const worldRect = world.getBoundingClientRect();
  scene.querySelectorAll('.card[data-id], [data-inline-file]').forEach(element => {
    const id = element.dataset.id || element.dataset.inlineFile;
    if (!id) return;
    const rect = element.getBoundingClientRect();
    layoutMemory.set(id, {
      x: (rect.left - worldRect.left) / canvas.scale,
      y: (rect.top - worldRect.top) / canvas.scale,
      w: rect.width / canvas.scale,
      h: rect.height / canvas.scale
    });
  });
}
function softenedPlacement(_item, target) {
  // Demo layout is intentional and fixed — no soft-snap interpolation.
  return target;
}
function requestLayoutSettle(item) {
  if (item) activateFocus(item);
  basePlacements.clear();
  basePlacementKey = '';
}
function expandAncestors(item) {
  if (!item) return;
  // Only open ancestor folders so a collapse isn't immediately undone.
  for (const parent of ancestors(item).filter(entry => entry.kind === 'folder')) expandedFolders.add(parent.id);
  const root = displayRootRaw();
  if (item.kind === 'file' && item.parentId === root?.id) expandedFolders.add(SYNTHETIC_ROOT_ID);
  pruneFolderDepth();
}
/** Prefer the inner workspace when a single wrapper folder was uploaded. */
function displayRoot() {
  return displayRootRaw();
}
/** Top-level islands: real folders + optional synthetic "root" for loose files. */
function topLevelItems(view = displayRoot()) {
  if (!view) return [];
  const kids = directItems(view);
  const folders = kids.filter(item => item.kind === 'folder');
  const files = kids.filter(item => item.kind === 'file');
  syntheticRootFiles = files;
  const items = [...folders];
  if (files.length) {
    items.push(syntheticRootNode());
    expandedFolders.add(SYNTHETIC_ROOT_ID);
  }
  return items.sort((a, b) => {
    if (a.id === SYNTHETIC_ROOT_ID) return 1;
    if (b.id === SYNTHETIC_ROOT_ID) return -1;
    if (a.kind !== b.kind) return a.kind === 'folder' ? -1 : 1;
    return (mapRegionPriority[mapRegion(a)] ?? 9) - (mapRegionPriority[mapRegion(b)] ?? 9) || a.label.localeCompare(b.label);
  });
}
function folderDepthFrom(root, item) {
  if (!root || !item) return 0;
  let depth = 0;
  for (let cursor = item; cursor && cursor.id !== root.id; cursor = node(cursor.parentId)) depth += 1;
  return depth;
}
/** Always keep 1 level open; never more than 2 levels of open folders. */
function pruneFolderDepth() {
  const root = displayRoot();
  if (!root) return;
  expandedFolders.add(root.id);
  if (syntheticRootFiles.length) expandedFolders.add(SYNTHETIC_ROOT_ID);
  for (const child of topLevelItems(root)) {
    if (child.kind === 'folder') expandedFolders.add(child.id);
  }
  for (const id of [...expandedFolders]) {
    if (id === SYNTHETIC_ROOT_ID) continue;
    const item = node(id);
    if (!item || item.kind !== 'folder') continue;
    if (folderDepthFrom(root, item) > 2) expandedFolders.delete(id);
  }
}
function toggleFolder(id) {
  const item = node(id);
  const root = displayRoot();
  if (!item || item.kind !== 'folder' || !root) return;
  if (item.id === root.id || item.id === SYNTHETIC_ROOT_ID || item.synthetic) return; // stay open
  if (expandedFolders.has(id)) {
    // Keep level-1 always open
    if (folderDepthFrom(root, item) <= 1) return;
    expandedFolders.delete(id);
    for (const child of folderItems(item)) {
      if (child.kind === 'folder') expandedFolders.delete(child.id);
    }
  } else {
    if (folderDepthFrom(root, item) > 2) return;
    expandedFolders.add(id);
    pruneFolderDepth();
  }
}
function ensureDefaultOutlineExpanded() {
  const root = displayRoot();
  if (!root) return;
  expandedFolders.clear();
  expandedFolders.add(root.id);
  for (const child of topLevelItems(root)) {
    if (child.kind === 'folder') expandedFolders.add(child.id);
  }
}
function captureFlip() {
  const map = new Map();
  scene.querySelectorAll('.frame.float[data-drag-id]').forEach(el => {
    map.set(el.dataset.dragId, el.getBoundingClientRect());
  });
  return map;
}
function playFlip(before) {
  if (skipFlipOnce) {
    skipFlipOnce = false;
    return;
  }
  if (!before?.size || document.body.classList.contains('reduce-motion')) return;
  scene.querySelectorAll('.frame.float[data-drag-id]').forEach((el, index) => {
    const id = el.dataset.dragId;
    el.style.setProperty('--float-delay', String((hashHue(id) % 1200)));
    el.style.setProperty('--inertia', String(index % 7));
    const prev = before.get(id);
    if (!prev) {
      el.classList.add('calm-in');
      return;
    }
    const next = el.getBoundingClientRect();
    const dx = prev.left - next.left;
    const dy = prev.top - next.top;
    if (Math.abs(dx) < 1 && Math.abs(dy) < 1) return;
    el.classList.add('flipping');
    el.style.transform = `translate(${dx}px, ${dy}px)`;
    requestAnimationFrame(() => {
      requestAnimationFrame(() => {
        el.style.transform = '';
        const done = () => {
          el.classList.remove('flipping');
          el.removeEventListener('transitionend', done);
        };
        el.addEventListener('transitionend', done);
        setTimeout(done, 2600);
      });
    });
  });
}
function triggerJelly(el, strength = 1) {
  if (!el || document.body.classList.contains('reduce-motion')) return;
  el.classList.remove('jelly-wobble');
  el.style.setProperty('--jelly', String(Math.min(1.4, Math.max(.4, strength))));
  void el.offsetWidth;
  el.classList.add('jelly-wobble');
  clearTimeout(el._jellyTimer);
  el._jellyTimer = setTimeout(() => el.classList.remove('jelly-wobble'), 1400);
}
const ISLAND_GAP = 26; // same breathing room between top-level islands as nested siblings
const MODULE_GAP = 22; // always keep air between fn modules inside a file
const NESTED_GAP = 26; // padding between sibling folders/files inside a parent
function topLevelIslandElements() {
  return [...scene.querySelectorAll('.frame-artboard > .frame.float[data-drag-id]')];
}
/** Top-level folder under pointer — only case where a drag may overlap another island. */
function folderUnderPointer(clientX, clientY, excludeId) {
  for (const el of topLevelIslandElements()) {
    const id = el.dataset.dragId;
    if (id === excludeId) continue;
    if (node(id)?.kind !== 'folder') continue;
    const r = el.getBoundingClientRect();
    if (clientX >= r.left && clientX <= r.right && clientY >= r.top && clientY <= r.bottom) return { id, el };
  }
  return null;
}
/** Visible board frame — gravity parks islands just outside this, never inside. */
function viewFieldBounds() {
  const boardRect = board.getBoundingClientRect();
  return {
    left: boardRect.left,
    top: boardRect.top,
    right: boardRect.right,
    bottom: boardRect.bottom
  };
}
/** Rim just outside the view frame where strays settle. */
function viewFieldRim(margin = 28) {
  const field = viewFieldBounds();
  return {
    left: field.left - margin,
    top: field.top - margin,
    right: field.right + margin,
    bottom: field.bottom + margin
  };
}
/** True when the island is already near the field (inside or just outside) — no pull. */
function islandNearViewField(rect, slack = 40) {
  const field = viewFieldBounds();
  const nearLeft = rect.right >= field.left - slack;
  const nearRight = rect.left <= field.right + slack;
  const nearTop = rect.bottom >= field.top - slack;
  const nearBottom = rect.top <= field.bottom + slack;
  return nearLeft && nearRight && nearTop && nearBottom;
}
/** Pull toward the nearest point on the outside rim — not toward center, not inside the field. */
function pullTowardViewField(rect) {
  const rim = viewFieldRim(28);
  const cx = rect.left + rect.width / 2;
  const cy = rect.top + rect.height / 2;
  let targetX = cx, targetY = cy;
  if (cx < rim.left) targetX = rim.left;
  else if (cx > rim.right) targetX = rim.right;
  if (cy < rim.top) targetY = rim.top;
  else if (cy > rim.bottom) targetY = rim.bottom;
  return { pullX: targetX - cx, pullY: targetY - cy };
}
function rectsOverlap(a, b, gap = ISLAND_GAP) {
  // Collide when rects are closer than `gap` (not when they already overlap by gap).
  const overlapX = Math.min(a.right, b.right) - Math.max(a.left, b.left);
  const overlapY = Math.min(a.bottom, b.bottom) - Math.max(a.top, b.top);
  return overlapX > -gap && overlapY > -gap;
}
function separationPush(moving, fixed, gap = ISLAND_GAP) {
  const overlapX = Math.min(moving.right, fixed.right) - Math.max(moving.left, fixed.left);
  const overlapY = Math.min(moving.bottom, fixed.bottom) - Math.max(moving.top, fixed.bottom);
  // Penetration past the required gap (positive = too close / overlapping).
  const penX = overlapX + gap;
  const penY = overlapY + gap;
  if (penX <= 0 || penY <= 0) return { dx: 0, dy: 0 };
  if (penX <= penY) {
    const dir = moving.left + moving.width / 2 <= fixed.left + fixed.width / 2 ? -penX : penX;
    return { dx: dir, dy: 0 };
  }
  const dir = moving.top + moving.height / 2 <= fixed.top + fixed.height / 2 ? -penY : penY;
  return { dx: 0, dy: dir };
}
function applyIslandTranslate(entry, next) {
  offsets.set(entry.item.id, next);
  entry.el.style.translate = `${next.x}px ${next.y}px`;
  entry.el.style.setProperty('--ox', `${next.x}px`);
  entry.el.style.setProperty('--oy', `${next.y}px`);
  entry.off = next;
  entry.rect = entry.el.getBoundingClientRect();
}
function resolveIslandOverlapDrag(islandId, islandEl, ox, oy, dx, dy, allowOverId) {
  let tx = ox + dx, ty = oy + dy;
  const scale = Math.max(.35, canvas.scale || 1);
  for (let pass = 0; pass < 8; pass++) {
    islandEl.style.translate = `${tx}px ${ty}px`;
    islandEl.style.setProperty('--ox', `${tx}px`);
    islandEl.style.setProperty('--oy', `${ty}px`);
    let myRect = islandEl.getBoundingClientRect();
    let hit = false;
    for (const other of topLevelIslandElements()) {
      const otherId = other.dataset.dragId;
      if (otherId === islandId || otherId === allowOverId) continue;
      const oRect = other.getBoundingClientRect();
      if (!rectsOverlap(myRect, oRect)) continue;
      const { dx: fixX, dy: fixY } = separationPush(myRect, oRect);
      tx += fixX / scale;
      ty += fixY / scale;
      hit = true;
      break;
    }
    if (!hit) break;
  }
  return { x: tx, y: ty };
}
function markDropTarget(clientX, clientY, excludeId) {
  const over = folderUnderPointer(clientX, clientY, excludeId);
  for (const el of topLevelIslandElements()) {
    el.classList.toggle('drop-target', over?.el === el);
  }
  return over?.id || null;
}
function clearDropTargets() {
  topLevelIslandElements().forEach(el => el.classList.remove('drop-target'));
}
function scheduleGravityDrift(delay = 160) {
  // Viewport field gravity runs continuously; luxury-motion only gates jelly/FLIP.
  if (app.classList.contains('dragging')) return;
  clearTimeout(gravityTimer);
  gravityTimer = setTimeout(() => softGravityStep(0), delay);
}
function softGravityStep(pass) {
  if (!graph) return;
  if (app.classList.contains('dragging')) {
    gravityTimer = setTimeout(() => softGravityStep(0), 240);
    return;
  }
  const root = displayRoot();
  if (!root) {
    gravityTimer = setTimeout(() => softGravityStep(0), 400);
    return;
  }
  const top = topLevelItems(root);
  let moved = false;
  const centers = [];
  for (const item of top) {
    const el = scene.querySelector(`.frame.float[data-drag-id="${CSS.escape(item.id)}"]`);
    if (!el) continue;
    const off = offsets.get(item.id) || { x: 0, y: 0 };
    const rect = el.getBoundingClientRect();
    centers.push({ item, el, off, rect });
  }
  const scale = Math.max(.35, canvas.scale || 1);
  for (const A of centers) {
    if (pinnedLayout.has(A.item.id)) continue;
    // Already inside or just outside the view frame — leave context alone.
    if (islandNearViewField(A.rect)) continue;
    const { pullX, pullY } = pullTowardViewField(A.rect);
    if (Math.abs(pullX) < 4 && Math.abs(pullY) < 4) continue;
    const speed = 0.028;
    const stepX = Math.max(-2.0, Math.min(2.0, pullX * speed / scale));
    const stepY = Math.max(-2.0, Math.min(2.0, pullY * speed / scale));
    if (Math.abs(stepX) < 0.04 && Math.abs(stepY) < 0.04) continue;
    applyIslandTranslate(A, { x: A.off.x + stepX, y: A.off.y + stepY });
    moved = true;
  }
  for (let i = 0; i < centers.length; i++) {
    for (let j = i + 1; j < centers.length; j++) {
      const A = centers[i], B = centers[j];
      if (!rectsOverlap(A.rect, B.rect, ISLAND_GAP)) continue;
      const aPinned = pinnedLayout.has(A.item.id);
      const bPinned = pinnedLayout.has(B.item.id);
      if (aPinned && bPinned) continue;
      const { dx, dy } = separationPush(A.rect, B.rect);
      if (!dx && !dy) continue;
      const sx = dx / scale, sy = dy / scale;
      if (!aPinned && !bPinned) {
        applyIslandTranslate(A, { x: A.off.x + sx * 0.5, y: A.off.y + sy * 0.5 });
        applyIslandTranslate(B, { x: B.off.x - sx * 0.5, y: B.off.y - sy * 0.5 });
        moved = true;
      } else if (aPinned && !bPinned) {
        applyIslandTranslate(B, { x: B.off.x - sx, y: B.off.y - sy });
        moved = true;
      } else if (!aPinned && bPinned) {
        applyIslandTranslate(A, { x: A.off.x + sx, y: A.off.y + sy });
        moved = true;
      }
    }
  }
  if (moved) scheduleDraw();
  gravityTimer = setTimeout(() => softGravityStep(0), moved ? 140 : 320);
}
function livesInsideExpandedFolder(file) {
  return !!file && ancestors(file).some(parent => parent.kind === 'folder' && parent.id !== rootFolder().id && expandedFolders.has(parent.id));
}
function focusAnchorElement() {
  return elementForSelection();
}
function lockFocusedAnchor(previousRect) {
  const item = selected(); const file = fileOf(item);
  const anchor = focusAnchorElement();
  if (!previousRect || !anchor || !file || focusedFileId !== file.id || !basePlacements.has(file.id)) return;
  const current = anchor.getBoundingClientRect();
  const dx = (previousRect.left - current.left) / canvas.scale;
  const dy = (previousRect.top - current.top) / canvas.scale;
  if (Math.abs(dx) < .5 && Math.abs(dy) < .5) return;
  // Keep the selected card's *layout* anchored, rather than layering a new
  // visual translate on every render.  The old approach compounded offsets
  // and only worked for top-level cards, which produced locked/jittery renders
  // for files inside folders.
  const placement = basePlacements.get(file.id);
  if (placement) basePlacements.set(file.id, { ...placement, x: placement.x + dx, y: placement.y + dy });
  if (focusOrigin?.id === file.id) focusOrigin = { ...focusOrigin, x: focusOrigin.x + dx, y: focusOrigin.y + dy };
  const remembered = layoutMemory.get(file.id);
  if (remembered) layoutMemory.set(file.id, { ...remembered, x: remembered.x + dx, y: remembered.y + dy });
  const container = scene.querySelector(`.card[data-id="${CSS.escape(file.id)}"], [data-inline-file="${CSS.escape(file.id)}"]`);
  if (container) container.style.translate = `${dx}px ${dy}px`;
}
function activateFocus(item) {
  const file = fileOf(item);
  const target = file || (item?.kind === 'folder' ? item : null);
  if (!target) return;
  expandAncestors(target);
  if (file) {
    focusedFileId = file.id;
    layoutAnchorFileId = file.id;
    flowMode = true;
  }
  basePlacements.clear();
  basePlacementKey = '';
}
function settleDragAnchor() {
  return false;
}
/** Remember where the pointer was on a frame before expand/reflow. */
function captureClickAnchor(id, event) {
  if (!id || !event) return;
  const el = scene.querySelector(`[data-drag-id="${CSS.escape(id)}"],[data-id="${CSS.escape(id)}"]`);
  if (!el) {
    clickAnchor = { id, clientX: event.clientX, clientY: event.clientY, relX: .5, relY: .35 };
    return;
  }
  const rect = el.getBoundingClientRect();
  clickAnchor = {
    id,
    clientX: event.clientX,
    clientY: event.clientY,
    relX: rect.width ? (event.clientX - rect.left) / rect.width : .5,
    relY: rect.height ? (event.clientY - rect.top) / rect.height : .35
  };
}
/** After layout, slide the island so the click point stays under the pointer. */
function stabilizeClickAnchor() {
  const anchor = clickAnchor;
  clickAnchor = null;
  if (!anchor) return;
  const el = scene.querySelector(`[data-drag-id="${CSS.escape(anchor.id)}"],[data-id="${CSS.escape(anchor.id)}"]`);
  if (!el) return;
  const rect = el.getBoundingClientRect();
  const targetX = rect.left + rect.width * (anchor.relX ?? .5);
  const targetY = rect.top + rect.height * (anchor.relY ?? .35);
  const dx = (anchor.clientX - targetX) / canvas.scale;
  const dy = (anchor.clientY - targetY) / canvas.scale;
  if (Math.abs(dx) < .4 && Math.abs(dy) < .4) return;
  const islandId = dragIslandId(anchor.id);
  const cur = offsets.get(islandId) || { x: 0, y: 0 };
  const next = { x: cur.x + dx, y: cur.y + dy };
  offsets.set(islandId, next);
  const islandEl = scene.querySelector(`[data-drag-id="${CSS.escape(islandId)}"]`) || el;
  islandEl.style.translate = `${next.x}px ${next.y}px`;
  islandEl.style.setProperty('--ox', `${next.x}px`);
  islandEl.style.setProperty('--oy', `${next.y}px`);
  scheduleDraw();
}
/** Top-level island that owns a nested frame (folder group drag). */
function dragIslandId(id) {
  const item = node(id);
  if (!item) return id;
  const top = topLevelOwner(item);
  return top?.id || id;
}
function parentCanvasId(id) {
  const item = node(id);
  if (!item) return null;
  if (item.kind === 'module') return item.fileId;
  const root = displayRootRaw();
  if (item.kind === 'file' && item.parentId === root?.id) return SYNTHETIC_ROOT_ID;
  if (item.parentId && item.parentId !== root?.id && item.parentId !== rootFolder()?.id) return item.parentId;
  return null;
}
/** Size frame chrome from label length so titles wrap instead of clipping. */
function frameLabelMetrics(label = '', { minW = 220, maxW = 420, chrome = 84, charW = 7.2, baseH = 54, lineH = 17, maxLines = 3 } = {}) {
  const text = String(label || '');
  const w = Math.min(maxW, Math.max(minW, Math.round(text.length * charW * 0.62) + chrome));
  const charsPerLine = Math.max(14, Math.floor((w - chrome) / charW));
  const lines = Math.min(maxLines, Math.max(1, Math.ceil(text.length / charsPerLine) || 1));
  return { w, h: baseH + (lines - 1) * lineH, lines };
}
function frameModuleSize(_file, module) {
  const label = module?.label ? `${module.label}()` : 'fn';
  const { w, h } = frameLabelMetrics(label, { minW: 172, maxW: 320, chrome: 56, baseH: 50, lineH: 16, maxLines: 2 });
  return { w, h: Math.max(50, h) };
}
function frameFileSize(file) {
  const header = frameLabelMetrics(file.label, { minW: 228, maxW: 440, chrome: 96, baseH: 54, lineH: 17, maxLines: 3 });
  if (!expandedFiles.has(file.id)) return { w: header.w, h: header.h, headerH: header.h, children: [] };
  const boxes = modules(file).slice(0, 18).map(module => {
    const size = frameModuleSize(file, module);
    return { id: module.id, item: module, w: size.w, h: size.h, size };
  });
  const packed = packBoxes(boxes, { gap: MODULE_GAP, pad: 18, maxWidth: Math.max(720, header.w - 24), mode: layoutModes.get(file.id) || 'auto' });
  return { w: Math.max(header.w, packed.w + 12), h: Math.max(header.h, 48) + packed.h + 12, headerH: header.h, children: packed.items };
}
function frameFolderSize(item, depth = 0) {
  const header = frameLabelMetrics(item.label, { minW: depth ? 208 : 232, maxW: 460, chrome: 108, baseH: 54, lineH: 17, maxLines: 3 });
  if ((!expandedFolders.has(item.id) && item.id !== SYNTHETIC_ROOT_ID) || depth > 8) {
    return { w: header.w, h: header.h, headerH: header.h, children: [] };
  }
  const boxes = folderItems(item).slice(0, depth > 3 ? 20 : 36).map(child => {
    const size = child.kind === 'folder' ? frameFolderSize(child, depth + 1) : frameFileSize(child);
    return { id: child.id, item: child, w: size.w, h: size.h, children: size.children, size };
  });
  const packed = packBoxes(boxes, {
    gap: NESTED_GAP,
    pad: 20,
    maxWidth: depth === 0 ? 1020 : 780,
    mode: layoutModes.get(item.id) || 'auto'
  });
  return { w: Math.max(header.w, packed.w + 12), h: Math.max(header.h, 48) + packed.h + 16, headerH: header.h, children: packed.items };
}
/** Shelf-pack floating boxes left→right, wrap on maxWidth, then separate overlaps. */
function packBoxes(boxes, { gap = 14, pad = 12, maxWidth = 900, mode = 'auto' } = {}) {
  let x = pad, y = pad, rowH = 0;
  const items = [];
  const ordered = [...boxes].sort((a, b) => {
    const ia = a.item || node(a.id);
    const ib = b.item || node(b.id);
    return (mapRegionPriority[mapRegion(ia)] ?? 9) - (mapRegionPriority[mapRegion(ib)] ?? 9)
      || primaryTraceScore(ib) - primaryTraceScore(ia)
      || (ia?.label || '').localeCompare(ib?.label || '');
  });
  const useRow = mode === 'row';
  const useCol = mode === 'column';
  for (const box of ordered) {
    if (!useCol && !useRow && x > pad && x + box.w > maxWidth - pad) {
      x = pad;
      y += rowH + gap;
      rowH = 0;
    }
    if (useCol && items.length) {
      x = pad;
      y += rowH + gap;
      rowH = 0;
    }
    const local = localOffsets.get(box.id) || { x: 0, y: 0 };
    items.push({ ...box, x: x + local.x, y: y + local.y });
    if (useRow || !useCol) {
      x += box.w + gap;
      rowH = Math.max(rowH, box.h);
    } else {
      rowH = box.h;
    }
  }
  separateBoxes(items, { gap, passes: 36 });
  let boundX = pad, boundY = pad;
  for (const item of items) {
    boundX = Math.max(boundX, item.x + item.w);
    boundY = Math.max(boundY, item.y + item.h);
  }
  return { items, w: Math.max(boundX + pad, pad * 2 + 120), h: Math.max(boundY + pad, pad * 2 + 48) };
}
/** Push overlapping boxes apart until they clear `gap`. */
function separateBoxes(items, { gap = 12, passes = 28 } = {}) {
  if (items.length < 2) return;
  for (let pass = 0; pass < passes; pass++) {
    let hit = false;
    for (let i = 0; i < items.length; i++) {
      for (let j = i + 1; j < items.length; j++) {
        const A = items[i], B = items[j];
        const ox = Math.min(A.x + A.w, B.x + B.w) - Math.max(A.x, B.x);
        const oy = Math.min(A.y + A.h, B.y + B.h) - Math.max(A.y, B.y);
        if (ox <= gap || oy <= gap) continue;
        hit = true;
        if (ox < oy) {
          const push = (ox - gap) / 2 + .5;
          if (A.x <= B.x) { A.x -= push; B.x += push; } else { A.x += push; B.x -= push; }
        } else {
          const push = (oy - gap) / 2 + .5;
          if (A.y <= B.y) { A.y -= push; B.y += push; } else { A.y += push; B.y -= push; }
        }
      }
    }
    if (!hit) break;
  }
  let minX = Infinity, minY = Infinity;
  for (const item of items) {
    minX = Math.min(minX, item.x);
    minY = Math.min(minY, item.y);
  }
  if (Number.isFinite(minX) && (minX < gap || minY < gap)) {
    const dx = Math.max(0, gap - minX);
    const dy = Math.max(0, gap - minY);
    for (const item of items) { item.x += dx; item.y += dy; }
  }
}
function buildFloatLayout(root) {
  floatPlacements.clear();
  const view = root || displayRoot();
  if (!view) return { w: 800, h: 480, items: [] };
  const top = topLevelItems(view).map(child => {
    const size = child.kind === 'folder' || child.synthetic ? frameFolderSize(child, 0) : frameFileSize(child);
    return { id: child.id, item: child, w: size.w, h: size.h, size };
  });
  const packed = packBoxes(top, { gap: ISLAND_GAP + 16, pad: 40, maxWidth: Math.max(960, board.clientWidth - 60) });
  relaxTopLevel(packed.items, ISLAND_GAP);
  let maxX = 0, maxY = 0;
  for (const entry of packed.items) {
    maxX = Math.max(maxX, entry.x + entry.w);
    maxY = Math.max(maxY, entry.y + entry.h);
  }
  packed.w = Math.max(packed.w, maxX + 36);
  packed.h = Math.max(packed.h, maxY + 36);
  return packed;
}
function relaxTopLevel(items, pad) {
  if (items.length < 2) return;
  const byId = new Map(items.map(item => [item.id, item]));
  const focusSeeds = new Set(sourceSeeds(selected()));
  const passes = traceActive() ? 32 : 22;
  for (let pass = 0; pass < passes; pass++) {
    for (const edge of edgeTypes()) {
      if (!WALK_TYPES.has(edge.type) && edge.type !== 'imports') continue;
      const aFile = fileOf(node(edge.from));
      const bFile = fileOf(node(edge.to));
      if (!aFile || !bFile) continue;
      const aTop = topLevelOwner(aFile);
      const bTop = topLevelOwner(bFile);
      if (!aTop || !bTop || aTop.id === bTop.id) continue;
      if (pinnedLayout.has(aTop.id) && pinnedLayout.has(bTop.id)) continue;
      const A = byId.get(aTop.id), B = byId.get(bTop.id);
      if (!A || !B) continue;
      const related = focusSeeds.has(edge.from) || focusSeeds.has(edge.to) || hasTrace(aTop) || hasTrace(bTop);
      const ax = A.x + A.w / 2, ay = A.y + A.h / 2;
      const bx = B.x + B.w / 2, by = B.y + B.h / 2;
      const dx = bx - ax, dy = by - ay;
      const dist = Math.hypot(dx, dy) || 1;
      const desired = related && traceActive()
        ? 150 + (A.w + B.w) * .14
        : 210 + (A.w + B.w) * .2;
      const pull = Math.min(related ? 14 : 10, (dist - desired) * (related ? .11 : .08));
      const ux = dx / dist, uy = dy / dist;
      const level = related && traceActive() ? (ay - by) * .04 : 0;
      if (!pinnedLayout.has(aTop.id)) { A.x += ux * pull * .5; A.y += uy * pull * .5 - level; }
      if (!pinnedLayout.has(bTop.id)) { B.x -= ux * pull * .5; B.y -= uy * pull * .5 + level; }
    }
    separateBoxes(items, { gap: ISLAND_GAP, passes: 12 });
  }
  let minX = Infinity, minY = Infinity;
  for (const item of items) { minX = Math.min(minX, item.x); minY = Math.min(minY, item.y); }
  for (const item of items) { item.x += pad - minX; item.y += pad - minY; }
}
function topLevelOwner(item) {
  const root = displayRoot();
  if (!item || !root) return null;
  // Loose files belong to the synthetic root island.
  if (item.kind === 'file' && item.parentId === root.id) return node(SYNTHETIC_ROOT_ID);
  if (item.id === SYNTHETIC_ROOT_ID) return item;
  let cursor = item;
  while (cursor && cursor.parentId && cursor.parentId !== root.id) {
    if (cursor.parentId === SYNTHETIC_ROOT_ID) return node(SYNTHETIC_ROOT_ID);
    cursor = node(cursor.parentId);
  }
  return cursor?.parentId === root.id ? cursor : null;
}
function automaticLayout() {
  const root = displayRoot() || rootFolder();
  const packed = buildFloatLayout(root);
  const viewportWidth = Math.max(980, board.clientWidth);
  const viewportHeight = Math.max(680, board.clientHeight);
  const contentWidth = Math.max(packed.w + 40, viewportWidth - 48);
  const contentHeight = Math.max(packed.h + 40, 420);
  const worldW = Math.max(viewportWidth, contentWidth + 80);
  const worldH = Math.max(viewportHeight, contentHeight + 120);
  basePlacements.clear();
  basePlacementKey = `float:${root?.id}:${expandedFolders.size}:${expandedFiles.size}:${expandedModules.size}`;
  return {
    placements: packed.items,
    chrome: [{ kind: 'stage', mode: 'frames', title: root?.label || 'repository', path: root?.path || '/', w: worldW, h: worldH }],
    root,
    mode: 'frames',
    w: worldW,
    h: worldH,
    contentWidth,
    contentHeight: Math.max(contentHeight, packed.h + 48),
    packed
  };
}

function sourceNotes(file) {
  const notes = new Map(); const local = new Set(modules(file).map(module => module.id));
  const add = (line, side, edge) => { if (!line) return; const list = notes.get(line) || []; if (!list.some(note => note.edge.id === edge.id && note.side === side)) list.push({ side, edge }); notes.set(line, list); };
  for (const edge of edgeTypes()) {
    if (traceActive() && !traceEdges.has(edge.id)) continue;
    if (sameModuleOrInternalContainer(edge)) continue;
    if (local.has(edge.from) || edge.from === file.id) add(edge.line, 'out', edge);
    if (local.has(edge.to)) add(node(edge.to)?.loc?.start, 'in', edge);
  }
  return notes;
}
function importSummaries(file) {
  return edgeTypes().filter(edge => CONTEXT_TYPES.has(edge.type) && (edge.from === file.id || edge.to === file.id)).slice(0, 8);
}
function importPortId(edge, side) {
  return `import:${edge.id}:${side === 'from' ? 'out' : 'in'}`;
}
function importRowHtml(edge) {
  return `<button class="inline-import ${selectedImportEdgeId === edge.id ? 'selected' : ''} ${traceActive() && !traceEdges.has(edge.id) ? 'dim' : ''}" data-inline-import="${edge.id}" title="${escape(edge.evidence)}">
    <span class="port edge-port in import-edge-port" data-import-port="${importPortId(edge, 'to')}" data-port-for="${importPortId(edge, 'to')}" data-port-side="in"></span>
    <span class="import-kind">import</span><b>${escape(edge.evidence)}</b>
    <span class="port edge-port out import-edge-port" data-import-port="${importPortId(edge, 'from')}" data-port-for="${importPortId(edge, 'from')}" data-port-side="out"></span>
  </button>`;
}
function sourceHtml(file) {
  const notes = sourceNotes(file); const source = file.meta?.source || '';
  const selectedModule = selected()?.kind === 'module' ? selected() : null;
  const selectedImport = edgeTypes().find(edge => edge.id === selectedImportEdgeId);
  const lines = source.split('\n').map((text, index) => { const line = index + 1; const entries = notes.get(line) || []; const klass = entries[0] ? `hit-${entries[0].side}` : ''; const active = selectedModule && line >= selectedModule.loc.start && line <= selectedModule.loc.end ? ' active-module' : ''; const activeImport = selectedImport?.line === line && selectedImport.from === file.id ? ' active-import' : ''; const dim = (selectedModule || selectedImport) && !active && !activeImport && !entries.length ? ' dim' : ''; const badges = entries.map(note => `<button class="line-badge ${note.side}" data-pin="${note.side === 'out' ? note.edge.from : note.edge.to}" data-source-port="source:${note.edge.id}:${note.side}" title="${escape(note.edge.evidence)}">${note.side === 'in' ? 'IN' : 'OUT'} · ${escape(note.edge.type)}<i></i></button>`).join(''); return `<span class="line ${klass}${active}${activeImport}${dim}" data-line="${line}" data-file="${file.id}"><i>${line}</i><code>${escape(text) || ' '}</code><span class="line-badges">${badges}</span></span>`; }).join('');
  return `<section class="source"><header><b>${escape(file.label)}</b><span>full source</span></header><pre>${lines}</pre></section>`;
}
function moduleSourceHtml(file, module) {
  const notes = sourceNotes(file);
  const source = (file.meta?.source || '').split('\n');
  const start = Math.max(1, module.loc.start);
  const end = Math.min(source.length, module.loc.end || module.loc.start);
  const lines = source.slice(start - 1, end).map((text, index) => {
    const line = start + index;
    const entries = (notes.get(line) || []).filter(note => note.edge.from === module.id || note.edge.to === module.id || note.edge.from === file.id);
    const klass = entries[0] ? `hit-${entries[0].side}` : '';
    const badges = entries.map(note => `<button class="line-badge ${note.side}" data-pin="${note.side === 'out' ? note.edge.from : note.edge.to}" data-source-port="source:${note.edge.id}:${note.side}" title="${escape(note.edge.evidence)}">${note.side === 'in' ? 'IN' : 'OUT'} · ${escape(note.edge.type)}<i></i></button>`).join('');
    return `<span class="line ${klass} active-module" data-line="${line}" data-file="${file.id}"><i>${line}</i><code>${escape(text) || ' '}</code><span class="line-badges">${badges}</span></span>`;
  }).join('');
  return `<section class="source module-source" data-module-source="${module.id}"><header><b>${escape(module.label)}()</b><span>source lines ${start}–${end}</span></header><pre>${lines || '<span class="line"><i>—</i><code>No source range found.</code><span></span></span>'}</pre></section>`;
}
function formatDiffHtml(file, limit = 120) {
  const diff = file?.git?.diff;
  if (!diff) return '<span class="diff-line meta">New or untracked file — full source is in the canvas.</span>';
  return diff.split('\n').slice(0, limit).map(line => {
    let cls = 'diff-line';
    if (line.startsWith('+++') || line.startsWith('---')) cls += ' meta';
    else if (line.startsWith('@@')) cls += ' hunk';
    else if (line.startsWith('+')) cls += ' add';
    else if (line.startsWith('-')) cls += ' remove';
    return `<span class="${cls}">${escape(line) || ' '}</span>`;
  }).join('');
}
function diffHtml(file) {
  const diff = file.git?.diff; if (!file.git?.change && !recentFor(file)) return '';
  if (!diff) return `<section class="diff"><header><b>LOCAL CHANGE</b></header><pre>New or untracked file. Source is available above.</pre></section>`;
  return `<section class="diff"><header><b>LOCAL DIFF</b></header><pre>${formatDiffHtml(file, 90)}</pre></section>`;
}
function diffPreviewHtml(file) {
  return '';
}
function framePorts(id) {
  return `<span class="port edge-port in endpoint-port ${pinned.has(id) ? 'pinned' : ''}" data-pin="${id}" data-port-for="${id}" data-port-side="in" title="Trace in"></span><span class="port edge-port out endpoint-port ${pinned.has(id) ? 'pinned' : ''}" data-pin="${id}" data-port-for="${id}" data-port-side="out" title="Trace out"></span>`;
}
function frameStyle(placement, tint, id, { depth = 0, inertia = 0 } = {}) {
  // Only top-level islands carry world offsets; nested frames stay inside the parent canvas.
  const island = dragIslandId(id);
  const off = island === id ? (offsets.get(id) || { x: 0, y: 0 }) : { x: 0, y: 0 };
  const glass = Math.min(78, 16 + depth * 14);
  const delay = hashHue(id) % 900;
  return `left:${placement.x}px;top:${placement.y}px;width:${placement.w}px;translate:${off.x}px ${off.y}px;--ox:${off.x}px;--oy:${off.y}px;--node:${tint};--accent:${tint};--depth:${depth};--glass:${glass}%;--float-delay:${delay};--inertia:${inertia}`;
}
function frameModuleHtml(file, module, placement, depth = 0, inertia = 0) {
  const hot = hoverId === module.id ? 'hot' : '';
  const tint = fileTint(file);
  return `<section class="frame frame-fn float ${selectedId === module.id ? 'selected' : ''} ${hot}" data-module-box="${module.id}" data-hover="${module.id}" data-drag-id="${module.id}" data-open-flow="${module.id}" style="${frameStyle(placement, tint, module.id, { depth: depth + 1, inertia })}">
    <header class="frame-bar" data-outline-row="${module.id}" data-hover="${module.id}">
      ${framePorts(module.id)}
      <button class="frame-title" data-module="${module.id}" data-open-flow="${module.id}" type="button">
        <em class="fn-kind">${module.moduleKind === 'class' ? 'class' : 'fn'}</em>
        <b>${escape(module.label)}()</b>
      </button>
      <button class="port pin-btn ${pinned.has(module.id) ? 'pinned' : ''}" data-pin="${module.id}" type="button" title="Pin"></button>
    </header>
  </section>`;
}
function frameFileHtml(file, placement, size = frameFileSize(file), depth = 0) {
  const expanded = expandedFiles.has(file.id);
  const hot = hoverId === file.id ? 'hot' : '';
  const tint = fileTint(file);
  const glyph = fileGlyph(file);
  const kids = expanded
    ? (size.children || []).map((child, index) => {
      const module = child.item || node(child.id);
      return module ? frameModuleHtml(file, module, child, depth, index % 6) : '';
    }).join('')
    : '';
  return `<section class="frame frame-file float ${expanded ? 'expanded' : ''} ${selectedId === file.id || fileOf(selected())?.id === file.id ? 'selected' : ''} ${recentFor(file) ? 'live-changed' : ''} ${file.orphan ? 'orphan' : ''} ${file.entrypoint ? 'entrypoint' : ''} ${hot}" data-id="${file.id}" data-inline="${file.id}" data-inline-file="${file.id}" data-kind="file" data-hover="${file.id}" data-drag-id="${file.id}" data-depth="${depth}" style="${frameStyle(placement, tint, file.id, { depth })}">
    <header class="frame-bar" data-outline-row="${file.id}" data-hover="${file.id}">
      ${framePorts(file.id)}
      <button class="frame-toggle" data-expand="${file.id}" type="button">${expanded ? '⌄' : '›'}</button>
      <button class="frame-title outline-label" data-inline="${file.id}" data-kind="file" data-focus-file="${file.id}" type="button">
        <span class="file-glyph" style="--glyph:${glyph.c}" title="${escape(file.extension || '')}">${escape(glyph.g)}</span>
        <b title="${escape(file.path)}">${escape(file.label)}</b>
        <span>${modules(file).length || '—'}</span>
      </button>
      <button class="port pin-btn ${pinned.has(file.id) ? 'pinned' : ''}" data-pin="${file.id}" type="button" title="Pin"></button>
    </header>
    ${expanded ? `<div class="frame-canvas float-canvas" style="height:${Math.max(64, placement.h - (size.headerH || 54) - 10)}px">${kids || '<p class="frame-empty">Empty</p>'}</div>` : ''}
  </section>`;
}
function frameFolderHtml(item, placement, size = frameFolderSize(item, 0), depth = 0) {
  const expanded = item.id === SYNTHETIC_ROOT_ID || item.synthetic || expandedFolders.has(item.id);
  const files = item.id === SYNTHETIC_ROOT_ID ? syntheticRootFiles.length : filesBelow(item).length;
  const region = item.synthetic ? 'context' : mapRegion(item);
  const copy = item.synthetic ? { title: 'root' } : railCopy(region);
  const hot = hoverId === item.id ? 'hot' : '';
  const tint = folderTint(item);
  const kids = expanded
    ? (size.children || []).map(child => {
      const childItem = child.item || node(child.id);
      if (!childItem) return '';
      const childSize = child.size || (childItem.kind === 'folder' ? frameFolderSize(childItem, depth + 1) : frameFileSize(childItem));
      return childItem.kind === 'folder'
        ? frameFolderHtml(childItem, child, childSize, depth + 1)
        : frameFileHtml(childItem, child, childSize, depth + 1);
    }).join('')
    : '';
  return `<section class="frame frame-folder float ${expanded ? 'expanded' : ''} ${item.synthetic ? 'synthetic-root' : ''} ${selectedId === item.id ? 'selected' : ''} ${hot}" data-id="${item.id}" data-inline="${item.id}" data-kind="folder" data-region="${region}" data-depth="${depth}" data-hover="${item.id}" data-drag-id="${item.id}" style="${frameStyle(placement, tint, item.id, { depth })}">
    <header class="frame-bar" data-outline-row="${item.id}" data-hover="${item.id}">
      ${framePorts(item.id)}
      <button class="frame-toggle" data-folder-expand="${item.id}" type="button" ${item.synthetic ? 'disabled' : ''}>${expanded ? '⌄' : '›'}</button>
      <button class="frame-title outline-label" data-inline="${item.id}" data-kind="folder" type="button">
        <em class="frame-kind">${escape(copy.title)}</em>
        <b>${escape(item.label)}</b>
        <span>${files}</span>
      </button>
      <button class="port pin-btn ${pinned.has(item.id) ? 'pinned' : ''}" data-pin="${item.id}" type="button" title="Pin"></button>
    </header>
    ${expanded ? `<div class="frame-canvas float-canvas" style="height:${Math.max(72, placement.h - (size.headerH || 54) - 10)}px">${kids || '<p class="frame-empty">Empty</p>'}</div>` : ''}
  </section>`;
}
function frameTreeHtml(root, packed) {
  if (!root) return '<p class="frame-empty">No workspace loaded.</p>';
  const items = packed?.items || buildFloatLayout(root).items;
  const kids = items.map(entry => {
    const item = entry.item || node(entry.id);
    if (!item) return '';
    const size = entry.size || (item.kind === 'folder' ? frameFolderSize(item, 0) : frameFileSize(item));
    return item.kind === 'folder' ? frameFolderHtml(item, entry, size, 0) : frameFileHtml(item, entry, size, 0);
  }).join('');
  const w = packed?.w || 800, h = packed?.h || 480;
  return `<div class="frame-artboard" data-id="${root.id}" data-kind="folder" style="width:${w}px;height:${h}px">${kids}</div>`;
}
function changeLines(file, limit = 6) {
  const lines = (file.git?.diff || '').split('\n').filter(line => /^[+-]/.test(line) && !/^(\+\+\+|---)/.test(line)).slice(0, limit);
  return lines.length ? lines : ['Workspace change detected.'];
}
function changedFiles(limit = 4) {
  const now = Date.now();
  return [...recentPaths.entries()]
    .filter(([path, at]) => !reviewedPaths.has(path) && now - at < 60_000)
    .map(([path, at]) => ({ file: graph.nodes.find(item => item.kind === 'file' && item.path === path), at }))
    .filter(entry => entry.file)
    .sort((a, b) => b.at - a.at)
    .slice(0, limit)
    .map(entry => entry.file);
}
function fileForPath(path) {
  return graph?.nodes.find(item => item.kind === 'file' && item.path === path);
}
function modulesTouched(file) {
  if (!file) return [];
  const changed = changeLines(file, 20);
  const source = file.meta?.source?.split('\n') || [];
  return modules(file)
    .filter(module => changed.some(line => source.slice(module.loc.start - 1, module.loc.end).some(sourceLine => line.includes(sourceLine.trim().slice(0, 24)) && sourceLine.trim().length > 4)))
    .slice(0, 2);
}
function upsertActivity(path) {
  const normalized = String(path || '').replaceAll('\\', '/');
  if (!normalized || reviewedPaths.has(normalized)) return;
  const now = Date.now();
  const current = activityItems.get(normalized);
  activityItems.set(normalized, { path: normalized, createdAt: current?.createdAt || now, updatedAt: now, status: 'active' });
}
function archiveActivity(path) {
  const item = activityItems.get(path);
  if (!item) return;
  activityItems.delete(path);
  archivedActivity.unshift({ ...item, archivedAt: Date.now() });
  archivedActivity.splice(8);
  renderActivityFeed();
  scheduleActivityFade();
}
function scheduleActivityFade() {
  clearTimeout(activityTimer);
  const now = Date.now();
  const fading = [...activityItems.values()].find(item => item.status === 'fading');
  if (fading) {
    activityTimer = setTimeout(() => archiveActivity(fading.path), 900);
    return;
  }
  const oldest = [...activityItems.values()].sort((a, b) => a.createdAt - b.createdAt)[0];
  if (!oldest) return;
  const wait = Math.max(0, 5200 - (now - oldest.updatedAt));
  activityTimer = setTimeout(() => {
    const item = activityItems.get(oldest.path);
    if (!item || item.status === 'fading') return;
    item.status = 'fading';
    renderActivityFeed();
    scheduleActivityFade();
  }, wait);
}
function renderActivityFeed() {
  if (activityFrame) return;
  activityFrame = requestAnimationFrame(() => {
    activityFrame = 0;
    const list = $('#activity-list');
    if (!list) return;
    const active = [...activityItems.values()].sort((a, b) => a.createdAt - b.createdAt);
    const archived = archivedActivity.filter(item => !activityItems.has(item.path));
    const activeHtml = active.map((item, index) => {
      const file = fileForPath(item.path);
      const touched = modulesTouched(file);
      const lines = file ? changeLines(file, 3) : ['Workspace change detected.'];
      return `<article class="activity-toast ${item.status === 'fading' ? 'fading' : ''} ${index > 0 ? 'queued' : ''}" data-activity="${escape(item.path)}">
        <header><b>${index ? 'Queued edit' : 'Codex edited'}</b><span>${escape(file?.git?.change || 'live')}</span></header>
        <strong>${escape(file?.label || item.path.split('/').pop())}</strong>
        <small>${escape(item.path)}</small>
        ${touched.length ? `<p>Affects ${touched.map(module => `${escape(module.label)}()`).join(', ')}</p>` : '<p>Trace and source updated in the map.</p>'}
        <pre>${lines.map(line => `<span class="${line.startsWith('+') ? 'add' : line.startsWith('-') ? 'remove' : ''}">${escape(line)}</span>`).join('')}</pre>
        <footer><button data-open-change="${escape(item.path)}">Open source</button><button data-review-change="${escape(item.path)}">Reviewed</button></footer>
      </article>`;
    }).join('');
    const historyHtml = archived.slice(0, 5).map(item => {
      const file = fileForPath(item.path);
      return `<button class="activity-history" data-open-change="${escape(item.path)}"><span>Reviewed</span><b>${escape(file?.label || item.path.split('/').pop())}</b></button>`;
    }).join('');
    list.innerHTML = activeHtml || historyHtml ? `${activeHtml}${historyHtml ? `<div class="activity-history-list">${historyHtml}</div>` : ''}` : '<p class="activity-empty">Agent edits will appear here without moving the canvas.</p>';
    bindActivityFeed();
  });
}
function chromeHtml(layout) {
  return (layout.chrome || []).map(piece => {
    if (piece.kind !== 'stage') return '';
    const stats = graph?.stats || {};
    return `<div class="stage-banner frames minimal" data-stage="frames">
      <div class="stage-banner-copy">
        <span class="stage-kicker">Hover to trace · click to pin focus</span>
        <h2>${escape(piece.title)}</h2>
      </div>
      <p class="stage-hint">${stats.files || 0} files · ${stats.modules || 0} fn</p>
    </div>`;
  }).join('');
}
function render() {
  if (!graph) return;
  // Nested frames must not keep independent world offsets — they live inside folders.
  for (const id of [...offsets.keys()]) {
    if (dragIslandId(id) !== id) offsets.delete(id);
  }
  const before = captureFlip();
  rememberLayoutPositions();
  const layout = automaticLayout();
  world.style.width = `${layout.w}px`;
  world.style.height = `${layout.h}px`;
  world.dataset.layoutMode = 'frames';
  world.classList.toggle('previewing', traceMode && !!hoverId && hoverId !== selectedId);
  scene.innerHTML = `${chromeHtml(layout)}<div class="frame-stage" style="width:${layout.contentWidth || layout.w - 80}px;height:${layout.contentHeight || layout.h - 100}px">${frameTreeHtml(layout.root, layout.packed)}</div>`;
  bindScene();
  bindHoverTrace();
  applyCanvas();
  refreshFocusClasses();
  drawEdges();
  playFlip(before);
  animateReflowEdges(920);
  scheduleGravityDrift();
  renderMinimap();
  renderActivityFeed();
}

function folderOwnsEndpoint(folder) {
  return !expandedFolders.has(folder.id);
}
function fileOwnsEndpoint(file) {
  return !expandedFiles.has(file.id);
}
function endpointFor(edge, side) {
  const id = side === 'from' ? edge.from : edge.to;
  const item = node(id);
  const file = fileOf(item);
  const sourcePort = `source:${edge.id}:${side === 'from' ? 'out' : 'in'}`;
  if (scene.querySelector(`[data-source-port="${CSS.escape(sourcePort)}"]`)) return sourcePort;
  const importPort = importPortId(edge, side);
  if (CONTEXT_TYPES.has(edge.type) && scene.querySelector(`[data-import-port="${CSS.escape(importPort)}"]`)) return importPort;
  if (item?.kind === 'module' && scene.querySelector(`[data-inline-module="${CSS.escape(item.id)}"],[data-module="${CSS.escape(item.id)}"]`)) {
    return `inline-module:${item.id}`;
  }
  if (file && scene.querySelector(`[data-inline-file="${CSS.escape(file.id)}"],[data-id="${CSS.escape(file.id)}"]`)) {
    if (fileOwnsEndpoint(file) || item?.kind === 'file') return file.id;
    // File is expanded: still allow file port when the module row is missing.
    if (item?.kind === 'module') {
      let visible = nearestVisibleFolder(file);
      while (visible && !folderOwnsEndpoint(visible)) visible = nearestVisibleFolder(node(visible.parentId));
      return visible?.id || file.id;
    }
    return file.id;
  }
  let visible = nearestVisibleFolder(file || item);
  while (visible && !folderOwnsEndpoint(visible)) visible = nearestVisibleFolder(node(visible.parentId));
  return visible?.id || null;
}
function isDetailedEndpoint(id) {
  return id?.startsWith('inline-module:') || id?.startsWith('module:') || id?.startsWith('source:');
}
function sameModuleOrInternalContainer(edge) {
  if (edge.from === edge.to) return true;
  const from = node(edge.from), to = node(edge.to);
  const fromFile = fileOf(from), toFile = fileOf(to);
  if (fromFile && toFile && fromFile.id === toFile.id) {
    const visibleModules = expandedFiles.has(fromFile.id) || !!scene.querySelector(`[data-inline-module="${CSS.escape(from?.id || '')}"],[data-module="${CSS.escape(from?.id || '')}"]`);
    if (from?.kind === 'module' && to?.kind === 'module' && from.id !== to.id && visibleModules) return false;
    return true;
  }
  return false;
}
function markEndpoint(id, side) {
  const selector = id.startsWith('source:') ? `[data-source-port="${CSS.escape(id)}"]` : id.startsWith('import:') ? `[data-import-port="${CSS.escape(id)}"]` : id.startsWith('inline-module:') ? `[data-inline-module="${CSS.escape(id.slice(14))}"]` : id.startsWith('module:') ? `[data-module="${CSS.escape(id.slice(7))}"]` : id.startsWith('inline:') ? `[data-inline-file="${CSS.escape(id.slice(7))}"]` : `[data-id="${CSS.escape(id)}"]`;
  const element = scene.querySelector(selector); if (!element) return;
  if (element.matches('[data-source-port],[data-import-port]')) { element.classList.add('connected-port'); return; }
  const moduleId = id.startsWith('inline-module:') ? id.slice(14) : id.startsWith('module:') ? id.slice(7) : null;
  const portId = moduleId || (id.startsWith('inline:') ? id.slice(7) : id);
  const port = element.matches(`[data-source-port="${CSS.escape(id)}"]`) ? element : element.querySelector(`[data-port-for="${CSS.escape(portId)}"][data-port-side="${side}"]`);
  port?.classList.add('connected-port');
}
function crossingOffsets(edges) {
  const offsets = new Map();
  const groups = new Map();
  for (const edge of edges) {
    const key = edge.b.x >= edge.a.x ? 'forward' : 'backward';
    const list = groups.get(key) || []; list.push(edge); groups.set(key, list);
  }
  for (const list of groups.values()) {
    const ordered = [...list].sort((a, b) => a.a.y - b.a.y || a.b.y - b.b.y);
    for (let i = 0; i < ordered.length; i++) {
      let inversions = 0, near = 0;
      for (let j = 0; j < ordered.length; j++) {
        if (i === j) continue;
        const overlapX = !(Math.max(ordered[i].a.x, ordered[i].b.x) < Math.min(ordered[j].a.x, ordered[j].b.x) || Math.max(ordered[j].a.x, ordered[j].b.x) < Math.min(ordered[i].a.x, ordered[i].b.x));
        if (!overlapX) continue;
        const beforeAtSource = ordered[i].a.y < ordered[j].a.y;
        const beforeAtTarget = ordered[i].b.y < ordered[j].b.y;
        if (beforeAtSource !== beforeAtTarget) inversions += beforeAtSource ? -1 : 1;
        if (Math.abs(ordered[i].a.y - ordered[j].a.y) < 38 || Math.abs(ordered[i].b.y - ordered[j].b.y) < 38) near += beforeAtSource ? -1 : 1;
      }
      offsets.set(ordered[i].edge.id, Math.max(-42, Math.min(42, inversions * 8 + near * 3)));
    }
  }
  return offsets;
}
function usesModulePort(id) {
  return id?.startsWith('inline-module:') || id?.startsWith('module:') || id?.startsWith('source:');
}
function showOverviewEdge() {
  // Outline canvas always draws the active trace edges to visible ports.
  return true;
}
function moduleBusPath(a, b, spread, cross, backwards) {
  const lanePad = 34 + Math.min(46, Math.abs(cross) * .55);
  const sourceLaneX = a.x + (backwards ? -lanePad : lanePad);
  const targetLaneX = b.x + (backwards ? lanePad : -lanePad);
  const midY = (a.y + b.y) / 2 + cross;
  return `M ${a.x} ${a.y + spread * .18} C ${sourceLaneX} ${a.y + spread * .18}, ${sourceLaneX} ${midY}, ${sourceLaneX} ${midY} L ${targetLaneX} ${midY} C ${targetLaneX} ${midY}, ${targetLaneX} ${b.y + spread * .18}, ${b.x} ${b.y + spread * .18}`;
}
/** Wires always leave the out-port going outward and enter the in-port from outside. */
function directedWirePath(a, b, spread = 0, cross = 0) {
  const outStub = 44; // exit to the right of out-port
  const inStub = 44;  // approach from the left of in-port
  const span = Math.max(80, Math.abs(b.x - a.x));
  const c1x = a.x + outStub + span * .22;
  const c2x = b.x - inStub - span * .22;
  const c1y = a.y + spread * .12;
  const c2y = b.y + spread * .12 + cross;
  // Horizontal stubs so the tangent at each node faces the port direction.
  return `M ${a.x} ${a.y} L ${a.x + outStub} ${a.y} C ${c1x} ${c1y}, ${c2x} ${c2y}, ${b.x - inStub} ${b.y} L ${b.x} ${b.y}`;
}
function drawEdges() {
  wires.innerHTML = '';
  scene.querySelectorAll('.connected-port').forEach(port => port.classList.remove('connected-port'));
  scene.querySelectorAll('.frame.trace-lit').forEach(el => el.classList.remove('trace-lit'));
  const liveEdges = activeTraceEdges();
  const liveNodes = activeTraceNodes();
  const previewing = !!hoverPreviewTrace();
  if (!liveEdges.size) return;
  for (const id of liveNodes) {
    scene.querySelector(`[data-id="${CSS.escape(id)}"],[data-module-box="${CSS.escape(id)}"]`)?.classList.add('trace-lit');
  }
  const unique = new Map();
  for (const edge of edgeTypes()) {
    if (!liveEdges.has(edge.id)) continue;
    if (sameModuleOrInternalContainer(edge)) continue;
    const from = endpointFor(edge, 'from'), to = endpointFor(edge, 'to');
    if (!from || !to || from === to) continue;
    const key = isDetailedEndpoint(from) || isDetailedEndpoint(to) ? edge.id : `${from}:${to}:${edge.type}`;
    if (!unique.has(key)) unique.set(key, { ...edge, from, to });
  }
  const rendered = [...unique.values()].map((edge, index) => ({ edge, index, a: point(edge.from, 'out'), b: point(edge.to, 'in') })).filter(item => item.a && item.b);
  const crossOffsets = crossingOffsets(rendered);
  const pairCounts = new Map();
  rendered.forEach(({ edge }) => { const key = `${edge.from}:${edge.to}`; pairCounts.set(key, (pairCounts.get(key) || 0) + 1); });
  const pairSeen = new Map();
  rendered.forEach(({ edge, index, a, b }) => {
    markEndpoint(edge.from, 'out'); markEndpoint(edge.to, 'in');
    const pairKey = `${edge.from}:${edge.to}`;
    const pairIndex = pairSeen.get(pairKey) || 0;
    pairSeen.set(pairKey, pairIndex + 1);
    const total = pairCounts.get(pairKey) || 1;
    const spread = (pairIndex - (total - 1) / 2) * Math.min(14, Math.max(6, 36 / total));
    const cross = crossOffsets.get(edge.id) || 0;
    const pathData = directedWirePath(a, b, spread, cross);
    const path = document.createElementNS('http://www.w3.org/2000/svg', 'path');
    path.setAttribute('d', pathData);
    const origin = originTintForEdge(edge);
    path.setAttribute('class', `wire ${traceMode ? 'moving' : 'static'} ${edge.type} flow-stage ${previewing ? 'preview' : 'committed'}`);
    if (origin) {
      path.style.stroke = origin;
      path.style.setProperty('--wire', origin);
    }
    path.style.setProperty('--delay', `${index * -0.1}s`);
    path.append(Object.assign(document.createElementNS('http://www.w3.org/2000/svg', 'title'), { textContent: `${edge.type}: ${edge.evidence}` }));
    wires.append(path);
  });
}
function originTintForEdge(edge) {
  const from = node(edge.from);
  if (!from) return null;
  if (from.kind === 'folder') return folderTint(from);
  const file = fileOf(from) || (from.kind === 'file' ? from : null);
  if (file) return fileTint(file);
  return null;
}
function bindHoverTrace() {
  const setHover = id => {
    if (hoverId === id) return;
    hoverId = id;
    world.classList.toggle('previewing', traceMode && !!id && id !== selectedId);
    scene.querySelectorAll('.frame.hot').forEach(el => el.classList.remove('hot'));
    if (id) scene.querySelector(`[data-id="${CSS.escape(id)}"],[data-module-box="${CSS.escape(id)}"]`)?.classList.add('hot');
    // Live hover traces only when the Live toggle is on.
    if (traceMode) drawEdges();
    refreshFocusClasses();
  };
  scene.querySelectorAll('.frame.float').forEach(frame => {
    frame.addEventListener('pointerenter', event => {
      event.stopPropagation();
      clearTimeout(hoverTimer);
      setHover(frame.dataset.moduleBox || frame.dataset.id || frame.dataset.hover);
    });
    frame.addEventListener('pointerleave', event => {
      if (frame.contains(event.relatedTarget)) return;
      clearTimeout(hoverTimer);
      hoverTimer = setTimeout(() => setHover(null), 60);
    });
  });
}
function point(id, side) {
  const selector = id.startsWith('source:') ? `[data-source-port="${CSS.escape(id)}"]` : id.startsWith('import:') ? `[data-import-port="${CSS.escape(id)}"]` : id.startsWith('inline-module:') ? `[data-inline-module="${CSS.escape(id.slice(14))}"]` : id.startsWith('module:') ? `[data-module="${CSS.escape(id.slice(7))}"]` : id.startsWith('inline:') ? `[data-inline-file="${CSS.escape(id.slice(7))}"]` : `[data-id="${CSS.escape(id)}"]`;
  const element = scene.querySelector(selector); if (!element) return null; const worldRect = world.getBoundingClientRect(), rect = element.getBoundingClientRect();
  if (id.startsWith('source:') || id.startsWith('import:')) return { x: ((side === 'out' ? rect.right : rect.left) - worldRect.left) / canvas.scale, y: (rect.top - worldRect.top + rect.height / 2) / canvas.scale };
  const moduleId = id.startsWith('inline-module:') ? id.slice(14) : id.startsWith('module:') ? id.slice(7) : null;
  const portId = moduleId || (id.startsWith('inline:') ? id.slice(7) : id);
  const port = element.querySelector(`[data-port-for="${CSS.escape(portId)}"][data-port-side="${side}"]`);
  if (port) {
    const portRect = port.getBoundingClientRect();
    return { x: ((side === 'out' ? portRect.right : portRect.left) - worldRect.left) / canvas.scale, y: (portRect.top - worldRect.top + portRect.height / 2) / canvas.scale };
  }
  return { x: ((side === 'out' ? rect.right : rect.left) - worldRect.left) / canvas.scale, y: (rect.top - worldRect.top + rect.height / 2) / canvas.scale };
}
function nearestVisibleFolder(item) {
  for (let cursor = item?.kind === 'folder' ? item : node(item?.parentId); cursor; cursor = node(cursor.parentId)) {
    if (scene.querySelector(`[data-id="${CSS.escape(cursor.id)}"]`)) return cursor;
  }
  return null;
}
function applyCanvas() { world.style.transform = `translate(${canvas.x}px,${canvas.y}px) scale(${canvas.scale})`; scheduleMinimap(); }
function canvasFocusTarget(element) {
  if (!element) return null;
  const worldRect = world.getBoundingClientRect();
  const rect = element.getBoundingClientRect();
  const left = (rect.left - worldRect.left) / canvas.scale;
  const top = (rect.top - worldRect.top) / canvas.scale;
  const right = (rect.right - worldRect.left) / canvas.scale;
  const bottom = (rect.bottom - worldRect.top) / canvas.scale;
  const scale = Math.min(1.18, Math.max(.5, Math.min((board.clientWidth - 220) / Math.max(1, right - left), (board.clientHeight - 180) / Math.max(1, bottom - top))));
  return {
    x: board.clientWidth / 2 - (left + right) / 2 * scale,
    y: board.clientHeight / 2 - (top + bottom) / 2 * scale,
    scale
  };
}
function smoothFocusSelection({ duration = 1300 } = {}) {
  const element = elementForSelection();
  const target = canvasFocusTarget(element);
  if (!target) return fitMap();
  if (document.body.classList.contains('reduce-motion')) {
    canvas.x = target.x; canvas.y = target.y; canvas.scale = target.scale;
    applyCanvas();
    return;
  }
  const start = { x: canvas.x, y: canvas.y, scale: canvas.scale };
  const t0 = performance.now();
  if (canvasAnim) cancelAnimationFrame(canvasAnim);
  board.classList.add('camera-animating');
  const step = now => {
    const t = Math.min(1, (now - t0) / duration);
    const ease = 1 - Math.pow(1 - t, 3);
    canvas.x = start.x + (target.x - start.x) * ease;
    canvas.y = start.y + (target.y - start.y) * ease;
    canvas.scale = start.scale + (target.scale - start.scale) * ease;
    applyCanvas();
    if (t < 1) canvasAnim = requestAnimationFrame(step);
    else { canvasAnim = 0; board.classList.remove('camera-animating'); }
  };
  canvasAnim = requestAnimationFrame(step);
}
function dismissAgentEditReveal() {
  clearTimeout(agentRevealTimer);
  agentRevealTimer = 0;
  const id = agentRevealExpandedId;
  agentRevealExpandedId = null;
  agentRevealPath = null;
  if (id && expandedFiles.has(id) && selectedId === id) expandedFiles.delete(id);
  render();
  updateInspector();
}
function playAgentEditReveal(path) {
  if (!autoRevealChanges || !graph || !path) return;
  const normalized = String(path).replaceAll('\\', '/');
  const file = fileByPath(normalized);
  if (!file) return;
  if (agentRevealPath && agentRevealPath !== normalized) dismissAgentEditReveal();
  clearTimeout(agentRevealTimer);
  agentRevealPath = normalized;
  agentRevealExpandedId = file.id;
  expandAncestors(file);
  pruneFolderDepth();
  expandedFiles.add(file.id);
  selectedId = file.id;
  layoutAnchorFileId = file.id;
  focusedFileId = file.id;
  flowMode = true;
  rebuildTrace();
  render();
  updateInspector();
  requestAnimationFrame(() => {
    smoothFocusSelection({ duration: 1400 });
    pulseSelection();
    $('#diff-panel')?.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
  });
  agentRevealTimer = setTimeout(() => {
    if (agentRevealPath !== normalized) return;
    dismissAgentEditReveal();
  }, agentRevealDwellMs);
}
function directManipulation() {
  board.classList.add('panning', 'zooming');
  clearTimeout(directManipulationTimer);
  directManipulationTimer = setTimeout(() => board.classList.remove('panning', 'zooming'), 140);
}
function scheduleDraw() { if (drawFrame) return; drawFrame = requestAnimationFrame(() => { drawFrame = 0; drawEdges(); }); }
function animateReflowEdges(duration = 780) {
  reflowDrawUntil = Math.max(reflowDrawUntil, performance.now() + duration);
  if (reflowFrame) return;
  const tick = () => {
    drawEdges();
    if (performance.now() < reflowDrawUntil) reflowFrame = requestAnimationFrame(tick);
    else reflowFrame = 0;
  };
  reflowFrame = requestAnimationFrame(tick);
}
function scheduleMinimap() { if (miniFrame) return; miniFrame = requestAnimationFrame(() => { miniFrame = 0; renderMinimap(); }); }
function resizeZones(groups) {
  const worldRect = world.getBoundingClientRect();
  for (const group of groups) {
    const cards = [...scene.querySelectorAll(`.card[data-boundary="${CSS.escape(group)}"]`)]; const zone = scene.querySelector(`.zone[data-zone="${CSS.escape(group)}"]`); if (!cards.length || !zone) continue;
    const boxes = cards.map(card => card.getBoundingClientRect()); const left = Math.min(...boxes.map(box => (box.left - worldRect.left) / canvas.scale)) - 18, top = Math.min(...boxes.map(box => (box.top - worldRect.top) / canvas.scale)) - 25, right = Math.max(...boxes.map(box => (box.right - worldRect.left) / canvas.scale)) + 18, bottom = Math.max(...boxes.map(box => (box.bottom - worldRect.top) / canvas.scale)) + 18;
    Object.assign(zone.style, { left: `${left}px`, top: `${top}px`, width: `${right - left}px`, height: `${bottom - top}px` });
  }
}
function visibleDragMembers(card, item) {
  return [card];
}
function bindFrameDrag(frame) {
  const id = frame.dataset.dragId;
  if (!id) return;
  let drag;
  let raf = 0;
  const onBar = event => event.target.closest('.frame-bar') && !event.target.closest('button,a,[data-pin]');
  const applyDragVisual = () => {
    raf = 0;
    if (!drag) return;
    const { dx, dy } = drag;
    if (drag.nested && drag.parentId) {
      // Visual-only during drag; commit localOffsets on pointerup.
      frame.style.translate = `${dx}px ${dy}px`;
      if (drag.parentEl) {
        drag.parentEl.style.width = `${drag.parentBaseW + Math.abs(dx) * .4}px`;
      }
      if (drag.canvasEl) {
        drag.canvasEl.style.height = `${drag.canvasBaseH + Math.abs(dy) * .4}px`;
      }
    } else {
      const allowOver = markDropTarget(drag.pointerX, drag.pointerY, drag.islandId);
      const resolved = resolveIslandOverlapDrag(drag.islandId, drag.islandEl, drag.ox, drag.oy, dx, dy, allowOver);
      drag.dx = resolved.x - drag.ox;
      drag.dy = resolved.y - drag.oy;
      const value = { x: resolved.x, y: resolved.y };
      offsets.set(drag.islandId, value);
      drag.islandEl.style.translate = `${value.x}px ${value.y}px`;
      drag.islandEl.style.setProperty('--ox', `${value.x}px`);
      drag.islandEl.style.setProperty('--oy', `${value.y}px`);
    }
    scheduleDraw();
  };
  frame.addEventListener('pointerdown', event => {
    if (event.button !== 0 || !onBar(event)) return;
    event.stopPropagation();
    clearTimeout(gravityTimer);
    const islandId = dragIslandId(id);
    const islandEl = scene.querySelector(`[data-drag-id="${CSS.escape(islandId)}"]`) || frame;
    const current = offsets.get(islandId) || { x: 0, y: 0 };
    const parentId = parentCanvasId(id);
    const parentEl = parentId ? scene.querySelector(`[data-drag-id="${CSS.escape(parentId)}"]`) : null;
    const local = localOffsets.get(id) || { x: 0, y: 0 };
    const canvasEl = parentEl?.querySelector(':scope > .frame-canvas');
    drag = {
      id, islandId, islandEl, parentId, parentEl, canvasEl,
      nested: islandId !== id,
      parentBaseW: parentEl?.offsetWidth || 0,
      canvasBaseH: canvasEl?.offsetHeight || 0,
      x: event.clientX, y: event.clientY,
      ox: current.x, oy: current.y,
      lx: local.x, ly: local.y,
      dx: 0, dy: 0,
      pointerX: event.clientX, pointerY: event.clientY,
      moved: false, remembered: false
    };
    draggingTraceAnchorId = islandId;
    frame.classList.add('dragging');
    islandEl.classList.add('dragging');
    parentEl?.classList.add('deforming');
    app.classList.add('dragging');
    frame.setPointerCapture(event.pointerId);
  });
  frame.addEventListener('pointermove', event => {
    if (!drag) return;
    const dx = (event.clientX - drag.x) / canvas.scale;
    const dy = (event.clientY - drag.y) / canvas.scale;
    drag.moved ||= Math.abs(dx) + Math.abs(dy) > 3;
    if (drag.moved && !drag.remembered) { remember(); drag.remembered = true; }
    drag.dx = dx; drag.dy = dy;
    drag.pointerX = event.clientX;
    drag.pointerY = event.clientY;
    if (!raf) raf = requestAnimationFrame(applyDragVisual);
  });
  const end = () => {
    if (!drag) return;
    if (raf) { cancelAnimationFrame(raf); raf = 0; applyDragVisual(); }
    const parentId = drag.parentId;
    const nested = drag.nested;
    const dx = drag.dx || 0, dy = drag.dy || 0;
    const draggedId = drag.id;
    const islandId = drag.islandId;
    const lx = drag.lx, ly = drag.ly;
    drag.parentEl?.classList.remove('deforming');
    clearDropTargets();
    if (drag.moved) {
      frame.dataset.dragged = String(Date.now());
      pinnedLayout.add(islandId);
      if (nested && parentId) {
        // Keep visual translate until render() rebuilds — clearing it first snaps back.
        localOffsets.set(draggedId, { x: lx + dx, y: ly + dy });
        skipFlipOnce = true;
        render();
        requestAnimationFrame(() => animateReflowEdges(1400));
      } else {
        const settled = resolveIslandOverlapDrag(islandId, drag.islandEl, drag.ox, drag.oy, dx, dy, null);
        offsets.set(islandId, { x: settled.x, y: settled.y });
        drag.islandEl.style.translate = `${settled.x}px ${settled.y}px`;
        drag.islandEl.style.setProperty('--ox', `${settled.x}px`);
        drag.islandEl.style.setProperty('--oy', `${settled.y}px`);
        animateReflowEdges(900);
        scheduleGravityDrift(1200);
      }
    } else {
      scheduleGravityDrift();
    }
    drag.islandEl?.classList.remove('dragging');
    drag = null;
    frame.classList.remove('dragging');
    app.classList.remove('dragging');
    draggingTraceAnchorId = null;
    drawEdges();
    renderMinimap();
  };
  frame.addEventListener('pointerup', end);
  frame.addEventListener('pointercancel', end);
}
function focusFolderFrame(folder, { expand = true, event = null } = {}) {
  if (!folder || folder.kind !== 'folder') return;
  if (agentRevealPath) {
    clearTimeout(agentRevealTimer);
    agentRevealPath = null;
    agentRevealExpandedId = null;
  }
  remember();
  if (event) captureClickAnchor(folder.id, event);
  activateFocus(folder);
  layoutAnchorFileId = folder.id;
  if (expand && folder.id !== displayRoot()?.id) {
    expandedFolders.add(folder.id);
    pruneFolderDepth();
  }
  selectItem(folder.id);
  flowMode = true;
  rebuildTrace();
  render();
  updateInspector();
  requestAnimationFrame(() => {
    stabilizeClickAnchor();
    animateReflowEdges(1400);
    pulseSelection();
  });
}
function focusFileFrame(file, { expand = true, event = null } = {}) {
  if (!file) return;
  if (agentRevealPath && file.id !== agentRevealExpandedId) {
    clearTimeout(agentRevealTimer);
    agentRevealPath = null;
    agentRevealExpandedId = null;
  }
  remember();
  if (event) captureClickAnchor(file.id, event);
  activateFocus(file);
  layoutAnchorFileId = file.id;
  if (expand) expandedFiles.add(file.id);
  selectItem(file.id);
  flowMode = true;
  rebuildTrace();
  render();
  updateInspector();
  requestAnimationFrame(() => {
    stabilizeClickAnchor();
    animateReflowEdges(900);
    pulseSelection();
  });
}
function highlightLine(text, language = '') {
  let html = escape(text || ' ');
  const py = /python/i.test(language);
  const comment = py
    ? html.replace(/(#.*)$/g, '<span class="tok-cm">$1</span>')
    : html.replace(/(\/\/.*)$/g, '<span class="tok-cm">$1</span>');
  html = comment
    .replace(/(&quot;.*?&quot;|&#39;.*?&#39;|`.*?`)/g, '<span class="tok-str">$1</span>')
    .replace(/\b(\d+(?:\.\d+)?)\b/g, '<span class="tok-num">$1</span>');
  const keywords = py
    ? /\b(def|class|return|import|from|as|if|elif|else|for|while|with|try|except|yield|async|await|True|False|None|self|pass|raise|and|or|not|in|is)\b/g
    : /\b(function|const|let|var|return|import|from|export|default|class|extends|if|else|for|while|try|catch|async|await|new|typeof|interface|type|enum|public|private|protected|static|void|null|undefined|true|false)\b/g;
  html = html.replace(keywords, '<span class="tok-kw">$1</span>');
  html = html.replace(/\b([A-Za-z_][\w]*)\s*(?=\()/g, '<span class="tok-fn">$1</span>');
  return html;
}
function connectWindow(file, edge, role) {
  const source = file?.meta?.source || '';
  const lines = source.split('\n');
  if (!lines.length) return '';
  const hit = Math.max(1, Math.min(lines.length, edge?.line || (role === 'here' ? 1 : 1)));
  const start = Math.max(1, hit - 2);
  const end = Math.min(lines.length, Math.max(start + 4, hit + 2));
  const body = lines.slice(start - 1, end).map((text, index) => {
    const line = start + index;
    const cls = line === hit ? 'flow-line hit-edge' : 'flow-line';
    return `<span class="${cls}"><i>${line}</i><code>${highlightLine(text, file?.language)}</code></span>`;
  }).join('');
  return `<div class="flow-connect hit" data-connect-line="${hit}">
    <header>${escape(edge?.type || 'trace')} · L${hit} · ±2 context</header>
    <pre class="flow-code">${body}</pre>
  </div>`;
}
function codeBlockHtml(item, { edge, role } = {}) {
  const file = fileOf(item) || (item.kind === 'file' ? item : null);
  const source = file?.meta?.source || '';
  const lines = source.split('\n');
  let start = 1, end = Math.min(lines.length, 24);
  let hitStart = null, hitEnd = null;
  if (item.kind === 'module' && item.loc) {
    start = item.loc.start;
    end = Math.min(lines.length, Math.max(start, Math.min(item.loc.end || start, start + 40)));
    hitStart = item.loc.start;
    hitEnd = item.loc.end || item.loc.start;
  }
  if (edge?.line && role !== 'here') {
    hitStart = edge.line;
    hitEnd = edge.line;
  }
  const code = lines.slice(start - 1, end).map((text, index) => {
    const line = start + index;
    const hit = hitStart != null && line >= hitStart && line <= hitEnd;
    return `<span class="flow-line${hit ? ' hit' : ''}"><i>${line}</i><code>${highlightLine(text, file?.language)}</code></span>`;
  }).join('') || '<span class="flow-line"><i>—</i><code>No source</code></span>';
  const glyph = file ? fileGlyph(file) : { g: '·', c: 'var(--muted)' };
  const title = item.kind === 'module' ? `${item.label}()` : item.label;
  const meta = edge ? `${edge.type}${edge.line ? ` · L${edge.line}` : ''}` : (item.kind === 'module' ? `L${start}–${end}` : file?.path || '');
  const connect = edge && file ? connectWindow(file, edge, role) : (role === 'here' && file && hitStart ? connectWindow(file, { type: 'focus', line: hitStart }, role) : '');
  return `<article class="flow-card ${role || ''}" data-flow-jump="${item.id}" data-flow-role="${role || ''}" data-flow-edge="${edge?.id || ''}">
    <div class="flow-card-head">
      <span class="file-glyph" style="--glyph:${glyph.c}">${escape(glyph.g)}</span>
      <b>${escape(title)}</b>
      <span>${escape(meta)}</span>
    </div>
    <small>${escape(file?.path || item.path || '')}</small>
    <pre class="flow-code">${code}</pre>
    ${connect}
  </article>`;
}
function flowNeighbors(focus) {
  const seeds = new Set(sourceSeeds(focus));
  const upstream = [];
  const downstream = [];
  for (const edge of (graph?.edges || []).filter(e => FLOW_TYPES.has(e.type))) {
    if (seeds.has(edge.to) && !seeds.has(edge.from)) {
      const other = node(edge.from);
      if (other) upstream.push({ edge, other });
    }
    if (seeds.has(edge.from) && !seeds.has(edge.to)) {
      const other = node(edge.to);
      if (other) downstream.push({ edge, other });
    }
  }
  const rank = type => ({ inherits: 0, calls: 1, dataflow: 2, events: 3, imports: 4, references: 5, reexports: 6 }[type] ?? 9);
  const dedupe = list => list
    .filter((item, index, arr) => arr.findIndex(x => x.other.id === item.other.id && x.edge.type === item.edge.type) === index)
    .sort((a, b) => rank(a.edge.type) - rank(b.edge.type) || (a.other.label || '').localeCompare(b.other.label || ''))
    .slice(0, 16);
  return { upstream: dedupe(upstream), downstream: dedupe(downstream) };
}
function drawFlowOverlayWires(upstream, downstream) {
  const svg = $('#flow-wires');
  const body = svg?.closest('.flow-body');
  if (!svg || !body) return;
  const bodyRect = body.getBoundingClientRect();
  const focusCard = $('#flow-focus')?.querySelector('.flow-card.here');
  if (!focusCard) { svg.innerHTML = ''; return; }
  const focusRect = focusCard.getBoundingClientRect();
  const fx = focusRect.left - bodyRect.left;
  const fy = focusRect.top - bodyRect.top + focusRect.height * .35;
  const paths = [];
  const link = (card, side, type) => {
    if (!card) return;
    const rect = card.getBoundingClientRect();
    const x1 = side === 'from' ? rect.right - bodyRect.left : fx;
    const y1 = rect.top - bodyRect.top + Math.min(rect.height * .4, 48);
    const x2 = side === 'from' ? fx : rect.left - bodyRect.left;
    const y2 = side === 'from' ? fy : rect.top - bodyRect.top + Math.min(rect.height * .4, 48);
    const mid = (x1 + x2) / 2;
    paths.push(`<path class="flow-wire ${escape(type || '')}" d="M${x1},${y1} C${mid},${y1} ${mid},${y2} ${x2},${y2}" />`);
  };
  $('#flow-upstream')?.querySelectorAll('.flow-card').forEach((card, index) => {
    link(card, 'from', upstream[index]?.edge?.type || 'calls');
  });
  $('#flow-downstream')?.querySelectorAll('.flow-card').forEach((card, index) => {
    link(card, 'to', downstream[index]?.edge?.type || 'calls');
  });
  svg.setAttribute('viewBox', `0 0 ${bodyRect.width} ${bodyRect.height}`);
  svg.innerHTML = paths.join('');
}
function openFlowOverlay(item, { narrative } = {}) {
  const focus = item?.kind === 'file' ? (modules(item)[0] || item) : item;
  if (!focus || !graph) return;
  const file = fileOf(focus) || (focus.kind === 'file' ? focus : null);
  const { upstream, downstream } = flowNeighbors(focus);
  const dialog = $('#flow-overlay');
  $('#flow-kicker').textContent = focus.kind === 'module' ? 'MODULE FLOW' : 'FILE FLOW';
  $('#flow-title').textContent = focus.kind === 'module' ? `${focus.label}()` : focus.label;
  $('#flow-path').textContent = file?.path || focus.path || '';
  $('#flow-focus-meta').textContent = focus.kind === 'module' ? `lines ${focus.loc?.start || '?'}–${focus.loc?.end || '?'}` : `${modules(file || {}).length} modules`;
  const story = narrative || [
    upstream.length ? `${upstream.length} upstream` : 'no upstream',
    downstream.length ? `${downstream.length} downstream` : 'no downstream'
  ].join(' · ');
  const narrativeEl = $('#flow-narrative');
  narrativeEl.hidden = !story;
  narrativeEl.textContent = story;
  $('#flow-upstream').innerHTML = upstream.map(({ edge, other }) => codeBlockHtml(other, { edge, role: 'from' })).join('') || '<p class="flow-empty">Nothing feeds into this node statically.</p>';
  $('#flow-focus').innerHTML = codeBlockHtml(focus, { role: 'here' });
  $('#flow-downstream').innerHTML = downstream.map(({ edge, other }) => codeBlockHtml(other, { edge, role: 'to' })).join('') || '<p class="flow-empty">Nothing consumes this node statically.</p>';
  dialog?.querySelectorAll('[data-flow-jump]').forEach(card => card.addEventListener('click', event => {
    if (event.target.closest('.flow-code, .flow-connect')) return;
    const target = node(card.dataset.flowJump);
    if (!target) return;
    closeFlowOverlay();
    if (target.kind === 'module') openFlowOverlay(target);
    else focusFileFrame(fileOf(target) || target);
  }));
  if (dialog && !dialog.open) dialog.showModal();
  selectItem(focus.id);
  activateFocus(focus);
  if (file) expandedFiles.add(file.id);
  rebuildTrace();
  render();
  requestAnimationFrame(() => {
    stabilizeClickAnchor();
    animateReflowEdges(1000);
    drawFlowOverlayWires(upstream, downstream);
    const columns = dialog?.querySelector('.flow-columns');
    columns?.addEventListener('scroll', () => drawFlowOverlayWires(upstream, downstream), { passive: true });
  });
}
function closeFlowOverlay() {
  const dialog = $('#flow-overlay');
  if (dialog?.open) dialog.close();
}
function bindScene() {
  scene.querySelectorAll('.frame.float[data-drag-id]').forEach(bindFrameDrag);
  scene.querySelectorAll('[data-folder-expand]').forEach(button => button.addEventListener('click', event => {
    event.stopPropagation();
    const id = button.dataset.folderExpand;
    const item = node(id);
    if (!item) return;
    remember();
    captureClickAnchor(id, event);
    toggleFolder(id);
    selectItem(id);
    flowMode = true;
    rebuildTrace();
    render();
    updateInspector();
    requestAnimationFrame(() => {
      stabilizeClickAnchor();
      animateReflowEdges(1400);
      pulseSelection();
    });
  }));
  scene.querySelectorAll('[data-expand]').forEach(button => button.addEventListener('click', event => {
    event.stopPropagation();
    const file = node(button.dataset.expand);
    if (!file) return;
    if (expandedFiles.has(file.id)) {
      remember();
      captureClickAnchor(file.id, event);
      expandedFiles.delete(file.id);
      selectItem(file.id);
      render();
      updateInspector();
      requestAnimationFrame(() => {
        stabilizeClickAnchor();
        animateReflowEdges(720);
      });
    } else {
      focusFileFrame(file, { expand: true, event });
    }
  }));
  scene.querySelectorAll('[data-focus-file]').forEach(button => button.addEventListener('click', event => {
    if (Date.now() - Number(button.closest('.frame')?.dataset.dragged || 0) < 220) return;
    event.stopPropagation();
    focusFileFrame(node(button.dataset.focusFile), { expand: true, event });
  }));
  scene.querySelectorAll('.outline-label[data-inline]:not([data-focus-file])').forEach(row => {
    row.addEventListener('click', event => {
      if (event.target.closest('[data-pin]') || Date.now() - Number(row.closest('.frame')?.dataset.dragged || 0) < 220) return;
      event.stopPropagation();
      const item = node(row.dataset.inline);
      if (!item) return;
      if (item.kind === 'file') return focusFileFrame(item, { expand: true, event });
      if (item.kind === 'folder') return focusFolderFrame(item, { expand: true, event });
      activateFocus(item);
      captureClickAnchor(item.id, event);
      selectItem(item.id);
      render();
      updateInspector();
      requestAnimationFrame(() => stabilizeClickAnchor());
    });
    row.addEventListener('dblclick', event => {
      event.stopPropagation();
      const item = node(row.dataset.inline);
      if (!item || item.kind !== 'folder') return;
      remember();
      captureClickAnchor(item.id, event);
      toggleFolder(item.id);
      focusFolderFrame(item, { expand: false, event });
    });
  });
  scene.querySelectorAll('.frame-fn[data-open-flow]').forEach(element => element.addEventListener('click', event => {
    if (event.target.closest('[data-pin]')) return;
    if (Date.now() - Number(element.dataset.dragged || 0) < 220) return;
    event.stopPropagation();
    const module = node(element.dataset.openFlow);
    if (module) openFlowOverlay(module);
  }));
  scene.querySelectorAll('[data-pin]').forEach(button => button.addEventListener('click', event => {
    event.stopPropagation();
    const id = button.dataset.pin;
    remember();
    pinned.has(id) ? pinned.delete(id) : pinned.add(id);
    rebuildTrace();
    render();
    updateInspector();
  }));
}
function initFlowOverlay() {
  $('#flow-close')?.addEventListener('click', () => closeFlowOverlay());
  $('#flow-overlay')?.addEventListener('click', event => {
    if (event.target === $('#flow-overlay')) closeFlowOverlay();
  });
  $('#flow-overlay')?.addEventListener('cancel', event => {
    event.preventDefault();
    closeFlowOverlay();
  });
}
function bindActivityFeed() {
  $('#activity-list')?.querySelectorAll('[data-open-change]').forEach(button => button.addEventListener('click', event => {
    event.stopPropagation();
    const path = button.dataset.openChange;
    if (!path) return;
    clearTimeout(agentRevealTimer);
    agentRevealPath = null;
    agentRevealExpandedId = null;
    playAgentEditReveal(path);
  }));
  $('#activity-list')?.querySelectorAll('[data-review-change]').forEach(button => button.addEventListener('click', event => {
    event.stopPropagation();
    reviewedPaths.add(button.dataset.reviewChange);
    archiveActivity(button.dataset.reviewChange);
    render(); updateInspector();
  }));
}
function refreshFocusClasses() {
  const selectedFile = fileOf(selected());
  const lit = activeTraceNodes();
  world.classList.toggle('flow-active', traceActive());
  world.classList.toggle('frames-active', true);
  world.classList.toggle('previewing', !!hoverPreviewTrace());
  world.classList.toggle('rails-active', false);
  scene.querySelectorAll('.frame-folder[data-id], .frame-file[data-id]').forEach(frame => {
    const item = node(frame.dataset.id);
    frame.classList.toggle('selected', frame.dataset.id === selectedId || frame.dataset.id === selectedFile?.id);
    frame.classList.toggle('focus-anchor', frame.dataset.id === focusedFileId);
    frame.classList.toggle('dim', outlineDim(item));
    frame.classList.toggle('trace-lit', lit.has(frame.dataset.id));
    frame.classList.toggle('agent-editing', frame.dataset.id === agentRevealExpandedId);
  });
  scene.querySelectorAll('.frame-fn').forEach(box => {
    const item = node(box.dataset.moduleBox);
    box.classList.toggle('selected', box.dataset.moduleBox === selectedId);
    box.classList.toggle('dim', outlineDim(item));
    box.classList.toggle('trace-lit', lit.has(box.dataset.moduleBox));
  });
}
function selectItem(id) {
  if (selectedId !== id) remember();
  selectedId = id; selectedImportEdgeId = undefined; rebuildTrace(); refreshFocusClasses(); drawEdges(); renderMinimap(); updateInspector(); writeDeepLink();
}
function updateInspector() {
  const item = selected() || entryFile(); if (!item) return;
  const file = fileOf(item) || (item.kind === 'file' ? item : null);
  const related = edgeTypes().filter(edge => edge.from === item.id || edge.to === item.id || (file && (edge.from === file.id || edge.to === file.id)));
  const region = mapRegion(file || item);
  $('#inspect-kind').textContent = `${item.kind.toUpperCase()} · FRAME · ${region.toUpperCase()}`;
  $('#inspect-title').textContent = item.kind === 'module' ? `${item.label}()` : item.label;
  $('#inspect-path').textContent = item.path || file?.path || '/';
  $('#inspect-trace').textContent = related.length
    ? `${related.length} live relationship${related.length === 1 ? '' : 's'}. Focused nodes slowly drift into a shared band.`
    : 'No direct relationships with the current edge filters.';
  const structure = $('#inspect-structure');
  if (structure) {
    const glyph = file?.kind === 'file' ? fileGlyph(file) : null;
    const mods = file?.kind === 'file' ? modules(file).slice(0, 8) : [];
    const folderKids = item.kind === 'folder' ? folderItems(item).slice(0, 8) : [];
    structure.innerHTML = [
      glyph ? `<div class="struct-row"><span class="file-glyph" style="--glyph:${glyph.c}">${escape(glyph.g)}</span><span>${escape(file.extension || 'file')} · ${file.language || 'asset'}</span></div>` : '',
      item.kind === 'folder' ? `<div class="struct-row muted">${folderKids.length} direct · ${filesBelow(item).length} files · depth cap 2</div>` : '',
      ...folderKids.map(child => {
        const g = child.kind === 'file' ? fileGlyph(child) : null;
        return `<button type="button" class="struct-jump" data-jump="${child.id}">${g ? `<span class="file-glyph" style="--glyph:${g.c}">${escape(g.g)}</span>` : (() => { const fi = folderIcon(child); return `<span class="folder-glyph compact" style="--accent:${fi.c}">${fi.g}</span>`; })()}<span>${escape(child.label)}</span></button>`;
      }),
      ...mods.map(module => `<button type="button" class="struct-jump" data-jump="${module.id}" data-open-flow-jump="${module.id}"><em>fn</em><span>${escape(module.label)}()</span></button>`)
    ].filter(Boolean).join('') || '<div class="struct-row muted">Select a frame to see its contents.</div>';
    structure.querySelectorAll('[data-jump]').forEach(button => button.addEventListener('click', () => {
      const target = node(button.dataset.jump);
      if (!target) return;
      clearTimeout(agentRevealTimer);
      agentRevealPath = null;
      agentRevealExpandedId = null;
      if (button.dataset.openFlowJump) return openFlowOverlay(target);
      if (target.kind === 'file') return focusFileFrame(target);
      remember();
      if (target.kind === 'folder') { toggleFolder(target.id); selectItem(target.id); }
      else selectItem(target.id);
      render();
      updateInspector();
    }));
  }
  $('#inspect-edges').innerHTML = related.slice(0, 9).map(edge => `<div><code>${edge.from === item.id ? '→' : '←'}</code> ${escape(edge.type)} · ${escape(edge.evidence)}${edge.line ? ` · line ${edge.line}` : ''}</div>`).join('') || '<div>No direct relationships.</div>';
  const sourcePanel = $('#source-panel'), sourceTarget = $('#inspect-source');
  if (file?.kind === 'file' && file.meta?.source) { sourcePanel.hidden = false; sourceTarget.innerHTML = sourceHtml(file); bindInspectorSource(); }
  else { sourcePanel.hidden = true; sourceTarget.innerHTML = ''; }
  if (item.kind === 'module') requestAnimationFrame(() => $('#inspect-source .line.active-module')?.scrollIntoView({ block: 'center', behavior: 'smooth' }));
  const panel = $('#diff-panel');
  const diffEl = $('#diff-code');
  const showDiff = file && (file.git?.change || recentFor(file));
  if (panel && diffEl) {
    panel.hidden = !showDiff;
    panel.classList.toggle('live', showDiff && agentRevealPath === file.path);
    if (showDiff) {
      $('#diff-meta').textContent = file.git?.change || 'live edit';
      diffEl.innerHTML = formatDiffHtml(file);
      if (agentRevealPath === file.path) {
        requestAnimationFrame(() => panel.scrollIntoView({ behavior: 'smooth', block: 'nearest' }));
      }
    } else {
      $('#diff-meta').textContent = '';
      diffEl.innerHTML = '';
    }
  }
}
function bindInspectorSource() {
  $('#inspect-source').querySelectorAll('[data-pin]').forEach(button => button.addEventListener('click', event => { event.stopPropagation(); const id = button.dataset.pin; remember(); pinned.has(id) ? pinned.delete(id) : pinned.add(id); rebuildTrace(); render(); updateInspector(); }));
}
function renderMinimap() {
  if (!graph) return;
  const w = 160, h = 104;
  const scale = Math.min(w / Math.max(1, world.offsetWidth), h / Math.max(1, world.offsetHeight));
  const nodes = [...scene.querySelectorAll('.frame > .frame-bar')].map(row => {
    const id = row.dataset.outlineRow;
    const rect = row.getBoundingClientRect();
    const worldRect = world.getBoundingClientRect();
    const x = (rect.left - worldRect.left) / canvas.scale + rect.width / (2 * canvas.scale);
    const y = (rect.top - worldRect.top) / canvas.scale + rect.height / (2 * canvas.scale);
    return `<i class="mini-node ${id === selectedId ? 'selected' : ''}" style="left:${x * scale}px;top:${y * scale}px"></i>`;
  }).join('');
  minimap.innerHTML = `${nodes}<i class="mini-viewport" style="left:${-canvas.x * scale}px;top:${-canvas.y * scale}px;width:${board.clientWidth * scale / canvas.scale}px;height:${board.clientHeight * scale / canvas.scale}px"></i>`;
}
function fitMap() {
  const tree = scene.querySelector('.frame-artboard') || scene.querySelector('.frame-stage');
  if (!tree) return;
  const stage = scene.querySelector('.frame-stage');
  const left = stage?.offsetLeft || tree.offsetLeft;
  const top = stage?.offsetTop || tree.offsetTop;
  const right = left + tree.offsetWidth;
  const bottom = top + tree.offsetHeight;
  const rawScale = Math.min((board.clientWidth - 96) / Math.max(1, right - left), (board.clientHeight - 88) / Math.max(1, bottom - top));
  canvas.scale = Math.min(1, Math.max(.42, rawScale));
  canvas.x = board.clientWidth / 2 - (left + right) / 2 * canvas.scale;
  canvas.y = Math.max(20, 56 - top * canvas.scale);
  applyCanvas();
}
function focusSelection() {
  const element = elementForSelection();
  if (!element) return fitMap();
  const worldRect = world.getBoundingClientRect();
  const rect = element.getBoundingClientRect();
  const left = (rect.left - worldRect.left) / canvas.scale, top = (rect.top - worldRect.top) / canvas.scale, right = (rect.right - worldRect.left) / canvas.scale, bottom = (rect.bottom - worldRect.top) / canvas.scale;
  canvas.scale = Math.min(1.18, Math.max(.5, Math.min((board.clientWidth - 220) / Math.max(1, right - left), (board.clientHeight - 180) / Math.max(1, bottom - top))));
  canvas.x = board.clientWidth / 2 - (left + right) / 2 * canvas.scale;
  canvas.y = board.clientHeight / 2 - (top + bottom) / 2 * canvas.scale;
  applyCanvas();
}
function elementForSelection() {
  const item = selected(); if (!item) return null;
  if (item.kind === 'module') {
    return scene.querySelector(`.frame-fn[data-module-box="${CSS.escape(item.id)}"]`)
      || scene.querySelector(`[data-inline-module="${CSS.escape(item.id)}"],[data-module="${CSS.escape(item.id)}"]`);
  }
  const file = fileOf(item);
  if (file) return scene.querySelector(`.frame-file[data-id="${CSS.escape(file.id)}"],[data-inline-file="${CSS.escape(file.id)}"]`);
  return scene.querySelector(`.frame[data-id="${CSS.escape(item.id)}"]`);
}
function keepSelectionVisible() {
  const element = elementForSelection(); if (!element) return;
  const margin = 44;
  const rect = element.getBoundingClientRect();
  const visibleWidth = Math.max(0, Math.min(rect.right, board.clientWidth) - Math.max(rect.left, 0));
  const visibleHeight = Math.max(0, Math.min(rect.bottom, board.clientHeight) - Math.max(rect.top, 0));
  const visibleRatio = (visibleWidth * visibleHeight) / Math.max(1, rect.width * rect.height);
  const centerVisible = rect.left + rect.width / 2 > 0 && rect.left + rect.width / 2 < board.clientWidth && rect.top + rect.height / 2 > 0 && rect.top + rect.height / 2 < board.clientHeight;
  if (visibleRatio > .48 && centerVisible) return;
  let dx = 0, dy = 0;
  if (rect.left < margin) dx = margin - rect.left;
  else if (rect.right > board.clientWidth - margin) dx = board.clientWidth - margin - rect.right;
  if (rect.top < margin) dy = margin - rect.top;
  else if (rect.bottom > board.clientHeight - margin) dy = board.clientHeight - margin - rect.bottom;
  if (Math.abs(dx) < 70) dx = 0;
  if (Math.abs(dy) < 70) dy = 0;
  if (!dx && !dy) return;
  canvas.x += dx;
  canvas.y += dy;
  applyCanvas();
}
function resetPresentation() {
  remember();
  exitFlow();
  offsets.clear();
  localOffsets.clear();
  layoutModes.clear();
  pinnedLayout.clear();
  basePlacements.clear();
  layoutMemory.clear();
  basePlacementKey = '';
  render();
  requestAnimationFrame(fitMap);
}
function canvasControls() {
  let pan, lastPanMoved = false, wheelRemainder = 0;
  const stopPan = () => { lastPanMoved = !!pan?.moved; pan = null; board.classList.remove('panning'); setTimeout(() => { lastPanMoved = false; }, 0); };
  board.addEventListener('pointerdown', event => { if (event.button !== 0 || event.target.closest('.frame,.frame-bar,button,#minimap')) return; pan = { x: event.clientX, y: event.clientY, left: canvas.x, top: canvas.y, moved: false }; board.classList.add('panning'); board.setPointerCapture(event.pointerId); });
  board.addEventListener('pointermove', event => { if (!pan) return; const dx = event.clientX - pan.x, dy = event.clientY - pan.y; pan.moved ||= Math.abs(dx) + Math.abs(dy) > 8; canvas.x = pan.left + dx; canvas.y = pan.top + dy; applyCanvas(); });
  board.addEventListener('pointerup', stopPan); board.addEventListener('pointercancel', stopPan);
  board.addEventListener('click', event => {
    if (event.target.closest('.frame,button,#minimap,.frame-bar') || lastPanMoved) return;
    remember();
    selectedImportEdgeId = undefined;
    exitFlow();
    pinned.clear();
    selectedId = rootFolder()?.id;
    rebuildTrace();
    render();
    updateInspector();
    syncToolbar();
  });
  board.addEventListener('wheel', event => {
    event.preventDefault();
    wheelRemainder += event.deltaY;
    if (Math.abs(wheelRemainder) < 3) return;
    const delta = Math.max(-180, Math.min(180, wheelRemainder));
    wheelRemainder = Math.abs(wheelRemainder) > 180 ? wheelRemainder - delta : 0;
    directManipulation();
    const rect = board.getBoundingClientRect(), cx = event.clientX - rect.left, cy = event.clientY - rect.top;
    const next = Math.min(1.55, Math.max(.34, canvas.scale * Math.exp(-delta * .00022)));
    const wx = (cx - canvas.x) / canvas.scale, wy = (cy - canvas.y) / canvas.scale;
    canvas.scale = next; canvas.x = cx - wx * next; canvas.y = cy - wy * next; applyCanvas();
  }, { passive: false });
  board.addEventListener('dblclick', event => { if (!event.target.closest('.card')) fitMap(); });
  window.addEventListener('keydown', event => {
    if (event.key !== 'Escape') return;
    if (expandedModules.size) { remember(); expandedModules.clear(); render(); }
    else if (sourceFiles.size) { remember(); sourceFiles.clear(); render(); }
    else if (expandedFiles.size) { remember(); expandedFiles.clear(); render(); }
    else if (expandedFolders.size) { remember(); expandedFolders.clear(); render(); }
    else if (flowMode) { remember(); exitFlow(); rebuildTrace(); render(); updateInspector(); }
    else if (scopeId !== rootFolder().id) { remember(); scopeId = node(scopeId)?.parentId || rootFolder().id; layoutAnchorFileId = entryFile(folder())?.id; render(); }
  });
}
minimap.addEventListener('pointerdown', event => { const rect = minimap.getBoundingClientRect(); const x = (event.clientX - rect.left) / rect.width * world.offsetWidth, y = (event.clientY - rect.top) / rect.height * world.offsetHeight; canvas.x = board.clientWidth / 2 - x * canvas.scale; canvas.y = board.clientHeight / 2 - y * canvas.scale; applyCanvas(); });
async function snapshotFiles(files) { sourceMode = 'snapshot'; if ($('#tracking-status')) $('#tracking-status').textContent = 'static browser snapshot'; const payload = await Promise.all(files.filter(file => file.size < 2_000_000).map(async file => ({ path: file.webkitRelativePath || file.name, source: await file.text() }))); const response = await fetch('/api/graph-files', { method: 'POST', headers: { 'content-type': 'application/json' }, body: JSON.stringify({ files: payload }) }); if (!response.ok) throw new Error(await response.text()); applyGraph(await response.json()); }
async function openWorkspace() { const input = $('#workspace-files'); if (!window.showDirectoryPicker) return input.click(); try { const handle = await window.showDirectoryPicker({ mode: 'read' }); const files = []; const walk = async (directory, prefix = '') => { for await (const [name, child] of directory.entries()) { if (['node_modules', '.git', 'dist', 'build'].includes(name)) continue; if (child.kind === 'directory') await walk(child, `${prefix}${name}/`); else files.push(Object.assign(await child.getFile(), { webkitRelativePath: `${prefix}${name}` })); } }; await walk(handle); await snapshotFiles(files); } catch (error) { if (error.name !== 'AbortError') console.error(error); } }
function mcpSnippet() {
  return JSON.stringify({
    mcpServers: {
      deepflow: {
        command: 'node',
        args: [`${location.origin}/mcp-server.js`.replace(location.origin, '<path-to-DeepFlow>/mcp-server.js')]
      }
    }
  }, null, 2) + '\n\nThen ask your agent to call deepflow_open_workspace with the absolute repo path before it starts editing, and deepflow_after_edit after file changes.';
}
function showOpenDialog() {
  const dialog = $('#open-dialog');
  $('#mcp-snippet').textContent = mcpSnippet();
  if (dialog?.showModal) dialog.showModal();
  else openWorkspace();
}
function initSettings() {
  const savedTheme = localStorage.getItem('deepflow-theme') || 'aurora';
  const knownThemes = new Set([...($('#theme-grid')?.querySelectorAll('[data-theme-choice]') || [])].map(button => button.dataset.themeChoice));
  const theme = knownThemes.has(savedTheme) ? savedTheme : 'aurora';
  if (theme !== savedTheme) localStorage.setItem('deepflow-theme', theme);
  const motion = localStorage.getItem('deepflow-motion') !== 'reduced';
  autoRevealChanges = localStorage.getItem('deepflow-auto-reveal') !== 'false';
  agentRevealDwellMs = Math.max(3000, Math.min(20000, Number(localStorage.getItem('deepflow-reveal-dwell') || 8000)));
  traceMode = localStorage.getItem('deepflow-live-trace') !== 'false';
  document.body.dataset.theme = theme;
  document.body.classList.toggle('reduce-motion', !motion);
  $('#motion-toggle').checked = motion;
  $('#auto-reveal-toggle').checked = autoRevealChanges;
  const dwell = $('#reveal-dwell');
  const dwellOut = $('#reveal-dwell-value');
  if (dwell) {
    dwell.value = String(Math.round(agentRevealDwellMs / 1000));
    if (dwellOut) dwellOut.textContent = `${dwell.value}s`;
  }
  const syncThemeButtons = () => $('#theme-grid')?.querySelectorAll('[data-theme-choice]').forEach(button => button.classList.toggle('active', button.dataset.themeChoice === document.body.dataset.theme));
  syncThemeButtons();
  $('#settings-open')?.addEventListener('click', () => $('#settings-dialog')?.showModal?.());
  $('#theme-grid')?.querySelectorAll('[data-theme-choice]').forEach(button => button.addEventListener('click', () => {
    document.body.dataset.theme = button.dataset.themeChoice;
    localStorage.setItem('deepflow-theme', button.dataset.themeChoice);
    syncThemeButtons();
    if (graph) render();
    else renderMinimap();
  }));
  $('#motion-toggle')?.addEventListener('change', event => {
    document.body.classList.toggle('reduce-motion', !event.target.checked);
    localStorage.setItem('deepflow-motion', event.target.checked ? 'full' : 'reduced');
  });
  $('#auto-reveal-toggle')?.addEventListener('change', event => {
    autoRevealChanges = event.target.checked;
    localStorage.setItem('deepflow-auto-reveal', String(autoRevealChanges));
  });
  $('#reveal-dwell')?.addEventListener('input', event => {
    agentRevealDwellMs = Number(event.target.value) * 1000;
    localStorage.setItem('deepflow-reveal-dwell', String(agentRevealDwellMs));
    if ($('#reveal-dwell-value')) $('#reveal-dwell-value').textContent = `${event.target.value}s`;
  });
}
function syncToolbar() {
  document.querySelectorAll('[data-toolbar-toggle]').forEach(button => {
    const key = button.dataset.toolbarToggle;
    button.classList.toggle('active', key === 'trace' ? traceMode : key === 'presentation' ? presentationMode : false);
  });
  document.querySelectorAll('[data-edge-toggle]').forEach(button => {
    const key = button.dataset.edgeToggle;
    button.classList.toggle('active', edgeVisibility[key] !== false);
  });
  app.classList.toggle('presentation-mode', presentationMode);
}
function markRecent(paths = []) {
  const now = Date.now();
  for (const path of paths) if (path) {
    const normalized = String(path).replaceAll('\\', '/');
    recentPaths.set(normalized, now);
    upsertActivity(normalized);
  }
  for (const [path, at] of recentPaths) if (now - at > 45_000) recentPaths.delete(path);
  renderActivityFeed();
  scheduleActivityFade();
}
function revealRecentChanges() {
  if (!autoRevealChanges || !recentPaths.size || !graph) return;
  const fresh = [...recentPaths.entries()]
    .filter(([, at]) => Date.now() - at < 12_000)
    .sort((a, b) => b[1] - a[1]);
  if (!fresh.length) return;
  playAgentEditReveal(fresh[0][0]);
}
function fileByPath(path) {
  return graph?.nodes.find(item => item.kind === 'file' && item.path === String(path || '').replaceAll('\\', '/'));
}
function folderByPath(path) {
  const normalized = String(path || '').replaceAll('\\', '/').replace(/\/$/, '');
  return graph?.nodes.find(item => item.kind === 'folder' && item.path === normalized);
}
function revealItem(item, { moduleName, line, pin = false, pulse = false, enterFlow = true } = {}) {
  if (!item || !graph) return;
  remember();
  const file = item.kind === 'file' ? item : item.kind === 'module' ? fileOf(item) : null;
  const folderTarget = item.kind === 'folder' ? item : null;
  const targetFile = file || (folderTarget ? entryFile(folderTarget) : null);
  expandAncestors(file || folderTarget || item);
  if (folderTarget) expandedFolders.add(folderTarget.id);
  let target = item;
  if (targetFile) {
    expandedFiles.add(targetFile.id);
    layoutAnchorFileId = targetFile.id;
    activateFocus(targetFile);
    const module = moduleName
      ? modules(targetFile).find(entry => entry.label === moduleName || `${entry.label}()` === moduleName)
      : line ? modules(targetFile).find(entry => line >= entry.loc.start && line <= entry.loc.end) : null;
    if (module) { expandedModules.add(module.id); target = module; }
  }
  selectedId = target.id;
  if (pin) pinned.add(target.id);
  if (enterFlow) flowMode = true;
  rebuildTrace(); render(); updateInspector(); syncToolbar();
  requestAnimationFrame(() => {
    keepSelectionVisible();
    if (pulse) pulseSelection();
    writeDeepLink();
  });
}
function pulseSelection() {
  const element = elementForSelection();
  if (!element) return;
  element.classList.add('pulse-hit');
  setTimeout(() => element.classList.remove('pulse-hit'), 1400);
}
function showTourCard(title, body) {
  const card = $('#tour-card');
  if (!card) return;
  $('#tour-title').textContent = title || 'DeepFlow tour';
  $('#tour-body').textContent = body || '';
  card.hidden = false;
  card.classList.add('visible');
  clearTimeout(showTourCard.timer);
  showTourCard.timer = setTimeout(() => { card.classList.remove('visible'); card.hidden = true; }, 5200);
}
async function playTour(steps = []) {
  for (let index = 0; index < steps.length; index++) {
    const step = steps[index];
    showTourCard(`${index + 1}/${steps.length} · ${step.title}`, step.narrative);
    handleViewerCommand({ ...step.command, type: step.command?.type });
    await new Promise(resolve => setTimeout(resolve, 2200));
  }
}
function handleViewerCommand(command = {}) {
  if (command.type === 'open-flow') {
    const file = fileByPath(command.path);
    if (!file) return;
    const target = command.module
      ? modules(file).find(module => module.label === command.module) || file
      : file;
    remember();
    expandAncestors(file);
    expandedFiles.add(file.id);
    openFlowOverlay(target, { narrative: command.narrative });
    writeDeepLink();
    return;
  }
  if (command.type === 'close-flow') {
    closeFlowOverlay();
    return;
  }
  if (command.type === 'clear-highlights') {
    remember(); closeFlowOverlay(); pinned.clear(); exitFlow(); recentPaths.clear(); rebuildTrace(); render(); updateInspector(); writeDeepLink(); return;
  }
  if (command.type === 'set-mode') {
    remember();
    if (command.mode === 'rails' || command.mode === 'outline') {
      exitFlow();
      ensureDefaultOutlineExpanded();
      rebuildTrace();
      render();
      updateInspector();
    } else if (command.mode === 'signal') {
      const item = selected() || entryItem();
      if (item) revealItem(fileOf(item) || item, { enterFlow: true, pulse: true });
    }
    writeDeepLink();
    return;
  }
  if (command.type === 'set-edges') {
    remember();
    Object.assign(edgeVisibility, command.edges || {});
    rebuildTrace(); render(); updateInspector(); syncToolbar();
    return;
  }
  if (command.type === 'show-orphans') {
    remember();
    const paths = command.paths?.length
      ? command.paths
      : graph.nodes.filter(n => n.kind === 'file' && n.orphan).map(n => n.path);
    pinned.clear();
    for (const path of paths.slice(0, 40)) {
      const item = fileByPath(path);
      if (!item) continue;
      pinned.add(item.id);
      expandAncestors(item);
      selectedId = item.id;
    }
    rebuildTrace(); render(); updateInspector(); syncToolbar();
    showTourCard('Orphans', `${paths.length} nodes with no static callers.`);
    if (command.pulse) requestAnimationFrame(pulseSelection);
    return;
  }
  if (command.type === 'tour-step') {
    showTourCard(command.title, command.narrative);
    if (command.command) handleViewerCommand(command.command);
    return;
  }
  if (command.type === 'tour-play') {
    playTour(command.steps || []).catch(console.error);
    return;
  }
  if (command.type === 'highlight-paths') {
    remember();
    for (const path of command.paths || []) {
      const item = fileByPath(path) || folderByPath(path);
      if (!item) continue;
      if (command.pin) pinned.add(item.id);
      expandAncestors(item);
      if (item.kind === 'folder') expandedFolders.add(item.id);
      if (item.kind === 'file') expandedFiles.add(item.id);
      selectedId = item.id;
      activateFocus(item);
    }
    rebuildTrace(); render(); updateInspector(); syncToolbar(); requestAnimationFrame(focusSelection); return;
  }
  if (command.type === 'jump') {
    const item = fileByPath(command.path) || folderByPath(command.path);
    revealItem(item, { moduleName: command.module, line: command.line, pin: command.pin, pulse: command.pulse !== false });
  }
}
function updateRepoStats() {
  const el = $('#repo-stats');
  if (!el || !graph) return;
  const s = graph.stats || {};
  el.textContent = `${s.files || 0} files · ${s.modules || 0} modules · ${s.orphaned || 0} orphans`;
}
function writeDeepLink() {
  if (!graph) return;
  const item = selected();
  const file = fileOf(item) || (item?.kind === 'folder' ? item : null);
  if (!file?.path) return;
  const params = new URLSearchParams();
  params.set('path', file.path);
  if (item?.kind === 'module') params.set('module', item.label);
  params.set('mode', traceActive() ? 'signal' : 'outline');
  history.replaceState(null, '', `#${params.toString()}`);
}
function applyDeepLink() {
  const hash = location.hash.replace(/^#/, '');
  if (!hash || !graph) return false;
  const params = new URLSearchParams(hash);
  const path = params.get('path');
  if (!path) return false;
  const item = fileByPath(path) || folderByPath(path);
  if (!item) return false;
  revealItem(item, {
    moduleName: params.get('module') || undefined,
    enterFlow: params.get('mode') !== 'outline' && params.get('mode') !== 'rails',
    pulse: true
  });
  return true;
}
function searchCandidates(query) {
  const q = String(query || '').trim().toLowerCase();
  if (!q || !graph) return [];
  return graph.nodes
    .filter(n => n.kind === 'file' || n.kind === 'module' || n.kind === 'folder')
    .map(n => {
      const hay = `${n.path || ''} ${n.label || ''}`.toLowerCase();
      if (!hay.includes(q)) return null;
      let score = 0;
      if ((n.label || '').toLowerCase() === q) score += 100;
      if ((n.path || '').toLowerCase().endsWith(q)) score += 80;
      if ((n.label || '').toLowerCase().startsWith(q)) score += 40;
      if (n.entrypoint) score += 12;
      if (n.orphan) score -= 4;
      return { node: n, score };
    })
    .filter(Boolean)
    .sort((a, b) => b.score - a.score || a.node.path.localeCompare(b.node.path))
    .slice(0, 18)
    .map(entry => entry.node);
}
function renderSearchResults(query) {
  const list = $('#search-results');
  if (!list) return;
  const matches = searchCandidates(query);
  list.innerHTML = matches.map((item, index) => `<button type="button" class="search-hit ${index === 0 ? 'active' : ''}" data-search-id="${item.id}">
    <b>${escape(item.kind === 'module' ? `${item.label}()` : item.label)}</b>
    <span>${escape(item.path || '/')}${item.entrypoint ? ' · entry' : ''}${item.orphan ? ' · orphan' : ''}</span>
  </button>`).join('') || '<p class="search-empty">No matches in this workspace.</p>';
  list.querySelectorAll('[data-search-id]').forEach(button => button.addEventListener('click', () => {
    const item = node(button.dataset.searchId);
    $('#search-dialog')?.close?.();
    revealItem(item, { pulse: true });
  }));
}
function openSearch() {
  const dialog = $('#search-dialog');
  const input = $('#search-input');
  if (!dialog?.showModal) return;
  input.value = '';
  renderSearchResults('');
  dialog.showModal();
  requestAnimationFrame(() => input.focus());
}
function initSearch() {
  $('#search-open')?.addEventListener('click', openSearch);
  const input = $('#search-input');
  input?.addEventListener('input', () => renderSearchResults(input.value));
  input?.addEventListener('keydown', event => {
    const hits = [...document.querySelectorAll('.search-hit')];
    const active = document.querySelector('.search-hit.active');
    const index = hits.indexOf(active);
    if (event.key === 'ArrowDown') {
      event.preventDefault();
      hits.forEach(hit => hit.classList.remove('active'));
      (hits[Math.min(hits.length - 1, index + 1)] || hits[0])?.classList.add('active');
    } else if (event.key === 'ArrowUp') {
      event.preventDefault();
      hits.forEach(hit => hit.classList.remove('active'));
      (hits[Math.max(0, index - 1)] || hits[0])?.classList.add('active');
    } else if (event.key === 'Enter') {
      event.preventDefault();
      active?.click();
    }
  });
  window.addEventListener('keydown', event => {
    if ((event.metaKey || event.ctrlKey) && event.key.toLowerCase() === 'k') {
      event.preventDefault();
      openSearch();
    }
  });
}
function applyGraph(next, { preserve = false } = {}) {
  const previousSelected = selectedId, previousScope = scopeId, previousAnchor = layoutAnchorFileId; graph = next;
  if (!preserve) { offsets.clear(); localOffsets.clear(); layoutModes.clear(); pinnedLayout.clear(); basePlacements.clear(); layoutMemory.clear(); basePlacementKey = ''; exitFlow(); expandedFiles.clear(); expandedFolders.clear(); expandedModules.clear(); sourceFiles.clear(); pinned.clear(); recentPaths.clear(); activityItems.clear(); archivedActivity.length = 0; undoStack.length = 0; redoStack.length = 0; }
  scopeId = preserve && node(previousScope)?.kind === 'folder' ? previousScope : rootFolder().id;
  selectedId = preserve && node(previousSelected) ? previousSelected : rootFolder().id;
  layoutAnchorFileId = preserve && node(previousAnchor)?.kind === 'file' ? previousAnchor : fileOf(node(selectedId))?.id || entryFile(folder())?.id;
  if (!preserve) ensureDefaultOutlineExpanded();
  if (preserve) requestAnimationFrame(() => revealRecentChanges());
  $('#repo-name').textContent = graph.roots.map(root => root.label).join(' + ');
  updateRepoStats();
  rebuildTrace(); render(); updateInspector(); updateHistory(); renderActivityFeed(); syncToolbar();
  if (!preserve) {
    requestAnimationFrame(() => {
      fitMap();
      if (!applyDeepLink()) writeDeepLink();
    });
  }
}
async function loadGraph({ preserve = false } = {}) { const response = await fetch('/api/graph', { method: 'POST', headers: { 'content-type': 'application/json' }, body: JSON.stringify({}) }); if (!response.ok) throw new Error(await response.text()); sourceMode = 'live'; if ($('#tracking-status')) $('#tracking-status').textContent = 'live local map'; applyGraph(await response.json(), { preserve }); }
initSettings();
initSearch();
initFlowOverlay();
$('#history-back').addEventListener('click', () => moveHistory(true)); $('#history-forward').addEventListener('click', () => moveHistory(false)); $('#reset-view').addEventListener('click', resetPresentation); $('#open-workspace').addEventListener('click', showOpenDialog); $('#choose-folder').addEventListener('click', openWorkspace); $('#copy-mcp').addEventListener('click', async () => { await navigator.clipboard?.writeText($('#mcp-snippet').textContent); $('#copy-mcp').textContent = 'Copied'; setTimeout(() => $('#copy-mcp').textContent = 'Copy MCP setup', 1200); }); $('#workspace-files').addEventListener('change', event => { if (event.target.files.length) snapshotFiles([...event.target.files]); event.target.value = ''; }); $('#inspector-toggle').addEventListener('click', () => app.classList.toggle('inspector-closed'));
$('#focus-selection')?.addEventListener('click', focusSelection);
window.addEventListener('hashchange', () => applyDeepLink());
document.querySelectorAll('[data-toolbar-toggle]').forEach(button => button.addEventListener('click', () => {
  remember();
  if (button.dataset.toolbarToggle === 'trace') {
    traceMode = !traceMode;
    localStorage.setItem('deepflow-live-trace', String(traceMode));
  }
  if (button.dataset.toolbarToggle === 'presentation') presentationMode = !presentationMode;
  rebuildTrace(); render(); updateInspector(); syncToolbar();
}));
document.querySelectorAll('[data-edge-toggle]').forEach(button => button.addEventListener('click', () => {
  remember();
  const key = button.dataset.edgeToggle;
  edgeVisibility[key] = edgeVisibility[key] === false;
  if (key === 'imports') edgeVisibility.reexports = edgeVisibility.references = edgeVisibility.imports;
  rebuildTrace(); render(); updateInspector(); syncToolbar();
}));
syncToolbar();
canvasControls(); updateHistory();
const changes = new EventSource('/api/changes');
changes.addEventListener('workspace-change', event => {
  try { markRecent(JSON.parse(event.data || '{}').paths || []); } catch {}
  if (sourceMode === 'live') loadGraph({ preserve: true }).catch(console.error);
});
changes.addEventListener('viewer-command', event => {
  try { handleViewerCommand(JSON.parse(event.data || '{}')); } catch (error) { console.error(error); }
});
window.addEventListener('resize', () => { if (graph) render(); });
loadGraph().catch(console.error);
