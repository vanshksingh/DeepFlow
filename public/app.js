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
let editAnimStyle = 'spark'; // pulse | ripple | flash | scan | fire | spark | hearts | lines
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
const nestedSeats = new Map(); // nested id -> absolute {x,y} in parent canvas (drop seat)
const userArranged = new Set(); // nested ids the user dragged - only these keep locals across reflow
const pinnedLayout = new Set(); // user-dragged frames skip shelf clustering (view-field gravity still applies)
const traceArranged = new Set(); // focus-rearranged islands — prefer keeping their seats
let gravityTimer = 0;
let traceAlignToken = 0;
let traceAlignRaf = 0;
let traceAlignTimer = 0;
let skipFlipOnce = false;
let flipBefore = null;
let clickAnchor = null; // expand under pointer - never camera-center on open
let forceFreshPack = false;
/** While set, pack/separate keeps these frames fixed so expand pushes siblings away. */
let layoutAnchorIds = new Set();
/** Sticky expand target — survives until morph end so idle packs keep the grown chip fixed. */
let stickyExpandId = null;
/** After minimize: hold island seats so relax/constellation cannot suck small folders to the center. */
let seatLock = new Set();
/** True while stickyExpandId is a collapse (not an open). */
let collapseMotion = false;
/** Focus/trace align owns motion - skip pack snap, FLIP, and soft-settle fights. */
let alignMotionPending = false;
let softSettleToken = 0;
let softSettleRunning = 0;
/** Pending constellation after expand morph completes. */
let pendingAlignAfterMorph = 0;
/** Trail of nodes visited inside the three-plane flow overlay. */
let flowTrail = [];
let flowTrailIndex = -1;
let flowNavCache = { upstream: [], downstream: [] };

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
// Distinct folder hues - translucent glass groups share a tint with their files.
const FOLDER_COLORS = [
  '#0d8a72', '#3b6fb8', '#b05a28', '#8f3f72', '#218ea0',
  '#6f8230', '#5a48a8', '#b4474a', '#1f7a62', '#9a6b18',
  '#3f6e8c', '#7a4570', '#177a7a', '#8a5634', '#4658a0',
  '#2d7a48', '#a05538', '#4a5f78'
];
const THEME_FOLDER_COLORS = {
  bubblegum: ['#ff6bb5', '#7c5cff', '#ff9f43', '#35c4c4', '#ff5c8a', '#b388ff', '#ff8fab', '#5ad1e6', '#ff7eb6', '#a78bfa', '#fb923c', '#22d3ee'],
  volcano: ['#d9480f', '#e67700', '#c92a2a', '#f59f00', '#e03131', '#f76707', '#fab005', '#c2255c', '#e8590c', '#f08c00', '#ae3ec9', '#ff922b'],
  hacker: ['#33ff66', '#00d4aa', '#7cff4a', '#00ffa3', '#39ff14', '#b8ff3c', '#1aff9c', '#66ff99', '#00cc88', '#88ff44', '#22eeaa', '#aaff00'],
  ocean: ['#0e7c86', '#0b6e99', '#14919b', '#2a9d8f', '#3a86ff', '#0077b6', '#00b4d8', '#48cae4', '#023e8a', '#0096c7', '#90e0ef', '#f0a202'],
  sunset: ['#e76f51', '#f4a261', '#e9c46a', '#f28482', '#ff6b6b', '#ffa94d', '#ffd43b', '#ff8787', '#d9480f', '#fd7e14', '#fab005', '#e64980'],
  lavender: ['#7c5cbf', '#5c7cfa', '#e599f7', '#9775fa', '#845ef7', '#748ffc', '#da77f2', '#7048e8', '#5f3dc4', '#4c6ef5', '#cc5de8', '#7950f2'],
  noir: ['#f5f5f5', '#c8c8c8', '#9a9a9a', '#e8e8e8', '#b0b0b0', '#dcdcdc', '#888888', '#fafafa', '#aaaaaa', '#dddddd', '#777777', '#eeeeee'],
  ember: ['#ff9f1c', '#ff6b35', '#d9381e', '#f7c59f', '#f4a261', '#e76f51', '#e9c46a', '#f28482', '#ffb703', '#fb8500', '#eb5e28', '#c1121f'],
  github: ['#238636', '#58a6ff', '#8957e5', '#d29922', '#2ea043', '#3fb950', '#a371f7', '#bc8cff', '#1f6feb', '#388bfd', '#d29922', '#e3b341'],
  solarized: ['#859900', '#2aa198', '#268bd2', '#b58900', '#cb4b16', '#dc322f', '#d33682', '#6c71c4', '#586e75', '#657b83', '#93a1a1', '#839496']
};
function themeFolderColors() {
  return THEME_FOLDER_COLORS[document.body.dataset.theme] || FOLDER_COLORS;
}
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
const color = value => {
  const palette = themeFolderColors();
  return palette[hashHue(value) % palette.length];
};
function folderTint(item) {
  const palette = themeFolderColors();
  if (item?.id === SYNTHETIC_ROOT_ID || item?.synthetic) return palette[palette.length - 1] || '#4a5f78';
  const region = mapRegion(item);
  const regionBias = { application: 0, package: 6, service: 1, infrastructure: 9, docs: 5, test: 3, generated: 5, context: 10 };
  const salt = hashHue(item.path || item.label);
  return palette[((regionBias[region] ?? 0) + salt) % palette.length];
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
// Selection or pins drive committed flow. Hover never counts (preview wires only).
function traceActive() {
  const item = selected();
  return !!(item && (item.kind === 'file' || item.kind === 'module' || item.kind === 'folder')) || pinned.size > 0 || !!hoverId;
}
/** True only for click/pin focus — never for hover preview. */
function hasCommittedTraceFocus() {
  if (pinned.size) return true;
  const item = selected();
  return !!(item && (item.kind === 'file' || item.kind === 'module' || item.kind === 'folder'));
}
function exitFlow() {
  flowMode = false;
  focusOrigin = null;
  focusedFileId = null;
}
function outlineDim() {
  // Keep every frame fully readable - highlight via wires/hot, never fade modules out.
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
  // Hide loose files at display-root - they live inside the synthetic "root" island.
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
  return {
    scopeId, selectedId, selectedImportEdgeId, layoutAnchorFileId, flowMode, focusedFileId, traceMode, presentationMode,
    expanded: [...expandedFiles], expandedFolders: [...expandedFolders], expandedModules: [...expandedModules],
    source: [...sourceFiles], pinned: [...pinned],
    offsets: [...offsets.entries()].map(([id, value]) => [id, { ...value }]),
    localOffsets: [...localOffsets.entries()].map(([id, value]) => [id, { ...value }]),
    nestedSeats: [...nestedSeats.entries()].map(([id, value]) => [id, { ...value }]),
    userArranged: [...userArranged],
    pinnedLayout: [...pinnedLayout],
    traceArranged: [...traceArranged],
    canvas: { ...canvas }, edgeVisibility: { ...edgeVisibility }
  };
}
function updateHistory() { $('#history-back').disabled = !undoStack.length; $('#history-forward').disabled = !redoStack.length; }
function remember() { if (!graph) return; undoStack.push(snapshot()); if (undoStack.length > 70) undoStack.shift(); redoStack.length = 0; updateHistory(); }
function restore(state) {
  scopeId = state.scopeId; selectedId = state.selectedId; selectedImportEdgeId = state.selectedImportEdgeId; layoutAnchorFileId = state.layoutAnchorFileId; flowMode = state.flowMode; focusedFileId = state.focusedFileId || null; focusOrigin = null; traceMode = state.traceMode ?? true; presentationMode = !!state.presentationMode;
  Object.assign(edgeVisibility, state.edgeVisibility || {});
  expandedFiles.clear(); state.expanded.forEach(id => expandedFiles.add(id)); expandedFolders.clear(); (state.expandedFolders || []).forEach(id => expandedFolders.add(id)); expandedModules.clear(); (state.expandedModules || []).forEach(id => expandedModules.add(id)); sourceFiles.clear(); state.source.forEach(id => sourceFiles.add(id)); pinned.clear(); state.pinned.forEach(id => pinned.add(id));
  offsets.clear(); (state.offsets || []).forEach(([id, value]) => offsets.set(id, value));
  userArranged.clear();
  (state.userArranged || []).forEach(id => userArranged.add(id));
  localOffsets.clear(); (state.localOffsets || []).forEach(([id, value]) => {
    localOffsets.set(id, value);
    userArranged.add(id);
  });
  nestedSeats.clear();
  (state.nestedSeats || []).forEach(([id, value]) => nestedSeats.set(id, { ...value }));
  if (!state.nestedSeats) {
    for (const [id, value] of localOffsets) nestedSeats.set(id, { x: value.x, y: value.y });
  }
  pinnedLayout.clear(); (state.pinnedLayout || []).forEach(id => pinnedLayout.add(id));
  traceArranged.clear(); (state.traceArranged || []).forEach(id => traceArranged.add(id));
  Object.assign(canvas, state.canvas);
  rebuildTrace(); render(); updateInspector(); syncToolbar();
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
  // Demo layout is intentional and fixed - no soft-snap interpolation.
  return target;
}
function requestLayoutSettle(item) {
  if (item) activateFocus(item);
  basePlacements.clear();
  basePlacementKey = '';
}
function expandAncestors(item) {
  if (!item) return;
  // Open the full ancestor chain so deep files (and their modules) stay visible.
  for (const parent of ancestors(item).filter(entry => entry.kind === 'folder')) expandedFolders.add(parent.id);
  const root = displayRootRaw();
  if (item.kind === 'file' && item.parentId === root?.id) expandedFolders.add(SYNTHETIC_ROOT_ID);
  // Keep root + top-level shelves open; never collapse deep folders we just revealed.
  ensureTopLevelFoldersOpen();
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
/** Folders that cannot collapse — hide the minimize/expand chevron entirely. */
function folderCanMinimize(item) {
  if (!item || item.kind !== 'folder') return false;
  const root = displayRoot();
  if (!root) return false;
  if (item.id === root.id || item.id === SYNTHETIC_ROOT_ID || item.synthetic) return false;
  // Level-1 shelves stay open (same guard as toggleFolder).
  if (folderDepthFrom(root, item) <= 1) return false;
  return true;
}
/** Keep the display root and its immediate folder shelves open. No depth ceiling. */
function ensureTopLevelFoldersOpen() {
  const root = displayRoot();
  if (!root) return;
  expandedFolders.add(root.id);
  if (syntheticRootFiles.length) expandedFolders.add(SYNTHETIC_ROOT_ID);
  for (const child of topLevelItems(root)) {
    if (child.kind === 'folder') expandedFolders.add(child.id);
  }
}
/** @deprecated Use ensureTopLevelFoldersOpen — kept as alias for older call sites. */
function pruneFolderDepth(_maxDepth = null) {
  ensureTopLevelFoldersOpen();
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
    expandedFolders.add(id);
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
  // Clear in-flight FLIP transforms so we don't sample mid-animation positions.
  scene.querySelectorAll('.frame.float.flipping, .frame.float.size-morph').forEach(el => {
    el.classList.remove('flipping', 'size-morph');
    el.style.transform = '';
  });
  const map = new Map();
  scene.querySelectorAll('.frame.float[data-drag-id]').forEach(el => {
    const rect = el.getBoundingClientRect();
    const canvas = el.querySelector(':scope > .frame-canvas');
    map.set(el.dataset.dragId, {
      left: rect.left,
      top: rect.top,
      width: rect.width,
      height: rect.height,
      canvasH: canvas ? canvas.offsetHeight : 0
    });
  });
  return map;
}
function playFlip(before) {
  if (skipFlipOnce) {
    skipFlipOnce = false;
    finishExpandMorph();
    return;
  }
  if (!before?.size || document.body.classList.contains('reduce-motion')) {
    finishExpandMorph();
    return;
  }
  const scale = Math.max(0.01, canvas?.scale || 1);
  let flipping = 0;
  const finished = new Set();
  const onFlipDone = (id) => {
    if (finished.has(id)) return;
    finished.add(id);
    flipping -= 1;
    if (flipping <= 0) finishExpandMorph();
  };
  scene.querySelectorAll('.frame.float[data-drag-id]').forEach((el, index) => {
    const id = el.dataset.dragId;
    const nested = el.classList.contains('frame-fn') || el.parentElement?.classList.contains('frame-canvas');
    el.style.setProperty('--float-delay', String((hashHue(id) % 1200)));
    el.style.setProperty('--inertia', String(index % 7));
    const prev = before.get(id);
    if (!prev) {
      el.classList.add(nested ? 'nest-arrive' : 'calm-in');
      return;
    }
    const layout = frameLayoutSize(el);
    const nextW = layout.w || el.offsetWidth;
    const nextH = layout.h || el.offsetHeight;
    const prevW = prev.width / scale;
    const prevH = prev.height / scale;
    const resized = Math.abs(prevW - nextW) >= 1 || Math.abs(prevH - nextH) >= 1;

    // Nested chips: size-morph only — never screen-space position FLIP under a
    // morphing parent (that double-counted parent motion and glitched to top).
    if (nested) {
      if (!resized) return;
      const canvasEl = el.querySelector(':scope > .frame-canvas');
      const nextCanvasH = canvasEl ? canvasEl.offsetHeight : 0;
      el.style.transition = 'none';
      el.style.animation = 'none';
      el.classList.remove('flipping', 'size-morph', 'jelly-wobble');
      el.style.width = `${prevW}px`;
      el.style.height = `${prevH}px`;
      if (canvasEl && prev.canvasH > 0) canvasEl.style.height = `${prev.canvasH}px`;
      void el.offsetWidth;
      el.classList.add('flipping', 'size-morph');
      el.style.transition = '';
      el.style.animation = '';
      flipping += 1;
      requestAnimationFrame(() => {
        el.style.width = `${nextW}px`;
        el.style.height = `${nextH}px`;
        if (canvasEl) canvasEl.style.height = nextCanvasH ? `${nextCanvasH}px` : '';
        const pending = new Set(['width', 'height']);
        const done = (event) => {
          if (event?.propertyName) {
            pending.delete(event.propertyName);
            if (pending.size) return;
          }
          el.classList.remove('flipping', 'size-morph');
          commitFrameLayoutSize(el, canvasEl);
          el.removeEventListener('transitionend', done);
          onFlipDone(id);
        };
        el.addEventListener('transitionend', done);
        setTimeout(() => done(), 1100);
      });
      return;
    }

    const next = el.getBoundingClientRect();
    const dx = prev.left - next.left;
    const dy = prev.top - next.top;
    const moved = Math.abs(dx) >= 0.5 || Math.abs(dy) >= 0.5;
    if (!moved && !resized) return;
    const canvasEl = el.querySelector(':scope > .frame-canvas');
    const nextCanvasH = canvasEl ? canvasEl.offsetHeight : 0;

    el.style.transition = 'none';
    el.style.animation = 'none';
    el.classList.remove('flipping', 'size-morph', 'jelly-wobble');
    if (resized) {
      el.style.width = `${prevW}px`;
      el.style.height = `${prevH}px`;
      if (canvasEl && prev.canvasH > 0) canvasEl.style.height = `${prev.canvasH}px`;
    }
    if (moved) el.style.transform = `translate(${dx}px, ${dy}px)`;
    void el.offsetWidth;

    el.classList.add('flipping');
    if (resized) el.classList.add('size-morph');
    el.style.transition = '';
    el.style.animation = '';
    flipping += 1;

    requestAnimationFrame(() => {
      if (resized) {
        el.style.width = `${nextW}px`;
        el.style.height = `${nextH}px`;
        if (canvasEl) canvasEl.style.height = nextCanvasH ? `${nextCanvasH}px` : '';
      }
      el.style.transform = '';
      const pending = new Set();
      if (moved) pending.add('transform');
      if (resized) { pending.add('width'); pending.add('height'); }
      const done = (event) => {
        if (event?.propertyName) {
          pending.delete(event.propertyName);
          if (pending.size) return;
        }
        el.classList.remove('flipping', 'size-morph');
        el.style.transform = '';
        if (resized) commitFrameLayoutSize(el, canvasEl);
        el.removeEventListener('transitionend', done);
        onFlipDone(id);
      };
      el.addEventListener('transitionend', done);
      setTimeout(() => done(), 1300);
    });
  });
  if (flipping <= 0) finishExpandMorph();
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
const ISLAND_GAP = 80; // breathing room between top-level islands — never touch
const MODULE_GAP = 24; // air between fn modules inside a file
const NESTED_GAP = 40; // padding between sibling folders/files inside a parent
const NEST_PAD = 32; // inner canvas padding — keep counts/chips off the rim
const NEST_SNAP = 16; // soft edge-align threshold for in-folder cleanup
/**
 * Push free boxes away from fixed walls (and each other) until `gap` clears.
 * Used to reserve constellation landing seats before flight.
 */
function yieldBoxesFromWalls(movers, walls, { gap = ISLAND_GAP, passes = 48, pad = 0 } = {}) {
  if (!movers?.length) return;
  const yieldAway = (mover, wall, penX, penY) => {
    if (penX < penY) {
      const moverCx = mover.x + mover.w / 2;
      const wallCx = wall.x + wall.w / 2;
      mover.x += moverCx >= wallCx ? (penX + 0.5) : -(penX + 0.5);
    } else {
      const moverCy = mover.y + mover.h / 2;
      const wallCy = wall.y + wall.h / 2;
      mover.y += moverCy >= wallCy ? (penY + 0.5) : -(penY + 0.5);
    }
  };
  for (let pass = 0; pass < passes; pass++) {
    let hit = false;
    for (const m of movers) {
      for (const wall of walls) {
        if (wall.id && wall.id === m.id) continue;
        const ox = Math.min(m.x + m.w, wall.x + wall.w) - Math.max(m.x, wall.x);
        const oy = Math.min(m.y + m.h, wall.y + wall.h) - Math.max(m.y, wall.y);
        if (ox <= -gap || oy <= -gap) continue;
        yieldAway(m, wall, ox + gap, oy + gap);
        hit = true;
      }
    }
    for (let i = 0; i < movers.length; i++) {
      for (let j = i + 1; j < movers.length; j++) {
        const A = movers[i], B = movers[j];
        const ox = Math.min(A.x + A.w, B.x + B.w) - Math.max(A.x, B.x);
        const oy = Math.min(A.y + A.h, B.y + B.h) - Math.max(A.y, B.y);
        if (ox <= -gap || oy <= -gap) continue;
        const penX = ox + gap, penY = oy + gap;
        if (penX < penY) {
          const push = penX / 2 + 0.5;
          if (A.x <= B.x) { A.x -= push; B.x += push; } else { A.x += push; B.x -= push; }
        } else {
          const push = penY / 2 + 0.5;
          if (A.y <= B.y) { A.y -= push; B.y += push; } else { A.y += push; B.y -= push; }
        }
        hit = true;
      }
    }
    for (const m of movers) {
      m.x = Math.max(pad, m.x);
      m.y = Math.max(pad, m.y);
    }
    if (!hit) break;
  }
}
function topLevelIslandElements() {
  return [...scene.querySelectorAll('.frame-artboard > .frame.float[data-drag-id]')];
}
/** Top-level folder under pointer - only case where a drag may overlap another island. */
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
/** Park this far outside the visible board - strays stop here, never enter the field. */
const VIEW_PARK_PAD = 40;
/** Only islands farther than this from the board edge get pulled. */
const VIEW_FAR_PAD = 200;
function viewFieldBounds() {
  const boardRect = board.getBoundingClientRect();
  return {
    left: boardRect.left,
    top: boardRect.top,
    right: boardRect.right,
    bottom: boardRect.bottom
  };
}
function viewParkRim() {
  const field = viewFieldBounds();
  return {
    left: field.left - VIEW_PARK_PAD,
    top: field.top - VIEW_PARK_PAD,
    right: field.right + VIEW_PARK_PAD,
    bottom: field.bottom + VIEW_PARK_PAD
  };
}
/** True when fully outside the far band - only these migrate to the park rim. */
function islandFarFromView(rect) {
  const field = viewFieldBounds();
  return rect.right < field.left - VIEW_FAR_PAD
    || rect.left > field.right + VIEW_FAR_PAD
    || rect.bottom < field.top - VIEW_FAR_PAD
    || rect.top > field.bottom + VIEW_FAR_PAD;
}
/** True when any part of the island intersects the board viewfinder. */
function islandInView(rect) {
  const field = viewFieldBounds();
  return rect.right > field.left
    && rect.left < field.right
    && rect.bottom > field.top
    && rect.top < field.bottom;
}
/** Pull so the island's near edge sits just outside the view (park rim). */
function pullTowardViewField(rect) {
  const rim = viewParkRim();
  let pullX = 0, pullY = 0;
  if (rect.right < rim.left) pullX = rim.left - rect.right;
  else if (rect.left > rim.right) pullX = rim.right - rect.left;
  if (rect.bottom < rim.top) pullY = rim.top - rect.bottom;
  else if (rect.top > rim.bottom) pullY = rim.bottom - rect.top;
  return { pullX, pullY };
}
function clampGravityStep(pullScreen, scale, speed, maxStep) {
  const target = pullScreen / scale;
  if (!target) return 0;
  const raw = target * speed;
  const capped = Math.sign(raw) * Math.min(Math.abs(raw), maxStep, Math.abs(target));
  return capped;
}
function rectsOverlap(a, b, gap = ISLAND_GAP) {
  // Collide when rects are closer than `gap` (not when they already overlap by gap).
  const overlapX = Math.min(a.right, b.right) - Math.max(a.left, b.left);
  const overlapY = Math.min(a.bottom, b.bottom) - Math.max(a.top, b.top);
  return overlapX > -gap && overlapY > -gap;
}
function separationPush(moving, fixed, gap = ISLAND_GAP) {
  const overlapX = Math.min(moving.right, fixed.right) - Math.max(moving.left, fixed.left);
  const overlapY = Math.min(moving.bottom, fixed.bottom) - Math.max(moving.top, fixed.top);
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
  const gapPx = ISLAND_GAP * scale;
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
      if (!rectsOverlap(myRect, oRect, gapPx)) continue;
      const { dx: fixX, dy: fixY } = separationPush(myRect, oRect, gapPx);
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
/** After a free drop, animate other islands aside so the dropped one keeps its place. */
function cancelSoftSettle() {
  softSettleToken += 1;
}
/**
 * Ease residual overlaps among constellation seats only (keep `anchorId` fixed).
 * Never shuffles unrelated islands — that read as random snapping on focus.
 */
function softHealIslandGaps(anchorId, { duration = 520, packIds = null } = {}) {
  if (!anchorId || !scene) return Promise.resolve();
  const allow = packIds instanceof Set && packIds.size ? packIds : null;
  const boxes = [];
  for (const el of topLevelIslandElements()) {
    const id = el.dataset.dragId;
    if (!id) continue;
    if (allow && !allow.has(id)) continue;
    if (pinnedLayout.has(id) && id !== anchorId) continue;
    const shelf = islandShelfBox(el, id);
    boxes.push({
      id,
      el,
      left: shelf.left,
      top: shelf.top,
      x: shelf.x,
      y: shelf.y,
      w: shelf.w,
      h: shelf.h,
      from: { ...(offsets.get(id) || { x: 0, y: 0 }) }
    });
  }
  if (boxes.length < 2) return Promise.resolve();
  separateBoxes(boxes, { gap: ISLAND_GAP, passes: 48, anchors: new Set([anchorId]), pad: 0 });
  const movers = [];
  for (const box of boxes) {
    if (box.id === anchorId) continue;
    const to = { x: box.x - box.left, y: box.y - box.top };
    if (Math.abs(to.x - box.from.x) < 1 && Math.abs(to.y - box.from.y) < 1) continue;
    movers.push({ id: box.id, el: box.el, from: box.from, to });
  }
  if (!movers.length) return Promise.resolve();
  const token = ++softSettleToken;
  const start = performance.now();
  softSettleRunning += 1;
  return new Promise(resolve => {
    const done = () => {
      softSettleRunning = Math.max(0, softSettleRunning - 1);
      for (const m of movers) bakeIslandOffset(m.id, m.el);
      resolve();
    };
    if (duration <= 0 || document.body.classList.contains('reduce-motion')) {
      for (const m of movers) {
        offsets.set(m.id, { ...m.to });
        m.el.style.translate = `${m.to.x}px ${m.to.y}px`;
        m.el.style.setProperty('--ox', `${m.to.x}px`);
        m.el.style.setProperty('--oy', `${m.to.y}px`);
      }
      done();
      return;
    }
    const tick = now => {
      if (token !== softSettleToken) {
        softSettleRunning = Math.max(0, softSettleRunning - 1);
        resolve();
        return;
      }
      const t = Math.min(1, (now - start) / duration);
      const ease = 1 - Math.pow(1 - t, 4);
      for (const m of movers) {
        const x = m.from.x + (m.to.x - m.from.x) * ease;
        const y = m.from.y + (m.to.y - m.from.y) * ease;
        offsets.set(m.id, { x, y });
        m.el.style.translate = `${x}px ${y}px`;
        m.el.style.setProperty('--ox', `${x}px`);
        m.el.style.setProperty('--oy', `${y}px`);
      }
      if (t < 1) requestAnimationFrame(tick);
      else done();
    };
    requestAnimationFrame(tick);
  });
}
/** Screen-space rect for an island using final layout size (not mid-FLIP geometry). */
function islandSettleRect(islandId, islandEl) {
  const place = floatPlacements.get(islandId);
  const scale = Math.max(.35, canvas.scale || 1);
  const worldRect = world.getBoundingClientRect();
  const off = offsets.get(islandId) || { x: 0, y: 0 };
  const left = parseFloat(islandEl.style.left) || 0;
  const top = parseFloat(islandEl.style.top) || 0;
  const w = place?.w || parseFloat(islandEl.style.width) || islandEl.offsetWidth || 0;
  const h = place?.h || parseFloat(islandEl.style.height) || islandEl.offsetHeight || 0;
  if (place || (w && h && islandEl.parentElement?.classList.contains('frame-artboard'))) {
    const x = (place?.x ?? left) + off.x;
    const y = (place?.y ?? top) + off.y;
    return {
      left: worldRect.left + x * scale,
      top: worldRect.top + y * scale,
      right: worldRect.left + (x + w) * scale,
      bottom: worldRect.top + (y + h) * scale,
      width: w * scale,
      height: h * scale
    };
  }
  return islandEl.getBoundingClientRect();
}
function softSettleNeighbors(islandId, islandEl, {
  duration = 780,
  protectIds = null,
  againstBoxes = null,
  plannedMoves = null,
  /** When true (focus constellation): only move islands that block a landing seat. */
  blockersOnly = false
} = {}) {
  if (!islandEl) return Promise.resolve();
  const token = ++softSettleToken;
  const scale = Math.max(.35, canvas.scale || 1);
  // Overlap tests use screen-space rects — gap must scale with zoom or
  // islands look like they touch when zoomed in.
  const gapPx = ISLAND_GAP * scale;
  const start = performance.now();
  const protectedIds = new Set(protectIds || []);
  protectedIds.add(islandId);
  const planned = new Map((plannedMoves || []).map(m => [m.id, m]));
  const shelfOverlap = (a, b, gap) => {
    const ox = Math.min(a.x + a.w, b.x + b.w) - Math.max(a.x, b.x);
    const oy = Math.min(a.y + a.h, b.y + b.h) - Math.max(a.y, b.y);
    return ox > -gap && oy > -gap;
  };
  const movers = [];
  for (const other of topLevelIslandElements()) {
    const otherId = other.dataset.dragId;
    if (!otherId || protectedIds.has(otherId)) continue;
    // Focused parent stays put — blockers yield.
    if (isLockedFocusIsland(otherId)) continue;
    if (pinnedLayout.has(otherId)) continue;
    const cur = offsets.get(otherId) || { x: 0, y: 0 };
    const preset = planned.get(otherId);
    if (blockersOnly) {
      // Unrelated islands stay put unless they sit on a reserved landing seat
      // (or were explicitly planned as clearers).
      if (!preset && againstBoxes?.length) {
        const place = floatPlacements.get(otherId);
        const left = parseFloat(other.style.left) || 0;
        const top = parseFloat(other.style.top) || 0;
        const w = place?.w || parseFloat(other.style.width) || other.offsetWidth || 220;
        const h = place?.h || parseFloat(other.style.height) || other.offsetHeight || 54;
        const box = {
          x: (place?.x ?? left) + cur.x,
          y: (place?.y ?? top) + cur.y,
          w, h
        };
        const blocks = againstBoxes.some(wall => shelfOverlap(box, wall, ISLAND_GAP));
        if (!blocks) continue;
      } else if (!preset && !againstBoxes?.length) {
        continue;
      }
    }
    movers.push({
      id: otherId,
      el: other,
      from: { ...cur },
      to: preset ? { x: preset.ox, y: preset.oy } : { ...cur },
      planned: !!preset
    });
  }
  const shelfRect = (box, ox = 0, oy = 0) => {
    const worldRect = world.getBoundingClientRect();
    const x = box.x + ox;
    const y = box.y + oy;
    return {
      left: worldRect.left + x * scale,
      top: worldRect.top + y * scale,
      right: worldRect.left + (x + box.w) * scale,
      bottom: worldRect.top + (y + box.h) * scale,
      width: box.w * scale,
      height: box.h * scale
    };
  };
  const resolveTargets = () => {
    const anchors = [];
    // Focus drop settle uses the live focus rect. Constellation blockers-only
    // settles against reserved landing seats only — not "everything near focus".
    if (!blockersOnly || !againstBoxes?.length) {
      anchors.push(islandSettleRect(islandId, islandEl));
    }
    if (againstBoxes?.length) {
      for (const box of againstBoxes) anchors.push(shelfRect(box));
    }
    for (const m of movers) {
      if (!m.planned) m.to = { ...(offsets.get(m.id) || m.from) };
    }
    for (let pass = 0; pass < 28; pass++) {
      let hit = false;
      for (const m of movers) {
        const place = floatPlacements.get(m.id);
        let oRect = place
          ? shelfRect({ x: place.x, y: place.y, w: place.w, h: place.h }, m.to.x, m.to.y)
          : (m.el.style.translate = `${m.to.x}px ${m.to.y}px`, m.el.getBoundingClientRect());
        for (const wall of anchors) {
          if (!rectsOverlap(wall, oRect, gapPx)) continue;
          const { dx, dy } = separationPush(oRect, wall, gapPx);
          if (!dx && !dy) continue;
          m.to.x += dx / scale;
          m.to.y += dy / scale;
          oRect = place
            ? shelfRect({ x: place.x, y: place.y, w: place.w, h: place.h }, m.to.x, m.to.y)
            : (() => {
              m.el.style.translate = `${m.to.x}px ${m.to.y}px`;
              return m.el.getBoundingClientRect();
            })();
          hit = true;
        }
      }
      for (let i = 0; i < movers.length; i++) {
        for (let j = i + 1; j < movers.length; j++) {
          const A = movers[i], B = movers[j];
          const aPlace = floatPlacements.get(A.id);
          const bPlace = floatPlacements.get(B.id);
          const aRect = aPlace
            ? shelfRect({ x: aPlace.x, y: aPlace.y, w: aPlace.w, h: aPlace.h }, A.to.x, A.to.y)
            : (A.el.style.translate = `${A.to.x}px ${A.to.y}px`, A.el.getBoundingClientRect());
          const bRect = bPlace
            ? shelfRect({ x: bPlace.x, y: bPlace.y, w: bPlace.w, h: bPlace.h }, B.to.x, B.to.y)
            : (B.el.style.translate = `${B.to.x}px ${B.to.y}px`, B.el.getBoundingClientRect());
          if (!rectsOverlap(aRect, bRect, gapPx)) continue;
          const { dx, dy } = separationPush(aRect, bRect, gapPx);
          if (!dx && !dy) continue;
          A.to.x += dx / scale * .5;
          A.to.y += dy / scale * .5;
          B.to.x -= dx / scale * .5;
          B.to.y -= dy / scale * .5;
          hit = true;
        }
      }
      if (!hit) break;
    }
  };
  resolveTargets();
  const applyMover = (m, x, y) => {
    offsets.set(m.id, { x, y });
    m.el.style.translate = `${x}px ${y}px`;
    m.el.style.setProperty('--ox', `${x}px`);
    m.el.style.setProperty('--oy', `${y}px`);
  };
  // resolveTargets parks movers on their TO seat while measuring — put them
  // back on FROM before the ease so the first paint isn't a snap flash.
  for (const m of movers) applyMover(m, m.from.x, m.from.y);
  const changed = movers.some(m => Math.hypot(m.to.x - m.from.x, m.to.y - m.from.y) > 1);
  if (!changed) return Promise.resolve();
  if (duration <= 0 || document.body.classList.contains('reduce-motion')) {
    for (const m of movers) applyMover(m, m.to.x, m.to.y);
    scheduleDraw();
    return Promise.resolve();
  }
  softSettleRunning += 1;
  return new Promise(resolve => {
    const done = () => {
      softSettleRunning = Math.max(0, softSettleRunning - 1);
      resolve();
    };
    const tick = now => {
      if (token !== softSettleToken) {
        done();
        return;
      }
      const t = Math.min(1, (now - start) / duration);
      const ease = 1 - Math.pow(1 - t, 4);
      for (const m of movers) {
        applyMover(m, m.from.x + (m.to.x - m.from.x) * ease, m.from.y + (m.to.y - m.from.y) * ease);
      }
      if (t < 1) requestAnimationFrame(tick);
      else {
        scheduleDraw();
        done();
      }
    };
    requestAnimationFrame(tick);
  });
}
/**
 * iPhone-style loose shelf: drop anywhere, then settle into rows that share a
 * top edge so siblings sit side-by-side. Insert index comes from the drop point.
 */
function computeNestedShelfSeats(kids, draggedId, dropX, dropY, { gap = NESTED_GAP, pad = NEST_PAD, maxWidth = 640 } = {}) {
  const entries = kids.map(el => {
    const size = frameLayoutSize(el);
    const w = size.w || el.offsetWidth || 200;
    const h = size.h || el.offsetHeight || 70;
    const x = parseFloat(el.style.left) || 0;
    const y = parseFloat(el.style.top) || 0;
    return {
      id: el.dataset.dragId,
      el,
      w, h, x, y,
      cx: x + w / 2,
      cy: y + h / 2
    };
  });
  const mine = entries.find(e => e.id === draggedId);
  if (!mine) return null;
  const ROW_BAND = 56;
  const others = entries.filter(e => e.id !== draggedId);
  const sorted = [...others].sort((a, b) => {
    const rowA = Math.round(a.cy / ROW_BAND);
    const rowB = Math.round(b.cy / ROW_BAND);
    return rowA - rowB || a.x - b.x || a.id.localeCompare(b.id);
  });
  const dropCx = dropX + mine.w / 2;
  const dropCy = dropY + mine.h / 2;
  let insertAt = sorted.length;
  for (let i = 0; i < sorted.length; i++) {
    const o = sorted[i];
    const rowSlack = Math.max(ROW_BAND, (o.h + mine.h) * 0.45);
    if (Math.abs(o.cy - dropCy) <= rowSlack) {
      if (dropCx < o.cx) { insertAt = i; break; }
    } else if (dropCy < o.cy) {
      insertAt = i;
      break;
    }
  }
  const ordered = [...sorted.slice(0, insertAt), { ...mine, x: dropX, y: dropY, cx: dropCx, cy: dropCy }, ...sorted.slice(insertAt)];
  // Pack left→right; wrap into new rows. Every chip in a row shares the same top.
  let x = pad, y = pad, rowH = 0;
  const seats = new Map();
  const shelfW = Math.max(pad * 2 + 200, maxWidth);
  for (const item of ordered) {
    if (x > pad && x + item.w > shelfW - pad) {
      x = pad;
      y += rowH + gap;
      rowH = 0;
    }
    seats.set(item.id, { x, y });
    x += item.w + gap;
    rowH = Math.max(rowH, item.h);
  }
  return { seats, ordered };
}
/**
 * Snap a drop onto a loose grid slot: below a neighbor (shared left) or
 * beside one (shared top) when the drop is clearly in that pocket.
 */
function snapNestedDropSeat(dropX, dropY, dropW, dropH, siblings, gap) {
  let x = dropX;
  let y = dropY;
  if (!siblings.length) return { x, y };
  const dropCx = x + dropW / 2;
  const dropCy = y + dropH / 2;
  let best = null;
  for (const s of siblings) {
    const size = frameLayoutSize(s.el);
    const w = size.w || s.w || 200;
    const h = size.h || s.h || 70;
    const sx = s.to?.x ?? s.x;
    const sy = s.to?.y ?? s.y;
    const cx = sx + w / 2;
    const cy = sy + h / 2;
    const dist = Math.hypot(dropCx - cx, dropCy - cy);
    if (!best || dist < best.dist) best = { sx, sy, w, h, cx, cy, dist };
  }
  if (!best || best.dist > Math.max(best.w, best.h) * 1.8) return { x, y };
  const below = dropCy > best.cy && (dropCy - best.cy) >= Math.abs(dropCx - best.cx) * 0.55;
  const above = dropCy < best.cy && (best.cy - dropCy) >= Math.abs(dropCx - best.cx) * 0.55;
  const right = dropCx > best.cx && !below && !above;
  const left = dropCx < best.cx && !below && !above;
  if (below) {
    // Stack under — share left edge, sit just below.
    x = best.sx;
    y = best.sy + best.h + gap;
  } else if (above) {
    x = best.sx;
    y = best.sy - dropH - gap; // may go past top — parent grows up on settle
  } else if (right) {
    x = best.sx + best.w + gap;
    y = best.sy;
  } else if (left) {
    x = best.sx - dropW - gap; // may go past left — parent grows left on settle
    y = best.sy;
  }
  return { x, y };
}
/** Soft-settle siblings after a nested drop: keep the drop seat, make room, grow parent. */
function softSettleNested(draggedId, parentId, { duration = 560 } = {}) {
  const parentEl = scene.querySelector(`[data-drag-id="${CSS.escape(parentId)}"]`);
  const canvasEl = parentEl?.querySelector(':scope > .frame-canvas');
  if (!canvasEl) return;
  const token = ++softSettleToken;
  const kids = [...canvasEl.querySelectorAll(':scope > .frame.float[data-drag-id]')];
  const mine = kids.find(el => el.dataset.dragId === draggedId);
  if (!mine) return;
  const gap = mine.classList.contains('frame-fn') ? MODULE_GAP : NESTED_GAP;
  const applySeat = (el, x, y) => {
    el.style.left = `${x}px`;
    el.style.top = `${y}px`;
    el.style.translate = '0px 0px';
    el.style.setProperty('--ox', '0px');
    el.style.setProperty('--oy', '0px');
  };
  // Kill CSS left/top transitions while RAF owns the ease — otherwise the
  // stylesheet fights each frame and seats look like they snap.
  for (const el of kids) {
    el.style.transition = 'none';
  }
  parentEl.style.transition = 'width .55s cubic-bezier(.22, 1, .36, 1), height .55s cubic-bezier(.22, 1, .36, 1)';
  canvasEl.style.transition = 'height .55s cubic-bezier(.22, 1, .36, 1), min-height .55s cubic-bezier(.22, 1, .36, 1)';
  // Keep the raw drop — including past top/left. Origin shift grows the folder there.
  const rawX = parseFloat(mine.style.left) || 0;
  const rawY = parseFloat(mine.style.top) || 0;
  const mineSize = frameLayoutSize(mine);
  const mineW = mineSize.w || mine.offsetWidth || 200;
  const mineH = mineSize.h || mine.offsetHeight || 70;
  const siblings = kids.filter(el => el.dataset.dragId !== draggedId).map(el => {
    const size = frameLayoutSize(el);
    return {
      id: el.dataset.dragId,
      el,
      from: { x: parseFloat(el.style.left) || 0, y: parseFloat(el.style.top) || 0 },
      to: { x: parseFloat(el.style.left) || 0, y: parseFloat(el.style.top) || 0 },
      w: size.w || el.offsetWidth || 200,
      h: size.h || el.offsetHeight || 70
    };
  });
  // Keep the drop — snap onto a loose below/beside slot, never yank back to the old shelf.
  const snapped = snapNestedDropSeat(rawX, rawY, mineW, mineH, siblings, gap);
  const mineTo = { x: snapped.x, y: snapped.y };
  const mineBox = {
    left: mineTo.x,
    top: mineTo.y,
    right: mineTo.x + mineW,
    bottom: mineTo.y + mineH,
    width: mineW,
    height: mineH
  };
  const nestBox = (x, y, w, h) => ({ left: x, top: y, right: x + w, bottom: y + h, width: w, height: h });
  const yieldFromAnchor = (m, wall) => {
    const box = nestBox(m.to.x, m.to.y, m.w, m.h);
    if (!rectsOverlap(wall, box, gap)) return false;
    const { dx, dy } = separationPush(box, wall, gap);
    m.to.x += dx;
    m.to.y += dy;
    return true;
  };
  for (let pass = 0; pass < 16; pass++) {
    let hit = false;
    for (const m of siblings) {
      if (yieldFromAnchor(m, mineBox)) hit = true;
    }
    for (let i = 0; i < siblings.length; i++) {
      for (let j = i + 1; j < siblings.length; j++) {
        const A = siblings[i], B = siblings[j];
        const aBox = nestBox(A.to.x, A.to.y, A.w, A.h);
        const bBox = nestBox(B.to.x, B.to.y, B.w, B.h);
        if (!rectsOverlap(aBox, bBox, gap)) continue;
        const { dx, dy } = separationPush(aBox, bBox, gap);
        if (!dx && !dy) continue;
        A.to.x += dx * .5;
        A.to.y += dy * .5;
        B.to.x -= dx * .5;
        B.to.y -= dy * .5;
        hit = true;
      }
    }
    if (!hit) break;
  }

  // Top/left overflow → shift canvas origin so everything stays padded and the
  // folder grows in that direction while the drop stays under the pointer.
  let minX = mineTo.x;
  let minY = mineTo.y;
  for (const m of siblings) {
    minX = Math.min(minX, m.to.x);
    minY = Math.min(minY, m.to.y);
  }
  const shiftX = Math.max(0, NEST_PAD - minX);
  const shiftY = Math.max(0, NEST_PAD - minY);
  if (shiftX || shiftY) {
    mineTo.x += shiftX;
    mineTo.y += shiftY;
    for (const m of siblings) {
      m.to.x += shiftX;
      m.to.y += shiftY;
      m.from.x += shiftX;
      m.from.y += shiftY;
    }
    shiftNestedCanvasOrigin(parentEl, canvasEl, draggedId, shiftX, shiftY);
  }
  const fromX = (parseFloat(mine.style.left) || 0);
  const fromY = (parseFloat(mine.style.top) || 0);

  const movers = [
    { id: draggedId, el: mine, from: { x: fromX, y: fromY }, to: { ...mineTo }, w: mineW, h: mineH },
    ...siblings
  ];

  // Grow from computed seats — don't paint TO before the ease (that snapped).
  let maxX = NEST_PAD, maxY = NEST_PAD;
  for (const m of movers) {
    maxX = Math.max(maxX, m.to.x + m.w);
    maxY = Math.max(maxY, m.to.y + m.h);
  }
  reshapeParentCanvas(parentEl, canvasEl, maxX + NEST_PAD, maxY + NEST_PAD, { allowShrink: true });
  const grandparentEl = parentEl.parentElement?.closest('.frame.float[data-drag-id]');
  const grandparentCanvas = grandparentEl?.querySelector(':scope > .frame-canvas');
  if (grandparentEl && grandparentCanvas) {
    encapsulateNestedChild(
      grandparentEl,
      grandparentCanvas,
      parentEl,
      parseFloat(parentEl.style.left) || 0,
      parseFloat(parentEl.style.top) || 0,
      { skipId: parentEl.dataset.dragId, deep: true, allowShrink: true }
    );
  }
  for (const m of movers) applySeat(m.el, m.from.x, m.from.y);
  nestedSeats.set(draggedId, { ...mineTo });
  userArranged.add(draggedId);

  const finish = () => {
    parentEl.style.transition = '';
    canvasEl.style.transition = '';
    for (const m of movers) {
      applySeat(m.el, m.to.x, m.to.y);
      m.el.style.transition = '';
      nestedSeats.set(m.id, { ...m.to });
    }
    // Re-assert size after seats land — shrink when content no longer needs the room.
    let endX = NEST_PAD, endY = NEST_PAD;
    for (const m of movers) {
      endX = Math.max(endX, m.to.x + m.w);
      endY = Math.max(endY, m.to.y + m.h);
    }
    reshapeParentCanvas(parentEl, canvasEl, endX + NEST_PAD, endY + NEST_PAD, { allowShrink: true });
    if (grandparentEl && grandparentCanvas) {
      encapsulateNestedChild(
        grandparentEl,
        grandparentCanvas,
        parentEl,
        parseFloat(parentEl.style.left) || 0,
        parseFloat(parentEl.style.top) || 0,
        { skipId: parentEl.dataset.dragId, deep: true, allowShrink: true }
      );
    }
    const islandId = dragIslandId(parentId);
    const islandEl = scene.querySelector(`.frame-artboard > .frame.float[data-drag-id="${CSS.escape(islandId)}"]`)
      || scene.querySelector(`[data-drag-id="${CSS.escape(islandId)}"]`);
    if (islandEl) softSettleNeighbors(islandId, islandEl, { duration: 720 });
    scheduleDraw();
    animateReflowEdges(360);
    clearTimeout(softSettleNested._reconcile);
    softSettleNested._reconcile = setTimeout(() => {
      if (app.classList.contains('dragging')) return;
      scheduleDraw();
      renderMinimap();
    }, 60);
  };

  if (duration <= 0 || document.body.classList.contains('reduce-motion')) {
    finish();
    return;
  }
  const start = performance.now();
  const tick = now => {
    if (token !== softSettleToken) return;
    const t = Math.min(1, (now - start) / duration);
    const ease = 1 - Math.pow(1 - t, 4);
    for (const m of movers) {
      applySeat(m.el, m.from.x + (m.to.x - m.from.x) * ease, m.from.y + (m.to.y - m.from.y) * ease);
    }
    if (t < 1) requestAnimationFrame(tick);
    else finish();
  };
  requestAnimationFrame(tick);
}
function reshapeParentCanvas(parentEl, canvasEl, contentW, contentH, { allowShrink = false } = {}) {
  if (!parentEl || !canvasEl) return;
  const header = parentEl.querySelector(':scope > .frame-bar');
  const headerH = header?.offsetHeight || 86;
  const pad = NEST_PAD;
  const layoutW = parseFloat(parentEl.dataset.layoutW) || 0;
  const layoutH = parseFloat(parentEl.dataset.layoutH) || 0;
  const contentNeedW = Math.ceil(Math.max(contentW || canvasEl.scrollWidth, 320) + pad);
  const contentNeedH = Math.ceil(headerH + Math.max(72, contentH || canvasEl.scrollHeight) + pad);
  // Mid-drag / post-expand: never shrink below authored layout — that looked
  // like folders horizontally collapsing and glitching against FLIP.
  const floorW = Math.max(parentEl.offsetWidth || 0, layoutW, FRAME_LABEL_CHROME.folder.minW);
  const floorH = Math.max(parentEl.offsetHeight || 0, layoutH);
  const needW = allowShrink
    ? Math.max(contentNeedW, FRAME_LABEL_CHROME.folder.minW)
    : Math.max(floorW, contentNeedW);
  const needH = allowShrink ? contentNeedH : Math.max(floorH, contentNeedH);
  parentEl.style.width = `${needW}px`;
  parentEl.style.height = `${needH}px`;
  canvasEl.style.height = `${Math.max(72, needH - headerH - 12)}px`;
  canvasEl.style.minHeight = canvasEl.style.height;
}
/**
 * Shift nested seats/DOM when the canvas grows left/up around a child.
 * Parent island moves opposite so the dragged chip stays under the pointer.
 */
function shiftNestedCanvasOrigin(parentEl, canvasEl, skipId, shiftX, shiftY) {
  if (!parentEl || !canvasEl || (!shiftX && !shiftY)) return;
  for (const el of canvasEl.querySelectorAll(':scope > .frame.float[data-drag-id]')) {
    const kidId = el.dataset.dragId;
    const left = (parseFloat(el.style.left) || 0) + shiftX;
    const top = (parseFloat(el.style.top) || 0) + shiftY;
    el.style.left = `${left}px`;
    el.style.top = `${top}px`;
    const seat = nestedSeats.get(kidId);
    if (seat) nestedSeats.set(kidId, { x: seat.x + shiftX, y: seat.y + shiftY });
    else if (kidId === skipId || userArranged.has(kidId)) nestedSeats.set(kidId, { x: left, y: top });
  }
  const parentId = parentEl.dataset.dragId;
  if (!parentId) return;
  const islandId = dragIslandId(parentId);
  if (islandId === parentId) {
    const off = offsets.get(islandId) || { x: 0, y: 0 };
    const next = { x: off.x - shiftX, y: off.y - shiftY };
    offsets.set(islandId, next);
    parentEl.style.translate = `${next.x}px ${next.y}px`;
    parentEl.style.setProperty('--ox', `${next.x}px`);
    parentEl.style.setProperty('--oy', `${next.y}px`);
  } else {
    // Parent itself is nested — nudge its seat the same way.
    const seat = nestedSeats.get(parentId) || {
      x: parseFloat(parentEl.style.left) || 0,
      y: parseFloat(parentEl.style.top) || 0
    };
    const next = { x: seat.x - shiftX, y: seat.y - shiftY };
    userArranged.add(parentId);
    nestedSeats.set(parentId, next);
    parentEl.style.left = `${next.x}px`;
    parentEl.style.top = `${next.y}px`;
  }
}
/** Grow the parent folder around a nested child — including top/left via origin shift. */
function encapsulateNestedChild(parentEl, canvasEl, childEl, childX, childY, {
  skipId = null,
  deep = false,
  allowShrink = false
} = {}) {
  if (!parentEl || !canvasEl || !childEl) return { shiftX: 0, shiftY: 0, x: childX, y: childY };
  const childId = skipId || childEl.dataset.dragId;
  let shiftX = 0;
  let shiftY = 0;
  if (childX < NEST_PAD) shiftX = NEST_PAD - childX;
  if (childY < NEST_PAD) shiftY = NEST_PAD - childY;
  if (shiftX || shiftY) shiftNestedCanvasOrigin(parentEl, canvasEl, childId, shiftX, shiftY);
  const x = childX + shiftX;
  const y = childY + shiftY;
  const childSize = frameLayoutSize(childEl);
  const childW = childSize.w || parseFloat(childEl.style.width) || childEl.offsetWidth || 0;
  const childH = childSize.h || parseFloat(childEl.style.height) || childEl.offsetHeight || 0;

  let maxX = x + childW;
  let maxY = y + childH;
  for (const k of canvasEl.querySelectorAll(':scope > .frame.float[data-drag-id]')) {
    if (k.dataset.dragId === childEl.dataset.dragId) continue;
    const kLeft = parseFloat(k.style.left) || 0;
    const kTop = parseFloat(k.style.top) || 0;
    const kSize = frameLayoutSize(k);
    const kW = kSize.w || parseFloat(k.style.width) || k.offsetWidth || 0;
    const kH = kSize.h || parseFloat(k.style.height) || k.offsetHeight || 0;
    maxX = Math.max(maxX, kLeft + kW);
    maxY = Math.max(maxY, kTop + kH);
  }

  reshapeParentCanvas(parentEl, canvasEl, maxX + NEST_PAD, maxY + NEST_PAD, { allowShrink });

  // Deep growth only on drop/settle — live drag must stay pointer-sticky.
  if (deep) {
    const grandparentEl = parentEl.parentElement?.closest('.frame.float[data-drag-id]');
    const grandparentCanvas = grandparentEl?.querySelector(':scope > .frame-canvas');
    if (grandparentEl && grandparentCanvas) {
      encapsulateNestedChild(
        grandparentEl,
        grandparentCanvas,
        parentEl,
        parseFloat(parentEl.style.left) || 0,
        parseFloat(parentEl.style.top) || 0,
        { skipId: parentEl.dataset.dragId, deep: true, allowShrink }
      );
    }
  }

  return { shiftX, shiftY, x, y };
}
function clearNestDragChrome() {
  scene.querySelectorAll('.nest-drop-active, .nest-canvas-active').forEach(el => {
    el.classList.remove('nest-drop-active', 'nest-canvas-active');
  });
}
function scheduleGravityDrift(delay = 160) {
  // Viewport field gravity runs continuously; luxury-motion only gates jelly/FLIP.
  if (app.classList.contains('dragging')) return;
  clearTimeout(gravityTimer);
  gravityTimer = setTimeout(() => softGravityStep(0), delay);
}
function softGravityStep(pass) {
  if (!graph) return;
  if (traceAlignRaf || softSettleRunning > 0) {
    gravityTimer = setTimeout(() => softGravityStep(0), 280);
    return;
  }
  if (app.classList.contains('dragging')) {
    gravityTimer = setTimeout(() => softGravityStep(0), 240);
    return;
  }
  const root = displayRoot();
  if (!root) {
    gravityTimer = setTimeout(() => softGravityStep(0), 400);
    return;
  }
  let moved = false;
  const centers = [];
  for (const el of topLevelIslandElements()) {
    const id = el.dataset.dragId;
    const item = node(id);
    if (!item) continue;
    const off = offsets.get(id) || { x: 0, y: 0 };
    centers.push({ item, el, off, rect: el.getBoundingClientRect() });
  }
  if (!centers.length) {
    gravityTimer = setTimeout(() => softGravityStep(0), 400);
    return;
  }
  const scale = Math.max(.35, canvas.scale || 1);
  const lockedId = lockedFocusIslandId();
  for (const A of centers) {
    A.far = islandFarFromView(A.rect);
    A.locked = lockedId && A.item.id === lockedId;
    // Only far-off islands drift to the park rim just outside the view.
    // Never park-pull anything still in (or near) the viewfinder.
    // Focused parent island never parks or drifts.
    // Post-minimize seats stay frozen until the user drags or expands.
    if (!A.far || A.locked || seatLock.has(A.item.id)) continue;
    const { pullX, pullY } = pullTowardViewField(A.rect);
    if (Math.abs(pullX) < 2 && Math.abs(pullY) < 2) continue;
    // Long-distance strays catch the rim faster; near-rim stays gentle.
    const dist = Math.hypot(pullX, pullY);
    const speed = dist > 900 ? 0.09 : dist > 420 ? 0.055 : 0.034;
    const maxStep = dist > 900 ? 9.5 : dist > 420 ? 5.2 : 2.6;
    const stepX = clampGravityStep(pullX, scale, speed, maxStep);
    const stepY = clampGravityStep(pullY, scale, speed, maxStep);
    if (Math.abs(stepX) < 0.05 && Math.abs(stepY) < 0.05) continue;
    applyIslandTranslate(A, { x: A.off.x + stepX, y: A.off.y + stepY });
    A.far = islandFarFromView(A.rect);
    moved = true;
  }
  // Soft padding: keep in-view seats still when a stray brushes them.
  // Far ↔ in-view: only the stray yields. In-view ↔ in-view: gentle shared nudge.
  // Gap is screen-space (rects are getBoundingClientRect).
  const gapPx = ISLAND_GAP * scale;
  for (let i = 0; i < centers.length; i++) {
    for (let j = i + 1; j < centers.length; j++) {
      const A = centers[i], B = centers[j];
      if (!rectsOverlap(A.rect, B.rect, gapPx)) continue;
      const { dx, dy } = separationPush(A.rect, B.rect, gapPx);
      if (!dx && !dy) continue;
      const aPinned = pinnedLayout.has(A.item.id) || seatLock.has(A.item.id) || A.locked;
      const bPinned = pinnedLayout.has(B.item.id) || seatLock.has(B.item.id) || B.locked;
      const aArranged = traceArranged.has(A.item.id);
      const bArranged = traceArranged.has(B.item.id);
      const aFar = A.far, bFar = B.far;
      // Focused island never moves — the other yields fully.
      if (A.locked && !B.locked) {
        applyIslandTranslate(B, { x: B.off.x - dx / scale, y: B.off.y - dy / scale });
        B.far = islandFarFromView(B.rect);
        moved = true;
        continue;
      }
      if (B.locked && !A.locked) {
        applyIslandTranslate(A, { x: A.off.x + dx / scale, y: A.off.y + dy / scale });
        A.far = islandFarFromView(A.rect);
        moved = true;
        continue;
      }
      // Two constellation seats still overlapping: never freeze — clear the stack.
      // Prefer the lower hop / earlier id as the keeper when neither is focus.
      if (aArranged && bArranged) {
        applyIslandTranslate(A, { x: A.off.x + (dx / scale) * 0.5, y: A.off.y + (dy / scale) * 0.5 });
        applyIslandTranslate(B, { x: B.off.x - (dx / scale) * 0.5, y: B.off.y - (dy / scale) * 0.5 });
        A.far = islandFarFromView(A.rect);
        B.far = islandFarFromView(B.rect);
        moved = true;
        continue;
      }
      // Focus-rearranged seats keep place; push already-there bystanders away.
      if (aArranged && !bArranged && !bPinned) {
        applyIslandTranslate(B, { x: B.off.x - dx / scale, y: B.off.y - dy / scale });
        B.far = islandFarFromView(B.rect);
        moved = true;
        continue;
      }
      if (bArranged && !aArranged && !aPinned) {
        applyIslandTranslate(A, { x: A.off.x + dx / scale, y: A.off.y + dy / scale });
        A.far = islandFarFromView(A.rect);
        moved = true;
        continue;
      }
      // Stray vs view: park physics owns the stray - don't migrate the view island.
      if (aFar !== bFar) {
        const stray = aFar ? A : B;
        const sign = aFar ? 1 : -1;
        const sx = (dx / scale) * sign;
        const sy = (dy / scale) * sign;
        if (Math.abs(sx) < 0.04 && Math.abs(sy) < 0.04) continue;
        if (!pinnedLayout.has(stray.item.id) && !seatLock.has(stray.item.id) && !stray.locked) {
          applyIslandTranslate(stray, { x: stray.off.x + sx, y: stray.off.y + sy });
          stray.far = islandFarFromView(stray.rect);
          moved = true;
        }
        continue;
      }
      // Both far: separate at full strength so they don't clump on the rim.
      // Both in-view: gentle heal only — strong continuous push feels uncontrollable.
      const strength = aFar ? 1 : 0.38;
      const sx = (dx / scale) * strength;
      const sy = (dy / scale) * strength;
      if (Math.abs(sx) < 0.04 && Math.abs(sy) < 0.04) continue;
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
      } else if (aFar) {
        applyIslandTranslate(A, { x: A.off.x + sx * 0.35, y: A.off.y + sy * 0.35 });
        applyIslandTranslate(B, { x: B.off.x - sx * 0.35, y: B.off.y - sy * 0.35 });
        moved = true;
      }
      A.far = islandFarFromView(A.rect);
      B.far = islandFarFromView(B.rect);
    }
  }
  // No continuous trace suction — constellation pack is one-shot on click.
  // Gravity only parks far islands and heals overlaps.
  if (moved) scheduleDraw();
  gravityTimer = setTimeout(() => softGravityStep(0), moved ? 110 : 280);
}
/** Shelf-space box for a top-level island (base left/top + drag offset). */
function islandShelfBox(el, id) {
  const left = parseFloat(el.style.left) || 0;
  const top = parseFloat(el.style.top) || 0;
  const off = offsets.get(id) || { x: 0, y: 0 };
  const size = frameLayoutSize(el);
  return {
    id,
    el,
    left,
    top,
    off: { x: off.x, y: off.y },
    x: left + off.x,
    y: top + off.y,
    w: size.w || el.offsetWidth || 220,
    h: size.h || el.offsetHeight || 54
  };
}
function cancelTraceAlign() {
  traceAlignToken += 1;
  clearTimeout(traceAlignTimer);
  if (traceAlignRaf) {
    cancelAnimationFrame(traceAlignRaf);
    traceAlignRaf = 0;
  }
  scene?.querySelectorAll('.trace-flying, .trace-align-focus').forEach(el => {
    el.classList.remove('trace-flying', 'trace-align-focus');
    el.style.zIndex = '';
  });
  scene?.classList.remove('trace-aligning');
  // Viewfinder park gravity must keep running after align is cancelled.
  scheduleGravityDrift(220);
}
function stripFlipTransforms() {
  scene?.querySelectorAll('.frame.flipping, .frame.size-morph, .frame.jelly-wobble').forEach(el => {
    el.classList.remove('flipping', 'size-morph', 'jelly-wobble');
    el.style.transform = '';
    if (el.dataset.layoutW) el.style.width = `${el.dataset.layoutW}px`;
    else el.style.width = '';
    if (el.dataset.layoutH) el.style.height = `${el.dataset.layoutH}px`;
    else el.style.height = '';
    const canvasEl = el.querySelector(':scope > .frame-canvas');
    if (canvasEl) canvasEl.style.height = '';
  });
}
function bfsDist(adj, start) {
  const dist = new Map([[start, 0]]);
  const queue = [start];
  while (queue.length) {
    const cur = queue.shift();
    for (const nxt of adj.get(cur) || []) {
      if (dist.has(nxt)) continue;
      dist.set(nxt, dist.get(cur) + 1);
      queue.push(nxt);
    }
  }
  return dist;
}
/** Bake translate offset into shelf left/top so idle pack cannot desync seats.
 *  Must be instant — CSS left/top transitions would clear translate first and
 *  then ease left/top (= snap back, then animate again). */
function bakeIslandOffset(id, el) {
  if (!id || !el) return;
  const left = parseFloat(el.style.left) || 0;
  const top = parseFloat(el.style.top) || 0;
  const off = offsets.get(id) || { x: 0, y: 0 };
  if (!off.x && !off.y) return;
  const nx = left + off.x;
  const ny = top + off.y;
  el.classList.add('seat-baking');
  el.style.left = `${nx}px`;
  el.style.top = `${ny}px`;
  el.style.translate = '0px 0px';
  el.style.setProperty('--ox', '0px');
  el.style.setProperty('--oy', '0px');
  // Flush so the browser commits the baked seat before transitions return.
  void el.offsetWidth;
  el.style.translate = '';
  el.classList.remove('seat-baking');
  offsets.delete(id);
  const place = floatPlacements.get(id);
  if (place) floatPlacements.set(id, { ...place, x: nx, y: ny });
}
function computeConstellationMovers() {
  const empty = { movers: [], stickIds: [], focusTopId: null, packSeats: [], packIds: new Set(), bystanderMoves: [] };
  const focus = selected();
  if (!focus || (focus.kind === 'folder' && focus.depth === 0)) {
    return empty;
  }
  const focusTop = topLevelOwner(fileOf(focus) || focus);
  if (!focusTop) return empty;

  const MAX_HOP = 3;
  const MAX_HOP2 = 10;
  const MAX_HOP3 = 8;
  const ROW_GAP = ISLAND_GAP + 12;
  // Edge-to-edge air between a node and its trace partner — tight enough to read.
  const LINK_GAP = ISLAND_GAP;

  // Candidate islands: focus + anything on the committed trace.
  const candidates = [];
  for (const el of topLevelIslandElements()) {
    const id = el.dataset.dragId;
    const item = node(id);
    if (!item) continue;
    if (id !== focusTop.id && !hasTrace(item)) continue;
    if (id !== focusTop.id && pinnedLayout.has(id)) continue;
    candidates.push(islandShelfBox(el, id));
  }
  if (candidates.length < 2) {
    const focusEl = scene.querySelector(`.frame-artboard > .frame.float[data-drag-id="${CSS.escape(focusTop.id)}"]`);
    const box = focusEl ? islandShelfBox(focusEl, focusTop.id) : null;
    const packSeats = box ? [{ id: focusTop.id, x: box.x, y: box.y, w: box.w, h: box.h }] : [];
    return { movers: [], stickIds: [], focusTopId: focusTop.id, packSeats, packIds: new Set([focusTop.id]), bystanderMoves: [] };
  }

  const candById = new Map(candidates.map(box => [box.id, box]));
  const undirected = new Map(candidates.map(box => [box.id, []]));
  const directed = [];
  const closerLinkCount = new Map(candidates.map(box => [box.id, 0]));
  for (const edge of edgeTypes()) {
    if (!WALK_TYPES.has(edge.type) && edge.type !== 'imports') continue;
    if (!traceEdges.has(edge.id)) continue;
    const aTop = topLevelOwner(fileOf(node(edge.from)) || node(edge.from));
    const bTop = topLevelOwner(fileOf(node(edge.to)) || node(edge.to));
    if (!aTop || !bTop || aTop.id === bTop.id) continue;
    if (!candById.has(aTop.id) || !candById.has(bTop.id)) continue;
    const aList = undirected.get(aTop.id);
    const bList = undirected.get(bTop.id);
    if (aList && !aList.includes(bTop.id)) aList.push(bTop.id);
    if (bList && !bList.includes(aTop.id)) bList.push(aTop.id);
    directed.push({ from: aTop.id, to: bTop.id });
  }
  const hopDist = bfsDist(undirected, focusTop.id);

  const scored = candidates.filter(box => {
    if (box.id === focusTop.id) return true;
    const hop = hopDist.get(box.id);
    return hop != null && hop >= 1 && hop <= MAX_HOP;
  });
  for (const box of scored) {
    if (box.id === focusTop.id) continue;
    const hop = hopDist.get(box.id) || 1;
    let n = 0;
    for (const nid of undirected.get(box.id) || []) {
      if ((hopDist.get(nid) ?? 99) < hop) n += 1;
    }
    closerLinkCount.set(box.id, n);
  }
  const hop1 = scored.filter(b => hopDist.get(b.id) === 1);
  const hop2 = scored
    .filter(b => hopDist.get(b.id) === 2)
    .sort((a, b) => (closerLinkCount.get(b.id) || 0) - (closerLinkCount.get(a.id) || 0) || a.id.localeCompare(b.id))
    .slice(0, MAX_HOP2);
  const hop3 = scored
    .filter(b => hopDist.get(b.id) === 3)
    .sort((a, b) => (closerLinkCount.get(b.id) || 0) - (closerLinkCount.get(a.id) || 0) || a.id.localeCompare(b.id))
    .slice(0, MAX_HOP3);
  const boxes = [candById.get(focusTop.id), ...hop1, ...hop2, ...hop3].filter(Boolean);
  const byId = new Map(boxes.map(box => [box.id, box]));
  const packIds = new Set(boxes.map(b => b.id));

  const focusBox = byId.get(focusTop.id);
  const focusCx = focusBox.x + focusBox.w / 2;
  const emitsIntoFocus = new Set();
  const receivesFromFocus = new Set();
  // Primary parent for deep hops = closer neighbor with the most directed weight.
  const primaryParent = new Map();
  for (const link of directed) {
    if (!packIds.has(link.from) || !packIds.has(link.to)) continue;
    if (link.to === focusTop.id) emitsIntoFocus.add(link.from);
    if (link.from === focusTop.id) receivesFromFocus.add(link.to);
  }
  for (const box of [...hop2, ...hop3]) {
    const hop = hopDist.get(box.id) || 2;
    const closer = (undirected.get(box.id) || [])
      .filter(nid => packIds.has(nid) && (hopDist.get(nid) ?? 99) < hop)
      .sort((a, b) => (hopDist.get(a) ?? 9) - (hopDist.get(b) ?? 9) || a.localeCompare(b));
    primaryParent.set(box.id, closer[0] || focusTop.id);
  }

  const world = new Map();
  world.set(focusTop.id, { x: focusBox.x, y: focusBox.y, w: focusBox.w, h: focusBox.h });
  const preferred = new Map();
  preferred.set(focusTop.id, { x: focusBox.x, y: focusBox.y });

  /** Seat `box` beside `anchor` on `side` (-1 left / +1 right), Y near anchor. */
  const seatBeside = (anchor, box, side, yHint = null) => {
    const gap = LINK_GAP;
    const idealX = side < 0 ? anchor.x - gap - box.w : anchor.x + anchor.w + gap;
    const anchorCy = yHint != null ? yHint : anchor.y + anchor.h / 2;
    const idealY = anchorCy - box.h / 2;
    // Already on the right side with a readable gap? Keep it — only polish the wire.
    const curCx = box.x + box.w / 2;
    const aCx = anchor.x + anchor.w / 2;
    const onSide = side < 0 ? curCx <= aCx + 8 : curCx >= aCx - 8;
    const curGap = side < 0 ? anchor.x - (box.x + box.w) : box.x - (anchor.x + anchor.w);
    if (onSide && curGap >= LINK_GAP * 0.7 && curGap <= LINK_GAP * 3.2) {
      const x = side < 0 ? anchor.x - LINK_GAP - box.w : anchor.x + anchor.w + LINK_GAP;
      // Strong Y ease toward the connector so the edge reads as a short hop.
      const y = box.y + (idealY - box.y) * 0.78;
      return { x, y, w: box.w, h: box.h };
    }
    return { x: idealX, y: idealY, w: box.w, h: box.h };
  };

  /** Resolve same-side overlaps by sliding vertically — never push partners farther from the connector. */
  const resolveVertical = (ids, side) => {
    if (ids.length < 2) return;
    const items = ids.map(id => world.get(id)).filter(Boolean);
    items.sort((a, b) => a.y - b.y || a.id.localeCompare(b.id));
    for (let pass = 0; pass < 24; pass++) {
      let hit = false;
      for (let i = 0; i < items.length - 1; i++) {
        const A = items[i], B = items[i + 1];
        const need = A.y + A.h + ROW_GAP;
        if (B.y >= need) continue;
        const push = (need - B.y) / 2 + 0.5;
        A.y -= push;
        B.y += push;
        hit = true;
      }
      if (!hit) break;
    }
    // Re-assert X on the connector side after vertical slides.
    for (const id of ids) {
      const seat = world.get(id);
      const box = byId.get(id);
      if (!seat || !box) continue;
      const anchor = focusBox;
      seat.x = side < 0 ? anchor.x - LINK_GAP - box.w : anchor.x + anchor.w + LINK_GAP;
      preferred.set(id, { x: seat.x, y: seat.y });
    }
  };

  // Hop-1: each partner sits beside focus at its own connector-aligned Y.
  // Forced column stacks made traces look artificial; per-island seats read as real links.
  const leftIds = [];
  const rightIds = [];
  for (const box of hop1) {
    const isEmitter = emitsIntoFocus.has(box.id);
    const isReceiver = receivesFromFocus.has(box.id);
    let side = box.x + box.w / 2 <= focusCx ? -1 : 1;
    if (isEmitter && !isReceiver) side = -1;
    else if (isReceiver && !isEmitter) side = 1;
    const seat = seatBeside(focusBox, box, side);
    world.set(box.id, { ...seat, id: box.id });
    preferred.set(box.id, { x: seat.x, y: seat.y });
    (side < 0 ? leftIds : rightIds).push(box.id);
  }
  resolveVertical(leftIds, -1);
  resolveVertical(rightIds, 1);

  const placeDeep = (list) => {
    const groups = new Map();
    for (const box of list) {
      const key = primaryParent.get(box.id) || focusTop.id;
      const g = groups.get(key) || [];
      g.push(box);
      groups.set(key, g);
    }
    for (const [anchorId, members] of groups) {
      const anchor = world.get(anchorId) || byId.get(anchorId) || focusBox;
      const ax = anchor.x + anchor.w / 2;
      // Default: outward from focus so the chain keeps reading left→right / right→left.
      let side = ax <= focusCx ? -1 : 1;
      const outs = members.filter(m => directed.some(l => l.from === anchorId && l.to === m.id));
      const ins = members.filter(m => directed.some(l => l.from === m.id && l.to === anchorId));
      if (outs.length && !ins.length) side = 1;
      else if (ins.length && !outs.length) side = -1;
      const ids = [];
      for (const box of members) {
        const seat = seatBeside(anchor, box, side);
        world.set(box.id, { ...seat, id: box.id });
        preferred.set(box.id, { x: seat.x, y: seat.y });
        ids.push(box.id);
      }
      // Vertical resolve relative to this parent — keep X locked to the parent side.
      if (ids.length > 1) {
        const items = ids.map(id => world.get(id)).filter(Boolean);
        items.sort((a, b) => a.y - b.y || a.id.localeCompare(b.id));
        for (let pass = 0; pass < 20; pass++) {
          let hit = false;
          for (let i = 0; i < items.length - 1; i++) {
            const A = items[i], B = items[i + 1];
            const need = A.y + A.h + ROW_GAP;
            if (B.y >= need) continue;
            const push = (need - B.y) / 2 + 0.5;
            A.y -= push;
            B.y += push;
            hit = true;
          }
          if (!hit) break;
        }
        for (const id of ids) {
          const seat = world.get(id);
          const box = byId.get(id);
          if (!seat || !box) continue;
          seat.x = side < 0 ? anchor.x - LINK_GAP - box.w : anchor.x + anchor.w + LINK_GAP;
          preferred.set(id, { x: seat.x, y: seat.y });
        }
      }
    }
  };
  placeDeep(hop2);
  placeDeep(hop3);

  // 1) Clear overlaps among pulled islands (focus stays put).
  const movable = [...world.entries()].map(([id, box]) => ({ id, ...box }));
  separateBoxes(movable, { gap: ISLAND_GAP, passes: 36, anchors: new Set([focusTop.id]), pad: 0 });
  // Tether: hold X hard against the connector (readable wire), ease Y gently.
  for (let tug = 0; tug < 4; tug++) {
    for (const box of movable) {
      if (box.id === focusTop.id) continue;
      const pref = preferred.get(box.id);
      if (!pref) continue;
      box.x += (pref.x - box.x) * 0.72;
      box.y += (pref.y - box.y) * 0.38;
    }
    separateBoxes(movable, { gap: ISLAND_GAP, passes: 14, anchors: new Set([focusTop.id]), pad: 0 });
  }
  for (const box of movable) {
    if (box.id === focusTop.id) {
      world.set(focusTop.id, { x: focusBox.x, y: focusBox.y, w: focusBox.w, h: focusBox.h });
    } else {
      world.set(box.id, { x: box.x, y: box.y, w: box.w, h: box.h });
    }
  }
  world.set(focusTop.id, { x: focusBox.x, y: focusBox.y, w: focusBox.w, h: focusBox.h });

  const packSeats = [...world.entries()].map(([id, box]) => ({ id, ...box }));
  const packIdsFinal = new Set(packSeats.map(s => s.id));

  // 2) Only bystanders that actually sit on a reserved landing seat yield.
  //    Far/unrelated islands stay completely still — no cascade nudges.
  const shelfHits = (a, b, gap) => {
    const ox = Math.min(a.x + a.w, b.x + b.w) - Math.max(a.x, b.x);
    const oy = Math.min(a.y + a.h, b.y + b.h) - Math.max(a.y, b.y);
    return ox > -gap && oy > -gap;
  };
  const bystanderBoxes = [];
  for (const el of topLevelIslandElements()) {
    const id = el.dataset.dragId;
    if (!id || packIdsFinal.has(id)) continue;
    if (pinnedLayout.has(id)) continue;
    const box = islandShelfBox(el, id);
    const blocksLanding = packSeats.some(seat => shelfHits(box, seat, ISLAND_GAP));
    if (!blocksLanding) continue;
    bystanderBoxes.push({
      id,
      el: box.el,
      left: box.left,
      top: box.top,
      x: box.x,
      y: box.y,
      w: box.w,
      h: box.h
    });
  }
  const walls = packSeats.map(s => ({ id: s.id, x: s.x, y: s.y, w: s.w, h: s.h }));
  for (const el of topLevelIslandElements()) {
    const id = el.dataset.dragId;
    if (!id || packIdsFinal.has(id) || bystanderBoxes.some(b => b.id === id)) continue;
    if (!pinnedLayout.has(id)) continue;
    const box = islandShelfBox(el, id);
    walls.push({ id, x: box.x, y: box.y, w: box.w, h: box.h });
  }
  yieldBoxesFromWalls(bystanderBoxes, walls, { gap: ISLAND_GAP, passes: 56, pad: 0 });

  const bystanderMoves = [];
  for (const box of bystanderBoxes) {
    const ox = box.x - box.left;
    const oy = box.y - box.top;
    const cur = offsets.get(box.id) || { x: 0, y: 0 };
    if (Math.abs(ox - cur.x) < 1 && Math.abs(oy - cur.y) < 1) continue;
    bystanderMoves.push({ id: box.id, ox, oy, x: box.x, y: box.y, w: box.w, h: box.h });
  }

  const movers = [];
  const stickIds = [];
  for (const box of boxes) {
    if (box.id === focusTop.id) continue;
    const ideal = world.get(box.id);
    if (!ideal) continue;
    stickIds.push(box.id);
    const tx = ideal.x;
    const ty = ideal.y;
    const dist = Math.hypot(tx - box.x, ty - box.y);
    // Always commit to the cleared seat — short blends left islands overlapping
    // the bystander lane they were supposed to claim.
    const to = { x: tx - box.left, y: ty - box.top };
    if (Math.abs(to.x - box.off.x) < 1.5 && Math.abs(to.y - box.off.y) < 1.5) continue;
    movers.push({
      id: box.id,
      el: box.el,
      from: { ...box.off },
      to,
      dist: Math.max(dist, 1),
      kind: 'trace',
      stick: true
    });
  }
  return { movers, stickIds, focusTopId: focusTop.id, packSeats, packIds: packIdsFinal, bystanderMoves };
}
function scheduleTraceAlign(delay = 90) {
  cancelTraceAlign();
  const token = traceAlignToken;
  traceAlignTimer = setTimeout(() => {
    if (token !== traceAlignToken) return;
    runTraceAlign(token);
  }, delay);
}
function runTraceAlign(token) {
  if (!graph || app.classList.contains('dragging')) {
    if (app.classList.contains('dragging')) {
      const retryToken = token;
      setTimeout(() => {
        if (retryToken !== traceAlignToken) return;
        if (!app.classList.contains('dragging')) runTraceAlign(retryToken);
      }, 220);
    }
    return;
  }
  if (token !== traceAlignToken) return;
  cancelSoftSettle();
  if (scene?.querySelector?.('.frame.flipping, .frame.size-morph')) stripFlipTransforms();
  clearTimeout(gravityTimer);
  clearSeatLock();
  const { movers, stickIds, focusTopId, packSeats, packIds, bystanderMoves } = computeConstellationMovers();
  const focusIsland = focusTopId
    ? scene.querySelector(`.frame-artboard > .frame.float[data-drag-id="${CSS.escape(focusTopId)}"]`)
    : null;
  const protectIds = new Set([focusTopId, ...(stickIds || []), ...(movers || []).map(m => m.id)].filter(Boolean));
  const packIdSet = packIds instanceof Set ? packIds : new Set((packSeats || []).map(p => p.id));
  const clearerIds = new Set((bystanderMoves || []).map(m => m.id));
  // Landing seats only — not pinned islands as extra walls that shove neighbors.
  const walls = [...(packSeats || [])];

  const settleClear = (ms) => {
    if (!focusIsland || !focusTopId) return Promise.resolve();
    return softSettleNeighbors(focusTopId, focusIsland, {
      duration: ms,
      protectIds,
      againstBoxes: walls.length ? walls : null,
      plannedMoves: bystanderMoves || null,
      blockersOnly: true
    });
  };

  const bakeClearers = () => {
    for (const id of clearerIds) {
      const el = scene.querySelector(`.frame-artboard > .frame.float[data-drag-id="${CSS.escape(id)}"]`);
      if (el) bakeIslandOffset(id, el);
    }
  };

  const bakeFlight = () => {
    for (const mover of movers || []) {
      bakeIslandOffset(mover.id, mover.el);
      if (mover.stick) traceArranged.add(mover.id);
    }
    for (const id of stickIds || []) {
      const el = scene.querySelector(`.frame-artboard > .frame.float[data-drag-id="${CSS.escape(id)}"]`);
      if (el) bakeIslandOffset(id, el);
      traceArranged.add(id);
    }
    if (focusTopId) traceArranged.add(focusTopId);
  };

  if (!movers.length) {
    for (const id of stickIds || []) traceArranged.add(id);
    if (focusTopId) traceArranged.add(focusTopId);
    settleClear(820).then(() => {
      bakeClearers();
      softHealIslandGaps(focusTopId, { duration: 420, packIds: packIdSet }).then(() => {
        scheduleGravityDrift(400);
      });
    });
    return;
  }

  const maxDist = Math.max(...movers.map(m => m.dist || 0), 80);
  const duration = Math.min(1400, Math.max(700, 480 + maxDist * 0.9));
  const start = performance.now();
  animateReflowEdges(duration + 200);
  scene.classList.add('trace-aligning');
  for (const mover of movers) {
    mover.el.classList.remove('flipping', 'jelly-wobble');
    mover.el.style.transform = '';
    mover.el.classList.add('trace-flying');
    mover.el.style.zIndex = '60';
  }
  const focusEl = focusIsland
    || elementForSelection()
    || scene.querySelector('.frame.selected, .frame.focus-anchor');
  if (focusEl) {
    focusEl.classList.add('trace-align-focus');
    focusEl.style.zIndex = '70';
  }
  // Clear overlaps in the SAME beat as the flight — not a second snap after.
  const blockersDone = settleClear(duration);

  const tick = now => {
    if (token !== traceAlignToken || app.classList.contains('dragging')) {
      for (const mover of movers) {
        mover.el.classList.remove('trace-flying');
        mover.el.style.zIndex = '';
      }
      focusEl?.classList.remove('trace-align-focus');
      if (focusEl) focusEl.style.zIndex = '';
      scene.classList.remove('trace-aligning');
      traceAlignRaf = 0;
      scheduleGravityDrift(280);
      return;
    }
    const t = Math.min(1, (now - start) / duration);
    const ease = 1 - Math.pow(1 - t, 4);
    for (const mover of movers) {
      const x = mover.from.x + (mover.to.x - mover.from.x) * ease;
      const y = mover.from.y + (mover.to.y - mover.from.y) * ease;
      offsets.set(mover.id, { x, y });
      mover.el.style.translate = `${x}px ${y}px`;
      mover.el.style.setProperty('--ox', `${x}px`);
      mover.el.style.setProperty('--oy', `${y}px`);
    }
    if (t < 1) {
      traceAlignRaf = requestAnimationFrame(tick);
      return;
    }
    for (const mover of movers) {
      offsets.set(mover.id, { ...mover.to });
      mover.el.style.translate = `${mover.to.x}px ${mover.to.y}px`;
      mover.el.style.setProperty('--ox', `${mover.to.x}px`);
      mover.el.style.setProperty('--oy', `${mover.to.y}px`);
    }
    // Bake while still .trace-flying (left/top transitions frozen), then clear classes.
    bakeFlight();
    for (const mover of movers) {
      mover.el.classList.remove('trace-flying');
      mover.el.style.zIndex = '';
    }
    focusEl?.classList.remove('trace-align-focus');
    if (focusEl) focusEl.style.zIndex = '';
    scene.classList.remove('trace-aligning');
    traceAlignRaf = 0;
    blockersDone.then(() => {
      bakeClearers();
      // Heal residual overlaps among traced seats only — never unrelated islands.
      softHealIslandGaps(focusTopId, { duration: 420, packIds: packIdSet }).then(() => {
        scheduleDraw();
        renderMinimap();
        scheduleGravityDrift(400);
      });
    });
  };
  traceAlignRaf = requestAnimationFrame(tick);
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
  const root = displayRoot();
  if (item.kind === 'file' && item.parentId === root?.id) return SYNTHETIC_ROOT_ID;
  // Nested under any folder that isn't the display root → parent canvas is that folder.
  if (item.parentId && item.parentId !== root?.id) return item.parentId;
  return null;
}
/** Size frame chrome from label length.
 * Chrome budgets MUST match public/demo-polish.css (.frame-bar / .fn-flow-hint / .pin-btn).
 * Underestimating chrome is what made module names paint past the chip border. */
const FRAME_LABEL_CHROME = {
  // barPadX + toggle + pin + gaps + titlePadL/R
  // minW must leave a readable title column after chrome; baseH clears 2-line titles.
  folder: { chrome: 32 + 28 + 28 + 16 + 16, minW: 360, maxW: 720, baseH: 86 },
  // barPadX + toggle + flow + pin + gaps + titlePad
  file: { chrome: 32 + 28 + 52 + 28 + 30 + 16, minW: 340, maxW: 620, baseH: 78 },
  // barPadX + flow + pin + gaps + titlePad (no toggle)
  module: { chrome: 26 + 52 + 28 + 20 + 14, minW: 280, maxW: 460, baseH: 70 }
};
function frameLabelMetrics(label = '', {
  kind = 'file',
  charW = 7.6,
  lineH = 18,
  maxLines = 2,
  minW,
  maxW,
  baseH
} = {}) {
  const budget = FRAME_LABEL_CHROME[kind] || FRAME_LABEL_CHROME.file;
  const chrome = budget.chrome;
  const lo = minW ?? budget.minW;
  const hi = maxW ?? budget.maxW;
  const base = baseH ?? budget.baseH;
  const text = String(label || '');
  // Folders: prefer a wider single-line title over a cramped wrap (that looked
  // horizontally squished after chrome grew to 28px toggle + padding).
  const lineBudget = kind === 'folder' ? 1 : maxLines;
  const targetTextW = Math.ceil(text.length * charW / lineBudget);
  const w = Math.min(hi, Math.max(lo, targetTextW + chrome));
  const textW = Math.max(96, w - chrome);
  const charsPerLine = Math.max(10, Math.floor(textW / charW));
  const lines = Math.min(maxLines, Math.max(1, Math.ceil(text.length / charsPerLine) || 1));
  return { w, h: base + (lines - 1) * lineH, lines, textW };
}
function frameModuleSize(_file, module) {
  const label = module?.label ? `${module.label}()` : 'fn';
  const { w, h } = frameLabelMetrics(label, { kind: 'module' });
  return { w, h: Math.max(64, h) };
}
function frameFileSize(file) {
  const header = frameLabelMetrics(file.label, { kind: 'file' });
  if (!expandedFiles.has(file.id)) return { w: header.w, h: header.h, headerH: header.h, children: [] };
  // Pack width: room for modules without forcing them past the file edge.
  const packMax = Math.max(header.w, 640);
  const maxChildW = Math.max(200, packMax - NEST_PAD * 2);
  const boxes = modules(file).slice(0, 18).map(module => {
    const size = frameModuleSize(file, module);
    const w = Math.min(size.w, maxChildW);
    return { id: module.id, item: module, w, h: size.h, size: { ...size, w } };
  });
  const packed = packBoxes(boxes, {
    gap: MODULE_GAP,
    pad: NEST_PAD,
    maxWidth: packMax,
    mode: layoutModes.get(file.id) || 'auto',
    persistLocals: true,
    // Never pin modules to file/folder expand anchors - that skewed the shelf.
    anchors: null
  });
  return { w: Math.max(header.w, packed.w + 8), h: Math.max(header.h, 48) + packed.h + 8, headerH: header.h, children: packed.items };
}
function frameFolderSize(item, depth = 0) {
  const header = frameLabelMetrics(item.label, {
    kind: 'folder',
    minW: depth ? 320 : FRAME_LABEL_CHROME.folder.minW
  });
  if ((!expandedFolders.has(item.id) && item.id !== SYNTHETIC_ROOT_ID) || depth > 8) {
    return { w: header.w, h: header.h, headerH: header.h, children: [] };
  }
  const boxes = folderItems(item).slice(0, depth > 3 ? 20 : 36).map(child => {
    const size = child.kind === 'folder' ? frameFolderSize(child, depth + 1) : frameFileSize(child);
    return { id: child.id, item: child, w: size.w, h: size.h, children: size.children, size };
  });
  const packed = packBoxes(boxes, {
    gap: NESTED_GAP,
    pad: NEST_PAD,
    // Prefer wide shelves so nested trees read left→right, not a deep stack.
    maxWidth: depth === 0 ? 1280 : depth === 1 ? 980 : 760,
    mode: layoutModes.get(item.id) || 'auto',
    persistLocals: true,
    anchors: stickyExpandId ? new Set([stickyExpandId]) : (layoutAnchorIds.size ? layoutAnchorIds : null)
  });
  // Floor width so a single narrow child can't leave the glass shell skinny.
  const minShell = depth ? 340 : 380;
  return {
    w: Math.max(header.w, packed.w + 8, minShell),
    h: Math.max(header.h, 56) + packed.h + 18,
    headerH: header.h,
    children: packed.items
  };
}
/** Shelf-pack floating boxes left→right, wrap on maxWidth, then separate overlaps. */
function packBoxes(boxes, { gap = 14, pad = 12, maxWidth = 900, mode = 'auto', persistLocals = false, anchors = null } = {}) {
  let x = pad, y = pad, rowH = 0;
  const items = [];
  // Keep shelf order stable across focus/defocus so related islands don't
  // teleport in on select and vanish when the trace clears.
  const ordered = [...boxes].sort((a, b) => {
    const ia = a.item || node(a.id);
    const ib = b.item || node(b.id);
    return (mapRegionPriority[mapRegion(ia)] ?? 9) - (mapRegionPriority[mapRegion(ib)] ?? 9)
      || (ia?.label || '').localeCompare(ib?.label || '');
  });
  const useRow = mode === 'row';
  const useCol = mode === 'column';
  const fixed = anchors instanceof Set && anchors.size ? anchors : null;
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
    // User-dragged chips keep an absolute canvas seat when available so drops
    // don't jump back to a stale shelf+local combo after re-pack.
    const seat = userArranged.has(box.id) ? nestedSeats.get(box.id) : null;
    const local = !seat && userArranged.has(box.id) ? (localOffsets.get(box.id) || { x: 0, y: 0 }) : { x: 0, y: 0 };
    items.push({
      ...box,
      shelfX: x,
      shelfY: y,
      x: seat ? seat.x : x + local.x,
      y: seat ? seat.y : y + local.y
    });
    if (useRow || !useCol) {
      x += box.w + gap;
      rowH = Math.max(rowH, box.h);
    } else {
      rowH = box.h;
    }
  }
  separateBoxes(items, { gap, passes: 40, anchors: fixed, pad });
  if (persistLocals) {
    const sticky = stickyExpandId;
    for (const item of items) {
      if (item.shelfX == null) continue;
      const movedFromShelf = Math.abs(item.x - item.shelfX) > 0.5 || Math.abs(item.y - item.shelfY) > 0.5;
      // Persist every seat we pushed during expand so idle reflow can't re-cover.
      if (sticky && (item.id === sticky || movedFromShelf || fixed?.has(item.id))) {
        userArranged.add(item.id);
        nestedSeats.set(item.id, { x: item.x, y: item.y });
      }
      if (!userArranged.has(item.id)) {
        localOffsets.delete(item.id);
        nestedSeats.delete(item.id);
        continue;
      }
      nestedSeats.set(item.id, { x: item.x, y: item.y });
      const dx = item.x - item.shelfX;
      const dy = item.y - item.shelfY;
      if (Math.abs(dx) < .5 && Math.abs(dy) < .5) localOffsets.delete(item.id);
      else localOffsets.set(item.id, { x: dx, y: dy });
    }
  }
  let boundX = pad, boundY = pad;
  for (const item of items) {
    boundX = Math.max(boundX, item.x + item.w);
    boundY = Math.max(boundY, item.y + item.h);
  }
  return { items, w: Math.max(boundX + pad, pad * 2 + 120), h: Math.max(boundY + pad, pad * 2 + 48) };
}
/** Push boxes apart until they clear `gap`. Anchored ids stay put; others yield.
 *  When one side is fixed (expand/focus anchor), movers yield AWAY from it —
 *  never back through the fixed chip (that caused "file glitches to the top"). */
function separateBoxes(items, { gap = 12, passes = 28, anchors = null, pad = gap } = {}) {
  if (items.length < 2) return;
  const fixed = anchors instanceof Set && anchors.size ? anchors : null;
  const yieldAway = (mover, wall, penX, penY) => {
    if (penX < penY) {
      const moverCx = mover.x + mover.w / 2;
      const wallCx = wall.x + wall.w / 2;
      mover.x += moverCx >= wallCx ? (penX + 0.5) : -(penX + 0.5);
    } else {
      const moverCy = mover.y + mover.h / 2;
      const wallCy = wall.y + wall.h / 2;
      mover.y += moverCy >= wallCy ? (penY + 0.5) : -(penY + 0.5);
    }
  };
  for (let pass = 0; pass < passes; pass++) {
    let hit = false;
    for (let i = 0; i < items.length; i++) {
      for (let j = i + 1; j < items.length; j++) {
        const A = items[i], B = items[j];
        const ox = Math.min(A.x + A.w, B.x + B.w) - Math.max(A.x, B.x);
        const oy = Math.min(A.y + A.h, B.y + B.h) - Math.max(A.y, B.y);
        if (ox <= -gap || oy <= -gap) continue;
        const moveA = !fixed?.has(A.id);
        const moveB = !fixed?.has(B.id);
        if (!moveA && !moveB) continue;
        hit = true;
        const penX = ox + gap;
        const penY = oy + gap;
        if (!moveA && moveB) {
          yieldAway(B, A, penX, penY);
        } else if (!moveB && moveA) {
          yieldAway(A, B, penX, penY);
        } else if (penX < penY) {
          const push = penX / 2 + 0.5;
          if (A.x <= B.x) { A.x -= push; B.x += push; } else { A.x += push; B.x -= push; }
        } else {
          const push = penY / 2 + 0.5;
          if (A.y <= B.y) { A.y -= push; B.y += push; } else { A.y += push; B.y -= push; }
        }
      }
    }
    if (!hit) break;
  }
  // Individual pad clamp — never global-shift movers back onto a fixed wall.
  for (const item of items) {
    if (fixed?.has(item.id)) continue;
    item.x = Math.max(pad, item.x);
    item.y = Math.max(pad, item.y);
  }
  // One more yield pass after clamp in case pad push re-overlapped the anchor.
  if (fixed) {
    for (let pass = 0; pass < 8; pass++) {
      let hit = false;
      for (let i = 0; i < items.length; i++) {
        for (let j = i + 1; j < items.length; j++) {
          const A = items[i], B = items[j];
          const ox = Math.min(A.x + A.w, B.x + B.w) - Math.max(A.x, B.x);
          const oy = Math.min(A.y + A.h, B.y + B.h) - Math.max(A.y, B.y);
          if (ox <= -gap || oy <= -gap) continue;
          const moveA = !fixed.has(A.id);
          const moveB = !fixed.has(B.id);
          if (!moveA && !moveB) continue;
          hit = true;
          const penX = ox + gap;
          const penY = oy + gap;
          if (!moveA && moveB) yieldAway(B, A, penX, penY);
          else if (!moveB && moveA) yieldAway(A, B, penX, penY);
          else if (penX < penY) {
            const push = penX / 2 + 0.5;
            if (A.x <= B.x) { A.x -= push; B.x += push; } else { A.x += push; B.x -= push; }
          } else {
            const push = penY / 2 + 0.5;
            if (A.y <= B.y) { A.y -= push; B.y += push; } else { A.y += push; B.y -= push; }
          }
          if (moveA) { A.x = Math.max(pad, A.x); A.y = Math.max(pad, A.y); }
          if (moveB) { B.x = Math.max(pad, B.x); B.y = Math.max(pad, B.y); }
        }
      }
      if (!hit) break;
    }
  }
}
/** Narrow expand anchors: only the expanding chip + its top-level island. */
function markExpandAnchor(id) {
  layoutAnchorIds = new Set();
  if (!id) return;
  stickyExpandId = id;
  layoutAnchorIds.add(id);
  const top = dragIslandId(id);
  if (top) layoutAnchorIds.add(top);
}
function clearExpandAnchor() {
  layoutAnchorIds = new Set();
  stickyExpandId = null;
  collapseMotion = false;
}
/** Freeze current top-level seats so post-minimize clustering cannot pull them in. */
function lockCurrentIslandSeats() {
  seatLock = new Set();
  for (const el of topLevelIslandElements()) {
    const id = el.dataset.dragId;
    if (id) seatLock.add(id);
  }
}
function clearSeatLock() {
  seatLock = new Set();
}
/** After expand morph finishes — drop sticky pack lock, then ONE layout motion.
 *  Collapse must NOT settle/align. Never cleanup + constellation (double snap). */
function finishExpandMorph() {
  const alignDelay = pendingAlignAfterMorph;
  const expandedId = stickyExpandId;
  const wasCollapse = collapseMotion;
  pendingAlignAfterMorph = 0;
  clearExpandAnchor();
  if (wasCollapse) return;
  if (alignDelay > 0) {
    scheduleTraceAlign(alignDelay);
    return;
  }
  if (expandedId) softSettleAfterExpand(expandedId, { duration: 900 });
}
/** Pin a nested frame's current canvas seat so open/resize grows in place
 *  and the parent expands sideways instead of teleporting the chip. */
function pinNestedSeatFromDom(id) {
  if (!id || !parentCanvasId(id)) return false;
  const el = scene.querySelector(`[data-drag-id="${CSS.escape(id)}"]`);
  if (!el) return false;
  userArranged.add(id);
  nestedSeats.set(id, {
    x: parseFloat(el.style.left) || 0,
    y: parseFloat(el.style.top) || 0
  });
  return true;
}
/** Lock a frame to its authored layout size after a morph — clearing width
 *  to '' dropped the inline size and folders looked horizontally collapsed. */
function commitFrameLayoutSize(el, canvasEl = null) {
  if (!el) return;
  const w = parseFloat(el.dataset.layoutW);
  const h = parseFloat(el.dataset.layoutH);
  if (w) el.style.width = `${w}px`;
  if (h) el.style.height = `${h}px`;
  if (canvasEl) {
    const header = el.querySelector(':scope > .frame-bar');
    const headerH = header?.offsetHeight || (el.classList.contains('frame-folder') ? 86 : 78);
    if (h) {
      canvasEl.style.height = `${Math.max(64, h - headerH - 12)}px`;
      canvasEl.style.minHeight = canvasEl.style.height;
    }
  }
}
/** Prefer authored layout size over mid-FLIP offsetWidth. */
function frameLayoutSize(el) {
  if (!el) return { w: 0, h: 0 };
  const w = parseFloat(el.dataset.layoutW) || parseFloat(el.style.width) || el.offsetWidth || 0;
  const h = parseFloat(el.dataset.layoutH) || parseFloat(el.style.height) || el.offsetHeight || 0;
  return { w, h };
}
/** Soft-align nearly matching left/top edges inside a folder canvas. */
function softSnapNestedSeats(entries) {
  if (!entries || entries.length < 2) return;
  for (let i = 0; i < entries.length; i++) {
    for (let j = i + 1; j < entries.length; j++) {
      const A = entries[i], B = entries[j];
      const dx = A.to.x - B.to.x;
      const dy = A.to.y - B.to.y;
      if (Math.abs(dx) > 0.5 && Math.abs(dx) < NEST_SNAP) {
        if (A.fixed && !B.fixed) B.to.x = A.to.x;
        else if (B.fixed && !A.fixed) A.to.x = B.to.x;
        else {
          const x = (A.to.x + B.to.x) / 2;
          if (!A.fixed) A.to.x = x;
          if (!B.fixed) B.to.x = x;
        }
      }
      if (Math.abs(dy) > 0.5 && Math.abs(dy) < NEST_SNAP) {
        if (A.fixed && !B.fixed) B.to.y = A.to.y;
        else if (B.fixed && !A.fixed) A.to.y = B.to.y;
        else {
          const y = (A.to.y + B.to.y) / 2;
          if (!A.fixed) A.to.y = y;
          if (!B.fixed) B.to.y = y;
        }
      }
      // Also snap right/bottom edges when close.
      const aRight = A.to.x + A.w, bRight = B.to.x + B.w;
      const aBot = A.to.y + A.h, bBot = B.to.y + B.h;
      if (!A.fixed && Math.abs(aRight - bRight) < NEST_SNAP && Math.abs(aRight - bRight) > 0.5) {
        A.to.x = bRight - A.w;
      } else if (!B.fixed && Math.abs(aRight - bRight) < NEST_SNAP && Math.abs(aRight - bRight) > 0.5) {
        B.to.x = aRight - B.w;
      }
      if (!A.fixed && Math.abs(aBot - bBot) < NEST_SNAP && Math.abs(aBot - bBot) > 0.5) {
        A.to.y = bBot - A.h;
      } else if (!B.fixed && Math.abs(aBot - bBot) < NEST_SNAP && Math.abs(aBot - bBot) > 0.5) {
        B.to.y = aBot - B.h;
      }
    }
  }
  for (const e of entries) {
    e.to.x = Math.max(NEST_PAD, e.to.x);
    e.to.y = Math.max(NEST_PAD, e.to.y);
  }
}
/**
 * In-folder cleanup: iPhone-style shelf reflow so siblings sit in loose rows
 * side-by-side. Used after expand/reset (drop uses softSettleNested).
 */
function cleanupNestedLayout(parentId, { duration = 520, anchorId = null, allowShrink = false } = {}) {
  const parentEl = scene.querySelector(`[data-drag-id="${CSS.escape(parentId)}"]`);
  const canvasEl = parentEl?.querySelector(':scope > .frame-canvas');
  if (!canvasEl) return;
  // Don't fight an in-flight size morph — that glitched folder widths.
  if (parentEl.classList.contains('flipping') || parentEl.classList.contains('size-morph')) return;
  const token = ++softSettleToken;
  const kids = [...canvasEl.querySelectorAll(':scope > .frame.float[data-drag-id]')];
  if (!kids.length) return;
  const gap = kids.every(el => el.classList.contains('frame-fn')) ? MODULE_GAP : NESTED_GAP;
  const anchorEl = anchorId ? kids.find(el => el.dataset.dragId === anchorId) : null;
  const dropX = anchorEl ? (parseFloat(anchorEl.style.left) || 0) : (parseFloat(kids[0].style.left) || NEST_PAD);
  const dropY = anchorEl ? (parseFloat(anchorEl.style.top) || 0) : (parseFloat(kids[0].style.top) || NEST_PAD);
  const pivotId = anchorId || kids[0].dataset.dragId;
  const canvasW = Math.max(
    canvasEl.clientWidth || 0,
    parseFloat(parentEl.style.width) || parentEl.offsetWidth || 0,
    parseFloat(parentEl.dataset.layoutW) || 0,
    480
  );
  const shelf = computeNestedShelfSeats(kids, pivotId, dropX, dropY, {
    gap,
    pad: NEST_PAD,
    maxWidth: canvasW
  });
  if (!shelf) return;
  const entries = kids.map(el => {
    const id = el.dataset.dragId;
    const from = { x: parseFloat(el.style.left) || 0, y: parseFloat(el.style.top) || 0 };
    const seat = shelf.seats.get(id) || from;
    const size = frameLayoutSize(el);
    return {
      id,
      el,
      from,
      to: { x: Math.max(NEST_PAD, seat.x), y: Math.max(NEST_PAD, seat.y) },
      w: size.w,
      h: size.h
    };
  });
  const grow = entries.reduce((acc, e) => ({
    x: Math.max(acc.x, e.to.x + e.w),
    y: Math.max(acc.y, e.to.y + e.h)
  }), { x: NEST_PAD, y: NEST_PAD });
  // Grow from computed seats — never paint TO seats before the ease (that snapped).
  reshapeParentCanvas(parentEl, canvasEl, grow.x + NEST_PAD, grow.y + NEST_PAD, { allowShrink });
  const grandparentEl = parentEl.parentElement?.closest('.frame.float[data-drag-id]');
  const grandparentCanvas = grandparentEl?.querySelector(':scope > .frame-canvas');
  if (grandparentEl && grandparentCanvas) {
    encapsulateNestedChild(
      grandparentEl,
      grandparentCanvas,
      parentEl,
      parseFloat(parentEl.style.left) || 0,
      parseFloat(parentEl.style.top) || 0,
      { skipId: parentEl.dataset.dragId, deep: true, allowShrink }
    );
  }
  const applySeat = (el, x, y) => {
    el.style.left = `${x}px`;
    el.style.top = `${y}px`;
    el.style.translate = '0px 0px';
    el.style.setProperty('--ox', '0px');
    el.style.setProperty('--oy', '0px');
  };
  for (const e of entries) {
    e.el.style.transition = 'none';
    applySeat(e.el, e.from.x, e.from.y);
  }
  if (duration <= 0 || document.body.classList.contains('reduce-motion')) {
    for (const e of entries) {
      applySeat(e.el, e.to.x, e.to.y);
      e.el.style.transition = '';
      nestedSeats.set(e.id, { ...e.to });
      if (anchorId && e.id === anchorId) userArranged.add(e.id);
    }
    scheduleDraw();
    return;
  }
  // Only ease parent size when we actually grew — width thrash looked like a collapse glitch.
  const grew =
    (parseFloat(parentEl.style.width) || 0) > (parseFloat(parentEl.dataset.layoutW) || 0) + 1
    || allowShrink;
  if (grew) {
    parentEl.style.transition = 'width .55s cubic-bezier(.22, 1, .36, 1), height .55s cubic-bezier(.22, 1, .36, 1)';
    canvasEl.style.transition = 'height .55s cubic-bezier(.22, 1, .36, 1), min-height .55s cubic-bezier(.22, 1, .36, 1)';
  }
  const start = performance.now();
  const tick = now => {
    if (token !== softSettleToken) return;
    const t = Math.min(1, (now - start) / duration);
    const ease = 1 - Math.pow(1 - t, 4);
    for (const e of entries) {
      applySeat(
        e.el,
        e.from.x + (e.to.x - e.from.x) * ease,
        e.from.y + (e.to.y - e.from.y) * ease
      );
    }
    if (t < 1) requestAnimationFrame(tick);
    else {
      parentEl.style.transition = '';
      canvasEl.style.transition = '';
      for (const e of entries) {
        applySeat(e.el, e.to.x, e.to.y);
        e.el.style.transition = '';
        nestedSeats.set(e.id, { ...e.to });
        if (anchorId && e.id === anchorId) userArranged.add(e.id);
      }
      scheduleDraw();
      animateReflowEdges(360);
    }
  };
  requestAnimationFrame(tick);
}
/** After expand/reflow, ease overlapping top-level islands away from the grown one. */
function softSettleAfterExpand(id, { duration = 1800 } = {}) {
  const islandId = dragIslandId(id);
  const run = () => {
    const islandEl = scene.querySelector(`.frame-artboard > .frame.float[data-drag-id="${CSS.escape(islandId)}"]`)
      || scene.querySelector(`[data-drag-id="${CSS.escape(islandId)}"]`);
    if (!islandEl) return;
    softSettleNeighbors(islandId, islandEl, { duration: Math.max(720, Math.min(1100, duration)) });
    // Nested open: shelf-resolve siblings inside the parent canvas around the grown chip.
    // Grow-only — shrinking the shell here collapsed folders horizontally mid-morph.
    const parentId = parentCanvasId(id);
    if (parentId) cleanupNestedLayout(parentId, {
      duration: Math.min(520, duration),
      anchorId: id,
      allowShrink: false
    });
  };
  // Wait two frames so playFlip commits final width/height before any live measure fallback.
  requestAnimationFrame(() => requestAnimationFrame(run));
}
/** Shelf width that prefers a near-square grid of top-level islands. */
function preferredShelfWidth(boxes, { gap = 28, pad = 40 } = {}) {
  const n = Math.max(1, boxes.length);
  const cols = Math.max(2, Math.ceil(Math.sqrt(n * 1.15)));
  const avgW = boxes.reduce((sum, box) => sum + (box.w || 220), 0) / n;
  const byContent = cols * (avgW + gap) + pad * 2;
  const byViewport = Math.max(1100, (board?.clientWidth || 1100) * 1.45);
  return Math.max(byContent, byViewport);
}
function buildFloatLayout(root) {
  floatPlacements.clear();
  const view = root || displayRoot();
  if (!view) return { w: 800, h: 480, items: [] };
  // Visual seats (shelf + translate) — single source of truth before pack.
  const prevVisual = new Map();
  scene.querySelectorAll('.frame-artboard > .frame.float[data-drag-id]').forEach(el => {
    const id = el.dataset.dragId;
    if (!id) return;
    const left = parseFloat(el.style.left) || 0;
    const top = parseFloat(el.style.top) || 0;
    const off = offsets.get(id) || { x: 0, y: 0 };
    prevVisual.set(id, { x: left + off.x, y: top + off.y, left, top, ox: off.x, oy: off.y });
  });
  const top = topLevelItems(view).map(child => {
    const size = child.kind === 'folder' || child.synthetic ? frameFolderSize(child, 0) : frameFileSize(child);
    return { id: child.id, item: child, w: size.w, h: size.h, size };
  });
  const shelfW = preferredShelfWidth(top, { gap: ISLAND_GAP + 16, pad: 40 });
  const packed = packBoxes(top, { gap: ISLAND_GAP + 16, pad: 40, maxWidth: shelfW });
  for (const entry of packed.items) {
    const frozen = prevVisual.get(entry.id);
    // Preserve prior shelf seats (not visual+offset — offsets still apply in frameStyle).
    if (!forceFreshPack && frozen) { entry.x = frozen.left; entry.y = frozen.top; }
  }
  forceFreshPack = false;

  // Motion ownership:
  //  - Expand/collapse (layoutAnchorIds): bake translates into seats, separate
  //    with FINAL sizes, clear offsets → FLIP alone animates neighbors away.
  //  - Focus-only (alignMotionPending, no expand): leave seats + offsets alone
  //    so constellation can ease via translate without a pack snap.
  const expanding = layoutAnchorIds.size > 0 || !!stickyExpandId;
  if (expanding) {
    for (const entry of packed.items) {
      const frozen = prevVisual.get(entry.id);
      if (frozen) {
        entry.x = frozen.x;
        entry.y = frozen.y;
      }
      offsets.delete(entry.id);
    }
    // Minimize: keep every island put. separateBoxes/relax would drift small
    // folders into the freed hole toward the map center.
    // Focus-open: skip pack-separate here — constellation + settleClear own
    // one motion. Doing both was the expand-FLIP then fly double-snap.
    if (!collapseMotion && pendingAlignAfterMorph <= 0) {
      // Only the top-level island of the expand target stays fixed — not the whole ancestor set.
      const topAnchors = new Set();
      const stickyTop = stickyExpandId ? dragIslandId(stickyExpandId) : null;
      if (stickyTop) topAnchors.add(stickyTop);
      for (const id of layoutAnchorIds) {
        const top = dragIslandId(id);
        if (top) topAnchors.add(top);
      }
      separateBoxes(packed.items, { gap: ISLAND_GAP, passes: 56, anchors: topAnchors, pad: 40 });
    }
    // Do not relaxTopLevel during expand — clustering pulls neighbors back into the grow.
  } else if (!alignMotionPending) {
    const locked = lockedFocusIslandId();
    const topAnchors = new Set();
    if (locked) topAnchors.add(locked);
    for (const id of pinnedLayout) topAnchors.add(id);
    // Idle reflow: separate in visual space, then write shelf by subtracting offsets.
    for (const entry of packed.items) {
      const off = offsets.get(entry.id) || { x: 0, y: 0 };
      entry.x += off.x;
      entry.y += off.y;
      entry._ox = off.x;
      entry._oy = off.y;
    }
    if (traceArranged.size) {
      // After focus pull: freeze constellation seats. Only islands that sit on
      // a reserved seat yield — never reshuffle the rest of the map.
      for (const id of traceArranged) topAnchors.add(id);
      const walls = packed.items.filter(item => topAnchors.has(item.id));
      const free = packed.items.filter(item => !topAnchors.has(item.id));
      yieldBoxesFromWalls(free, walls, { gap: ISLAND_GAP, passes: 36, pad: 0 });
    } else {
      separateBoxes(packed.items, { gap: ISLAND_GAP, passes: 48, anchors: topAnchors.size ? topAnchors : null, pad: 0 });
      // Post-minimize seatLock: heal overlaps only — never cluster toward center.
      if (!seatLock.size) relaxTopLevel(packed.items, ISLAND_GAP);
    }
    for (const entry of packed.items) {
      entry.x -= entry._ox || 0;
      entry.y -= entry._oy || 0;
      delete entry._ox;
      delete entry._oy;
    }
  }

  let maxX = 0, maxY = 0;
  for (const entry of packed.items) {
    floatPlacements.set(entry.id, { x: entry.x, y: entry.y, w: entry.w, h: entry.h });
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
  const locked = lockedFocusIslandId();
  // Gentle clustering only - hard pulls made focus feel like a snap, and
  // clearing the trace made related islands jump away / off-screen.
  const passes = traceActive() ? 10 : 8;
  // Prefer seats for user-pinned / focus / post-minimize lock — NOT every
  // constellation id (restoring those re-stacked overlaps every pass).
  const pinnedXY = new Map(items.filter(item => pinnedLayout.has(item.id) || seatLock.has(item.id) || item.id === locked).map(item => [item.id, { x: item.x, y: item.y }]));
  for (let pass = 0; pass < passes; pass++) {
    for (const edge of edgeTypes()) {
      if (!WALK_TYPES.has(edge.type) && edge.type !== 'imports') continue;
      // With a committed focus, only pull along the live trace — never tug
      // unrelated graph neighbors (that snapped non-trace islands on focus).
      if (hasCommittedTraceFocus() && traceEdges.size && !traceEdges.has(edge.id)) continue;
      const aFile = fileOf(node(edge.from));
      const bFile = fileOf(node(edge.to));
      if (!aFile || !bFile) continue;
      const aTop = topLevelOwner(aFile);
      const bTop = topLevelOwner(bFile);
      if (!aTop || !bTop || aTop.id === bTop.id) continue;
      if ((pinnedLayout.has(aTop.id) || traceArranged.has(aTop.id) || seatLock.has(aTop.id) || aTop.id === locked)
        && (pinnedLayout.has(bTop.id) || traceArranged.has(bTop.id) || seatLock.has(bTop.id) || bTop.id === locked)) continue;
      const A = byId.get(aTop.id), B = byId.get(bTop.id);
      if (!A || !B) continue;
      const related = focusSeeds.has(edge.from) || focusSeeds.has(edge.to) || hasTrace(aTop) || hasTrace(bTop);
      const ax = A.x + A.w / 2, ay = A.y + A.h / 2;
      const bx = B.x + B.w / 2, by = B.y + B.h / 2;
      const dx = bx - ax, dy = by - ay;
      const dist = Math.hypot(dx, dy) || 1;
      const desired = related && traceActive()
        ? 150 + (A.w + B.w) * .12
        : 190 + (A.w + B.w) * .16;
      // Pull together when farther than desired; never push apart here (separateBoxes does that).
      const pull = Math.min(related ? 4.2 : 2.8, (dist - desired) * (related ? .05 : .032));
      if (pull < 0.15) continue;
      const ux = dx / dist, uy = dy / dist;
      const level = related && traceActive() ? (ay - by) * .01 : 0;
      if (!pinnedLayout.has(aTop.id) && !traceArranged.has(aTop.id) && !seatLock.has(aTop.id) && aTop.id !== locked) {
        A.x += ux * pull * .5; A.y += uy * pull * .5 - level;
      }
      if (!pinnedLayout.has(bTop.id) && !traceArranged.has(bTop.id) && !seatLock.has(bTop.id) && bTop.id !== locked) {
        B.x -= ux * pull * .5; B.y -= uy * pull * .5 + level;
      }
    }
    // Hard anchors: focus + user pins + seatLock. Constellation seats may
    // still yield so overlaps clear instead of freezing stacked folders.
    const anchors = new Set([
      ...(layoutAnchorIds.size ? layoutAnchorIds : []),
      ...(locked ? [locked] : []),
      ...pinnedLayout,
      ...seatLock
    ]);
    if (anchors.size) {
      separateBoxes(items, { gap: ISLAND_GAP, passes: 14, anchors });
      for (const [id, xy] of pinnedXY) {
        const item = byId.get(id);
        if (item) { item.x = xy.x; item.y = xy.y; }
      }
    } else {
      separateBoxes(items.filter(item => !pinnedLayout.has(item.id) && !seatLock.has(item.id)), { gap: ISLAND_GAP, passes: 12 });
      for (const [id, xy] of pinnedXY) {
        const item = byId.get(id);
        if (item) { item.x = xy.x; item.y = xy.y; }
      }
    }
  }
  let minX = Infinity, minY = Infinity;
  for (const item of items) { minX = Math.min(minX, item.x); minY = Math.min(minY, item.y); }
  const shiftX = pad - minX, shiftY = pad - minY;
  for (const item of items) {
    // Keep expand anchors, locked focus, and idle pinned seats fixed.
    if (layoutAnchorIds.has(item.id) || item.id === locked) continue;
    if (!layoutAnchorIds.size && !locked && pinnedLayout.has(item.id)) continue;
    item.x += shiftX;
    item.y += shiftY;
  }
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
  const live = activeTraceEdges();
  const add = (line, side, edge) => { if (!line) return; const list = notes.get(line) || []; if (!list.some(note => note.edge.id === edge.id && note.side === side)) list.push({ side, edge }); notes.set(line, list); };
  for (const edge of edgeTypes()) {
    if (traceActive() && !live.has(edge.id)) continue;
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
  const live = activeTraceEdges();
  return `<button class="inline-import ${selectedImportEdgeId === edge.id ? 'selected' : ''} ${traceActive() && !live.has(edge.id) ? 'dim' : ''}" data-inline-import="${edge.id}" title="${escape(edge.evidence)}">
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
  return `<section class="source module-source" data-module-source="${module.id}"><header><b>${escape(module.label)}()</b><span>source lines ${start}-${end}</span></header><pre>${lines || '<span class="line"><i>-</i><code>No source range found.</code><span></span></span>'}</pre></section>`;
}
function formatDiffHtml(file, limit = 120) {
  const diff = file?.git?.diff;
  if (!diff) return '<span class="diff-line meta">New or untracked file. Full source is in the canvas.</span>';
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
  return `<span class="port edge-port in endpoint-port" data-port-for="${id}" data-port-side="in" title="Trace in"></span><span class="port edge-port out endpoint-port" data-port-for="${id}" data-port-side="out" title="Trace out"></span>`;
}
function frameStyle(placement, tint, id, { depth = 0, inertia = 0 } = {}) {
  // Only top-level islands carry world offsets; nested frames stay inside the parent canvas.
  const island = dragIslandId(id);
  const off = island === id ? (offsets.get(id) || { x: 0, y: 0 }) : { x: 0, y: 0 };
  const glass = Math.min(78, 16 + depth * 14);
  const delay = hashHue(id) % 900;
  const h = placement.h ? `height:${placement.h}px;` : '';
  return `left:${placement.x}px;top:${placement.y}px;width:${placement.w}px;${h}translate:${off.x}px ${off.y}px;--ox:${off.x}px;--oy:${off.y}px;--node:${tint};--accent:${tint};--depth:${depth};--glass:${glass}%;--float-delay:${delay};--inertia:${inertia}`;
}
/** Final layout size as data attrs — readable while playFlip temporarily sets old width/height. */
function frameLayoutData(placement) {
  const w = placement?.w != null ? ` data-layout-w="${Math.round(placement.w)}"` : '';
  const h = placement?.h != null ? ` data-layout-h="${Math.round(placement.h)}"` : '';
  return `${w}${h}`;
}
function frameModuleHtml(file, module, placement, depth = 0, inertia = 0) {
  const hot = hoverId === module.id ? 'hot' : '';
  const tint = fileTint(file);
  return `<section class="frame frame-fn float ${selectedId === module.id ? 'selected' : ''} ${hot}" data-module-box="${module.id}" data-hover="${module.id}" data-drag-id="${module.id}" data-open-flow="${module.id}" title="Open code flow"${frameLayoutData(placement)} style="${frameStyle(placement, tint, module.id, { depth: depth + 1, inertia })}">
    <header class="frame-bar frame-bar-module" data-outline-row="${module.id}" data-hover="${module.id}">
      ${framePorts(module.id)}
      <button class="frame-title" data-module="${module.id}" data-open-flow="${module.id}" type="button" title="${escape(module.label)}()">
        <em class="fn-kind">${module.moduleKind === 'class' ? 'class' : 'fn'}</em>
        <b title="${escape(module.label)}()">${escape(module.label)}()</b>
      </button>
      <button class="fn-flow-hint" data-open-flow="${module.id}" type="button" title="Open code flow">flow</button>
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
  return `<section class="frame frame-file float ${expanded ? 'expanded' : ''} ${selectedId === file.id || fileOf(selected())?.id === file.id ? 'selected' : ''} ${recentFor(file) ? 'live-changed' : ''} ${file.orphan ? 'orphan' : ''} ${file.entrypoint ? 'entrypoint' : ''} ${hot}" data-id="${file.id}" data-inline="${file.id}" data-inline-file="${file.id}" data-kind="file" data-hover="${file.id}" data-drag-id="${file.id}" data-depth="${depth}"${frameLayoutData(placement)} style="${frameStyle(placement, tint, file.id, { depth })}">
    <header class="frame-bar frame-bar-file" data-outline-row="${file.id}" data-hover="${file.id}">
      ${framePorts(file.id)}
      <button class="frame-toggle" data-expand="${file.id}" type="button">${expanded ? '⌄' : '›'}</button>
      <button class="frame-title outline-label" data-inline="${file.id}" data-kind="file" data-focus-file="${file.id}" type="button" title="${escape(file.path || file.label)}">
        <span class="file-glyph" style="--glyph:${glyph.c}" title="${escape(file.extension || '')}">${escape(glyph.g)}</span>
        <b title="${escape(file.path || file.label)}">${escape(file.label)}</b>
        <span class="frame-count">${modules(file).length || '-'}</span>
      </button>
      <button class="fn-flow-hint" data-open-file-flow="${file.id}" type="button" title="Open code flow">flow</button>
      <button class="port pin-btn ${pinned.has(file.id) ? 'pinned' : ''}" data-pin="${file.id}" type="button" title="Pin"></button>
    </header>
    ${expanded ? `<div class="frame-canvas float-canvas" style="height:${Math.max(64, placement.h - (size.headerH || 78) - 12)}px">${kids || '<p class="frame-empty">Empty</p>'}</div>` : ''}
  </section>`;
}
function frameFolderHtml(item, placement, size = frameFolderSize(item, 0), depth = 0) {
  const expanded = item.id === SYNTHETIC_ROOT_ID || item.synthetic || expandedFolders.has(item.id);
  const files = item.id === SYNTHETIC_ROOT_ID ? syntheticRootFiles.length : filesBelow(item).length;
  const region = item.synthetic ? 'context' : mapRegion(item);
  const copy = item.synthetic ? { title: 'root' } : railCopy(region);
  const hot = hoverId === item.id ? 'hot' : '';
  const tint = folderTint(item);
  const canMinimize = folderCanMinimize(item);
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
  return `<section class="frame frame-folder float ${expanded ? 'expanded' : ''} ${item.synthetic ? 'synthetic-root' : ''} ${!canMinimize ? 'no-toggle' : ''} ${selectedId === item.id ? 'selected' : ''} ${hot}" data-id="${item.id}" data-inline="${item.id}" data-kind="folder" data-region="${region}" data-depth="${depth}" data-hover="${item.id}" data-drag-id="${item.id}"${frameLayoutData(placement)} style="${frameStyle(placement, tint, item.id, { depth })}">
    <header class="frame-bar${!canMinimize ? ' frame-bar-no-toggle' : ''}" data-outline-row="${item.id}" data-hover="${item.id}">
      ${framePorts(item.id)}
      ${canMinimize ? `<button class="frame-toggle" data-folder-expand="${item.id}" type="button" aria-label="${expanded ? 'Minimize folder' : 'Expand folder'}">${expanded ? '⌄' : '›'}</button>` : ''}
      <button class="frame-title outline-label" data-inline="${item.id}" data-kind="folder" type="button" title="${escape(item.path || item.label)}">
        <em class="frame-kind">${escape(copy.title)}</em>
        <b title="${escape(item.path || item.label)}">${escape(item.label)}</b>
        <span class="frame-count">${files}</span>
      </button>
      <button class="port pin-btn ${pinned.has(item.id) ? 'pinned' : ''}" data-pin="${item.id}" type="button" title="Pin"></button>
    </header>
    ${expanded ? `<div class="frame-canvas float-canvas" style="height:${Math.max(88, placement.h - (size.headerH || 86) - 14)}px">${kids || '<p class="frame-empty">Empty</p>'}</div>` : ''}
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
function chromeHtml(_layout) {
  return '';
}
/** Top-level island that must stay put while its subtree is the focus. */
function lockedFocusIslandId() {
  const focus = selected();
  if (!focus) return null;
  const top = topLevelOwner(fileOf(focus) || focus);
  return top?.id || null;
}
function isLockedFocusIsland(id) {
  const locked = lockedFocusIslandId();
  return !!(locked && id === locked);
}
function render() {
  if (!graph) return;
  // Never rebuild DOM mid-drag - that orphans the pointer capture and jumps nodes.
  if (app.classList.contains('dragging')) return;
  const overlayOpen = !!$('#flow-overlay')?.open;
  const alignOwned = alignMotionPending && !overlayOpen;
  // Expanding a folder/file should morph — never quiet/skip FLIP on open.
  const expanding = layoutAnchorIds.size > 0;
  if (overlayOpen) {
    skipFlipOnce = true;
    cancelSoftSettle();
    quietLayoutMotion(280);
  } else if (alignOwned || expanding) {
    // Keep size/position morph alive for focus + expand.
    skipFlipOnce = false;
    app.classList.remove('layout-quiet');
    clearTimeout(quietLayoutMotion._t);
    cancelSoftSettle();
  }
  if (overlayOpen) alignMotionPending = false;
  // Nested frames must not keep independent world offsets - they live inside folders.
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
  // Keep click under pointer only during open morph — focus-only align must not
  // pre-nudge (that read as the first snap before constellation).
  if (clickAnchor && !overlayOpen && expanding) stabilizeClickAnchor();
  else clickAnchor = null;
  drawEdges();
  playFlip(before);
  animateReflowEdges(overlayOpen ? 400 : expanding ? 1100 : alignOwned ? 400 : 920);
  // Sticky expand cleared in finishExpandMorph after FLIP — not here.
  if (!expanding) clearExpandAnchor();
  // Always keep viewfinder park gravity alive — focus/align only delays it.
  if (overlayOpen) {
    alignMotionPending = false;
    clearTimeout(gravityTimer);
  } else if (alignOwned || expanding) {
    alignMotionPending = false;
    scheduleGravityDrift(1200);
  } else {
    scheduleGravityDrift();
  }
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
  if (item?.kind === 'module') {
    // Frame modules use data-module-box / data-drag-id (not data-inline-module).
    if (scene.querySelector(`[data-module-box="${CSS.escape(item.id)}"],[data-drag-id="${CSS.escape(item.id)}"],[data-inline-module="${CSS.escape(item.id)}"]`)) {
      return item.id;
    }
    if (scene.querySelector(`[data-module="${CSS.escape(item.id)}"]`)) {
      return `module:${item.id}`;
    }
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
function endpointHost(id) {
  if (!id) return null;
  if (id.startsWith('source:')) return scene.querySelector(`[data-source-port="${CSS.escape(id)}"]`);
  if (id.startsWith('import:')) return scene.querySelector(`[data-import-port="${CSS.escape(id)}"]`);
  if (id.startsWith('inline-module:') || id.startsWith('module:')) {
    const mid = id.startsWith('inline-module:') ? id.slice(14) : id.slice(7);
    return scene.querySelector(`[data-module-box="${CSS.escape(mid)}"],[data-drag-id="${CSS.escape(mid)}"],[data-inline-module="${CSS.escape(mid)}"]`)
      || scene.querySelector(`[data-module="${CSS.escape(mid)}"]`)?.closest('.frame')
      || scene.querySelector(`[data-module="${CSS.escape(mid)}"]`);
  }
  if (id.startsWith('inline:')) return scene.querySelector(`[data-inline-file="${CSS.escape(id.slice(7))}"]`);
  return scene.querySelector(`[data-id="${CSS.escape(id)}"],[data-module-box="${CSS.escape(id)}"],[data-drag-id="${CSS.escape(id)}"]`);
}
function endpointPortId(id) {
  if (id.startsWith('inline-module:')) return id.slice(14);
  if (id.startsWith('module:')) return id.slice(7);
  if (id.startsWith('inline:')) return id.slice(7);
  return id;
}
function markEndpoint(id, side) {
  const element = endpointHost(id); if (!element) return;
  if (element.matches('[data-source-port],[data-import-port]')) { element.classList.add('connected-port'); return; }
  const host = element.closest?.('.frame') || element;
  const port = host.querySelector(`[data-port-for="${CSS.escape(endpointPortId(id))}"][data-port-side="${side}"]`);
  port?.classList.add('connected-port');
}
function crossingOffsets(edges) {
  const offsets = new Map();
  const groups = new Map();
  for (const edge of edges) {
    // Resolve crossings within the same family so calls/imports don't share a lane.
    const family = wireFamily(edge.edge.type);
    const key = `${edge.b.x >= edge.a.x ? 'forward' : 'backward'}:${family}`;
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
function wireFamily(type) {
  return CONTEXT_TYPES.has(type) ? 'context' : 'flow';
}
/** Calls / imports share a corridor with only a slight parallel offset. */
function familyLaneBias(type) {
  return CONTEXT_TYPES.has(type) ? 6 : -6;
}
function moduleBusPath(a, b, spread, cross, backwards) {
  const lanePad = 34 + Math.min(46, Math.abs(cross) * .55);
  // Always leave right / arrive left — even when the bus runs backwards.
  const sourceLaneX = a.x + lanePad;
  const targetLaneX = b.x - lanePad;
  const midY = (a.y + b.y) / 2 + cross + spread * .18;
  return `M ${a.x} ${a.y} C ${sourceLaneX} ${a.y}, ${sourceLaneX} ${midY}, ${(sourceLaneX + targetLaneX) / 2} ${midY} C ${targetLaneX} ${midY}, ${targetLaneX} ${b.y}, ${b.x} ${b.y}`;
}
/** Out ports leave RIGHT, in ports arrive from the LEFT.
 *  Endpoints lock to exact port centers; spread/cross only bend the mid curve. */
function directedWirePath(a, b, spread = 0, cross = 0, family = 'flow') {
  const y0 = a.y;
  const y1 = b.y;
  const dx = b.x - a.x;
  // Tiny family lift so imports track calls on nearly the same path.
  const familyY = family === 'context' ? 5 : -5;
  const familyBow = family === 'context' ? 8 : 0;
  const midLift = familyY + spread * .08 + cross * .35;

  // Backwards: compact U-loop that still exits right and enters left.
  if (dx < 0) {
    const bow = Math.max(32, Math.min(68, 36 + Math.abs(dx) * .18 + Math.abs(cross) * .2)) + familyBow;
    const midY = (y0 + y1) / 2 + midLift
      + (Math.abs(y0 - y1) < 24 ? (cross >= 0 ? bow * .3 : -bow * .3) : 0);
    const right = Math.max(a.x, b.x) + bow;
    const left = Math.min(a.x, b.x) - bow;
    const midX = (a.x + b.x) / 2;
    return `M ${a.x} ${y0} C ${a.x + bow * .55} ${y0}, ${right} ${midY}, ${midX} ${midY} C ${left} ${midY}, ${b.x - bow * .55} ${y1}, ${b.x} ${y1}`;
  }

  // Close but forward: short directed cubic (no wide loop).
  if (dx < 72) {
    const reach = Math.min(Math.max(dx * .42, 18), 36) + (family === 'context' ? 4 : 0);
    return `M ${a.x} ${y0} C ${a.x + reach} ${y0 + midLift * .55}, ${b.x - reach} ${y1 + midLift * .55}, ${b.x} ${y1}`;
  }

  // Normal forward span — classic soft cubic, exit right / enter left.
  const reach = Math.min(Math.max(dx * .4, 48), 120) + (family === 'context' ? 10 : 0);
  return `M ${a.x} ${y0} C ${a.x + reach} ${y0 + midLift}, ${b.x - reach} ${y1 + midLift}, ${b.x} ${y1}`;
}
function drawEdges() {
  scene.querySelectorAll('.connected-port').forEach(port => port.classList.remove('connected-port'));
  scene.querySelectorAll('.frame.trace-lit').forEach(el => el.classList.remove('trace-lit'));
  const liveEdges = activeTraceEdges();
  const liveNodes = activeTraceNodes();
  const previewing = !!hoverPreviewTrace();
  const keep = new Set();
  if (!liveEdges.size) {
    wires.replaceChildren();
    return;
  }
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
  // Fan within the same endpoint pair; call+import share one corridor key.
  const pairCounts = new Map();
  rendered.forEach(({ edge }) => {
    const key = `${edge.from}:${edge.to}:${wireFamily(edge.type)}`;
    pairCounts.set(key, (pairCounts.get(key) || 0) + 1);
  });
  const pairSeen = new Map();
  const corridorCounts = new Map();
  const corridorSeen = new Map();
  const corridorKeyFor = (a, b) => {
    const ax = Math.round(a.x / 40);
    const bx = Math.round(b.x / 40);
    const ay = Math.round(a.y / 48);
    const by = Math.round(b.y / 48);
    // No family in key — imports track the same path as calls, offset only.
    return `${ax}:${bx}:${ay}:${by}`;
  };
  rendered.forEach(({ a, b }) => {
    const key = corridorKeyFor(a, b);
    corridorCounts.set(key, (corridorCounts.get(key) || 0) + 1);
  });
  rendered.forEach(({ edge, index, a, b }) => {
    markEndpoint(edge.from, 'out'); markEndpoint(edge.to, 'in');
    const family = wireFamily(edge.type);
    const pairKey = `${edge.from}:${edge.to}:${family}`;
    const pairIndex = pairSeen.get(pairKey) || 0;
    pairSeen.set(pairKey, pairIndex + 1);
    const total = pairCounts.get(pairKey) || 1;
    const cKey = corridorKeyFor(a, b);
    const cIndex = corridorSeen.get(cKey) || 0;
    corridorSeen.set(cKey, cIndex + 1);
    const cTotal = corridorCounts.get(cKey) || 1;
    const pairSpread = (pairIndex - (total - 1) / 2) * Math.min(10, Math.max(5, 24 / total));
    const corridorSpread = cTotal > 1
      ? (cIndex - (cTotal - 1) / 2) * Math.min(8, Math.max(5, 16 / cTotal))
      : 0;
    const spread = pairSpread + corridorSpread + familyLaneBias(edge.type);
    const cross = (crossOffsets.get(edge.id) || 0) * 0.5 + (family === 'context' ? 3 : -3);
    const pathData = directedWirePath(a, b, spread, cross, family);
    const wireKey = edge.id;
    keep.add(wireKey);
    let path = wires.querySelector(`[data-wire="${CSS.escape(wireKey)}"]`);
    const origin = originTintForEdge(edge);
    let dialect = '';
    if (traceDialects) {
      const fromFile = fileOf(node(edge.from));
      const toFile = fileOf(node(edge.to));
      const hot = (fromFile && recentFor(fromFile)) || (toFile && recentFor(toFile));
      const orphaned = fromFile?.orphan || toFile?.orphan;
      dialect = orphaned ? 'dialect-removed' : hot ? 'dialect-live' : 'dialect-unreviewed';
    }
    const cls = `wire ${traceMode ? 'moving' : 'static'} ${edge.type} flow-stage wire-${family} ${previewing ? 'preview' : 'committed'} ${dialect}`.trim();
    if (!path) {
      path = document.createElementNS('http://www.w3.org/2000/svg', 'path');
      path.setAttribute('data-wire', wireKey);
      path.append(Object.assign(document.createElementNS('http://www.w3.org/2000/svg', 'title'), { textContent: `${edge.type}: ${edge.evidence}` }));
      wires.append(path);
    }
    // Update geometry in place so dash animation doesn't restart every frame.
    if (path.getAttribute('d') !== pathData) path.setAttribute('d', pathData);
    if (path.getAttribute('class') !== cls) path.setAttribute('class', cls);
    if (origin) {
      path.style.stroke = origin;
      path.style.setProperty('--wire', origin);
    } else {
      path.style.removeProperty('stroke');
      path.style.removeProperty('--wire');
    }
    path.style.setProperty('--delay', `${index * -0.15}s`);
    const title = path.querySelector('title');
    if (title) title.textContent = `${edge.type}: ${edge.evidence}`;
  });
  [...wires.querySelectorAll('[data-wire]')].forEach(path => {
    if (!keep.has(path.getAttribute('data-wire'))) path.remove();
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
function destinationTintForEdge(edge) {
  const to = node(edge.to);
  if (!to) return null;
  if (to.kind === 'folder') return folderTint(to);
  const file = fileOf(to) || (to.kind === 'file' ? to : null);
  if (file) return fileTint(file);
  return null;
}
function itemTint(item) {
  if (!item) return null;
  if (item.kind === 'folder') return folderTint(item);
  const file = fileOf(item) || (item.kind === 'file' ? item : null);
  return file ? fileTint(file) : null;
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
      // Moving into a parent/sibling frame: transfer hover (parent never gets pointerenter).
      const next = event.relatedTarget?.closest?.('.frame.float');
      if (next && scene.contains(next)) {
        clearTimeout(hoverTimer);
        setHover(next.dataset.moduleBox || next.dataset.id || next.dataset.hover);
        return;
      }
      clearTimeout(hoverTimer);
      hoverTimer = setTimeout(() => setHover(null), 60);
    });
  });
}
function point(id, side) {
  const element = endpointHost(id); if (!element) return null;
  const worldRect = world.getBoundingClientRect();
  const rect = element.getBoundingClientRect();
  if (id.startsWith('source:') || id.startsWith('import:')) {
    return { x: ((side === 'out' ? rect.right : rect.left) - worldRect.left) / canvas.scale, y: (rect.top - worldRect.top + rect.height / 2) / canvas.scale };
  }
  const host = element.closest?.('.frame') || element;
  const port = host.querySelector(`[data-port-for="${CSS.escape(endpointPortId(id))}"][data-port-side="${side}"]`);
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
function applyCanvas() {
  world.style.transform = `translate(${canvas.x}px,${canvas.y}px) scale(${canvas.scale})`;
  scheduleMinimap();
  // Pan/zoom changes the viewfinder — wake park gravity for long-distance strays.
  scheduleGravityDrift(90);
}
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
function smoothFocusSelection({ duration = 1900 } = {}) {
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
function playAgentEditReveal(path, { theater = false } = {}) {
  if (!autoRevealChanges || !graph || !path) return;
  const normalized = String(path).replaceAll('\\', '/');
  const file = fileByPath(normalized);
  if (!file) return;
  if (agentRevealPath && agentRevealPath !== normalized) dismissAgentEditReveal();
  clearTimeout(agentRevealTimer);
  agentRevealPath = normalized;
  agentRevealExpandedId = file.id;
  expandAncestors(file);
  expandedFiles.add(file.id);
  selectedId = file.id;
  layoutAnchorFileId = file.id;
  focusedFileId = file.id;
  flowMode = true;
  rebuildTrace();
  render();
  updateInspector();
  requestAnimationFrame(() => {
    smoothFocusSelection({ duration: 2000 });
    applyEditAnimBurst(file.id);
    const burstKind = editAnimStyle === 'hearts' ? 'hearts' : editAnimStyle === 'spark' ? 'sparks' : 'sparks';
    if (editAnimStyle !== 'lines' && editAnimStyle !== 'hearts' && editAnimStyle !== 'fire') {
      spawnParticleBurst(scene.querySelector(`[data-id="${CSS.escape(file.id)}"]`), burstKind);
    }
    if (theater) playEditTheater(file).catch(() => {});
    else $('#diff-panel')?.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
  });
  agentRevealTimer = setTimeout(() => {
    if (agentRevealPath !== normalized) return;
    dismissAgentEditReveal();
  }, Math.max(agentRevealDwellMs, theater ? 9000 : agentRevealDwellMs));
}
function applyEditAnimBurst(fileId) {
  const el = scene.querySelector(`.frame-file[data-id="${CSS.escape(fileId)}"]`);
  if (!el || document.body.classList.contains('reduce-motion')) return;
  el.classList.remove('edit-anim-burst', 'edit-anim-lines-on', 'edit-anim-hearts-on', 'edit-anim-fire-on');
  el.querySelector('.edit-anim-lines')?.remove();
  el.querySelector('.edit-anim-hearts')?.remove();
  el.querySelector('.edit-anim-fire')?.remove();
  void el.offsetWidth;
  el.classList.add('edit-anim-burst');
  if (editAnimStyle === 'hearts') {
    mountEditHeartsAnim(el);
    spawnParticleBurst(el, 'hearts');
  } else if (editAnimStyle === 'fire') {
    mountEditFireAnim(el);
    spawnParticleBurst(el, 'fire');
  } else if (editAnimStyle === 'lines') {
    mountEditLinesAnim(el);
    spawnParticleBurst(el, 'fire');
  }
  clearTimeout(el._editAnimTimer);
  el._editAnimTimer = setTimeout(() => {
    el.classList.remove('edit-anim-burst', 'edit-anim-lines-on', 'edit-anim-hearts-on', 'edit-anim-fire-on');
    el.querySelector('.edit-anim-lines')?.remove();
    el.querySelector('.edit-anim-hearts')?.remove();
    el.querySelector('.edit-anim-fire')?.remove();
  }, editAnimStyle === 'lines' ? 3200 : editAnimStyle === 'hearts' || editAnimStyle === 'fire' ? 2600 : 1800);
}
function mountEditLinesAnim(el) {
  if (!el) return;
  el.classList.add('edit-anim-lines-on');
  const strip = document.createElement('div');
  strip.className = 'edit-anim-lines';
  strip.setAttribute('aria-hidden', 'true');
  const rows = [
    { w: 92 }, { w: 68 }, { w: 84 }, { w: 46 },
    { w: 76 }, { w: 58 }, { w: 88 }, { w: 52 },
    { w: 60 }, { w: 90 }, { w: 45 }
  ];
  strip.innerHTML = `
    <div class="edit-lines-beacon"></div>
    <div class="edit-lines-scroll">
      <em class="edit-lines-label">editing</em>
      ${rows.map((row, i) => `<span style="--w:${row.w}%;--i:${i}"></span>`).join('')}
    </div>
  `;
  el.appendChild(strip);
}
function mountEditHeartsAnim(el) {
  if (!el) return;
  el.classList.add('edit-anim-hearts-on');
  const layer = document.createElement('div');
  layer.className = 'edit-anim-hearts';
  layer.setAttribute('aria-hidden', 'true');
  const glyphs = ['♥', '♡', '♥', '♡', '♥', '♡', '♥', '♡', '♥', '♡', '♥', '♡'];
  const parts = ['<div class="edit-anim-center-glyph" style="color: #ff7eb6; text-shadow: 0 0 20px #e83e8c;">♥</div>'];
  glyphs.forEach((g, i) => {
    const angle = (i / glyphs.length) * Math.PI * 2;
    const dist = 30 + Math.random() * 40;
    const hx = (Math.cos(angle) * dist).toFixed(1) + 'px';
    const hy = (Math.sin(angle) * dist - 20).toFixed(1) + 'px';
    const delay = (i * 0.1).toFixed(2) + 's';
    const dur = (1.2 + (i % 4) * 0.22).toFixed(2) + 's';
    const scale = (0.5 + Math.random() * 0.5).toFixed(2);
    parts.push(`<span style="--hx:${hx};--hy:${hy};--hd:${delay};--hs:${scale};--hdur:${dur}">${g}</span>`);
  });
  layer.innerHTML = parts.join('');
  el.appendChild(layer);
}
function mountEditFireAnim(el) {
  if (!el) return;
  el.classList.add('edit-anim-fire-on');
  const layer = document.createElement('div');
  layer.className = 'edit-anim-fire';
  layer.setAttribute('aria-hidden', 'true');
  const glyphs = ['●', '○', '•', '◦', '°', '●', '○', '•', '◦', '°', '●', '○'];
  const parts = ['<div class="edit-anim-center-glyph fire-glyph" style="color: #ff9f1c; text-shadow: 0 0 20px #ff6b35;">●</div>'];
  glyphs.forEach((g, i) => {
    const angle = (i / glyphs.length) * Math.PI * 2;
    const dist = 30 + Math.random() * 50;
    const hx = (Math.cos(angle) * dist).toFixed(1) + 'px';
    const hy = (Math.sin(angle) * dist - 30).toFixed(1) + 'px';
    const delay = (i * 0.08).toFixed(2) + 's';
    const dur = (1.0 + (i % 4) * 0.3).toFixed(2) + 's';
    const scale = (0.4 + Math.random() * 0.8).toFixed(2);
    parts.push(`<span style="--hx:${hx};--hy:${hy};--hd:${delay};--hs:${scale};--hdur:${dur}">${g}</span>`);
  });
  layer.innerHTML = parts.join('');
  el.appendChild(layer);
}
function syncEditAnim() {
  document.body.dataset.editAnim = editAnimStyle;
  $('#edit-anim-grid')?.querySelectorAll('[data-edit-anim]').forEach(button => {
    button.classList.toggle('active', button.dataset.editAnim === editAnimStyle);
  });
}
function directManipulation() {
  board.classList.add('panning', 'zooming');
  clearTimeout(directManipulationTimer);
  directManipulationTimer = setTimeout(() => board.classList.remove('panning', 'zooming'), 140);
}
function scheduleDraw() { if (drawFrame) return; drawFrame = requestAnimationFrame(() => { drawFrame = 0; drawEdges(); }); }
function animateReflowEdges(duration = 900) {
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
  // Titles / pins / flow entry stay clickable - never start a drag from them.
  const onBar = event => event.target.closest('.frame-bar')
    && !event.target.closest('button,a,[data-pin],[data-open-flow],[data-open-file-flow],.frame-title,.fn-kind,.fn-flow-hint');
  const applyDragVisual = () => {
    raf = 0;
    if (!drag) return;
    const { dx, dy } = drag;
    if (drag.nested && drag.parentId) {
      // Pure translate while held — never encapsulate/shift origin mid-drag
      // (that expanded folders leftward and yanked siblings + selection).
      let x = drag.baseLeft + dx;
      let y = drag.baseTop + dy;
      frame.style.translate = `${x - drag.baseLeft}px ${y - drag.baseTop}px`;
      frame.style.setProperty('--ox', `${x - drag.baseLeft}px`);
      frame.style.setProperty('--oy', `${y - drag.baseTop}px`);
    } else {
      // Free island drag: no collision while held; neighbors yield only after drop.
      markDropTarget(drag.pointerX, drag.pointerY, drag.islandId);
      const value = { x: drag.ox + dx, y: drag.oy + dy };
      offsets.set(drag.islandId, value);
      drag.islandEl.style.translate = `${value.x}px ${value.y}px`;
      drag.islandEl.style.setProperty('--ox', `${value.x}px`);
      drag.islandEl.style.setProperty('--oy', `${value.y}px`);
    }
    // Skip wire redraw while dragging - continuous SVG rebuilds cause stutter.
  };
  frame.addEventListener('pointerdown', event => {
    if (event.button !== 0 || !onBar(event)) return;
    event.stopPropagation();
    clearTimeout(gravityTimer);
    cancelTraceAlign();
    cancelSoftSettle();
    const islandId = dragIslandId(id);
    const islandEl = scene.querySelector(`[data-drag-id="${CSS.escape(islandId)}"]`) || frame;
    // Kill in-flight FLIP / jelly so grab doesn't fight a mid-transition transform.
    islandEl.classList.remove('flipping', 'jelly-wobble', 'calm-in');
    frame.classList.remove('flipping', 'jelly-wobble', 'calm-in');
    islandEl.style.transform = '';
    frame.style.transform = '';
    islandEl.style.transition = 'none';
    frame.style.transition = 'none';
    const current = offsets.get(islandId) || { x: 0, y: 0 };
    const parentId = parentCanvasId(id);
    const parentEl = parentId ? scene.querySelector(`[data-drag-id="${CSS.escape(parentId)}"]`) : null;
    const local = localOffsets.get(id) || { x: 0, y: 0 };
    const canvasEl = parentEl?.querySelector(':scope > .frame-canvas');
    const seat = nestedSeats.get(id);
    const baseLeft = seat?.x ?? (parseFloat(frame.style.left) || 0);
    const baseTop = seat?.y ?? (parseFloat(frame.style.top) || 0);
    drag = {
      id, islandId, islandEl, parentId, parentEl, canvasEl,
      nested: islandId !== id,
      parentBaseW: parentEl?.offsetWidth || 0,
      canvasBaseH: canvasEl?.offsetHeight || 0,
      baseLeft, baseTop,
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
    if (drag.nested) {
      parentEl?.classList.add('nest-drop-active');
      canvasEl?.classList.add('nest-canvas-active');
      frame.classList.add('nest-dragging');
      if (parentEl) parentEl.style.transition = 'none';
      if (canvasEl) canvasEl.style.transition = 'none';
    }
    app.classList.add('dragging');
    wires.style.opacity = '.2';
    frame.setPointerCapture(event.pointerId);
  });
  frame.addEventListener('pointermove', event => {
    if (!drag) return;
    const dx = (event.clientX - drag.x) / canvas.scale;
    const dy = (event.clientY - drag.y) / canvas.scale;
    drag.moved ||= Math.abs(dx) + Math.abs(dy) > 10;
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
    const islandEl = drag.islandEl;
    const parentEl = drag.parentEl;
    const canvasEl = drag.canvasEl;
    const baseLeft = drag.baseLeft;
    const baseTop = drag.baseTop;
    clearDropTargets();
    clearNestDragChrome();
    wires.style.opacity = '';
    if (drag.moved) {
      frame.dataset.dragged = String(Date.now());
      clearSeatLock();
      if (!nested) {
        pinnedLayout.add(islandId);
        // User seat wins over focus-rearrange memory.
        traceArranged.delete(islandId);
      }
      if (nested && parentId) {
        // Keep raw seat (including past top/left) — softSettle grows the folder there.
        const dropX = baseLeft + dx;
        const dropY = baseTop + dy;
        userArranged.add(draggedId);
        nestedSeats.set(draggedId, {
          x: dropX,
          y: dropY
        });
        localOffsets.delete(draggedId);
        frame.style.left = `${dropX}px`;
        frame.style.top = `${dropY}px`;
        frame.style.translate = '0px 0px';
        frame.style.setProperty('--ox', '0px');
        frame.style.setProperty('--oy', '0px');
        void frame.offsetWidth;
        if (islandEl) void islandEl.offsetWidth;
        islandEl?.classList.remove('dragging');
        frame.classList.remove('dragging', 'nest-dragging');
        frame.style.transition = '';
        islandEl.style.transition = '';
        if (parentEl) parentEl.style.transition = '';
        if (canvasEl) canvasEl.style.transition = '';
        app.classList.remove('dragging');
        draggingTraceAnchorId = null;
        drag = null;
        softSettleNested(draggedId, parentId, { duration: 720 });
        scheduleDraw();
        scheduleGravityDrift(1100);
        return;
      }
      // Keep the dropped island where released; softly push neighbors aside.
      const value = { x: drag.ox + dx, y: drag.oy + dy };
      offsets.set(islandId, value);
      islandEl.style.translate = `${value.x}px ${value.y}px`;
      islandEl.style.setProperty('--ox', `${value.x}px`);
      islandEl.style.setProperty('--oy', `${value.y}px`);
      void islandEl.offsetWidth;
      void frame.offsetWidth;
      islandEl.classList.remove('dragging');
      frame.classList.remove('dragging');
      frame.style.transition = '';
      islandEl.style.transition = '';
      app.classList.remove('dragging');
      draggingTraceAnchorId = null;
      drag = null;
      softSettleNeighbors(islandId, islandEl, { duration: 720 });
      scheduleDraw();
      renderMinimap();
      scheduleGravityDrift(1400);
      return;
    }
    void frame.offsetWidth;
    if (islandEl) void islandEl.offsetWidth;
    islandEl?.classList.remove('dragging');
    frame.classList.remove('dragging', 'nest-dragging');
    frame.style.transition = '';
    islandEl.style.transition = '';
    app.classList.remove('dragging');
    draggingTraceAnchorId = null;
    drag = null;
    scheduleDraw();
    renderMinimap();
    scheduleGravityDrift(400);
  };
  frame.addEventListener('pointerup', end);
  frame.addEventListener('pointercancel', end);
}
function quietLayoutMotion(ms = 160) {
  app.classList.add('layout-quiet');
  clearTimeout(quietLayoutMotion._t);
  quietLayoutMotion._t = setTimeout(() => app.classList.remove('layout-quiet'), ms);
}
/** Drop stale nested seats so a fresh expand packs modules on the shelf. */
function clearNestedSeatsFor(file) {
  if (!file) return;
  for (const mod of modules(file)) {
    userArranged.delete(mod.id);
    nestedSeats.delete(mod.id);
    localOffsets.delete(mod.id);
  }
}
/**
 * Prepare for focus/trace align. Opens keep FLIP + size morph — never snap.
 */
function beginFocusAlignMotion({ animateOpen = true } = {}) {
  cancelTraceAlign();
  cancelSoftSettle();
  clearSeatLock();
  // Only strip mid-flight FLIP when something is actually flipping.
  if (scene?.querySelector?.('.frame.flipping, .frame.size-morph')) stripFlipTransforms();
  alignMotionPending = true;
  if (animateOpen) {
    skipFlipOnce = false;
    app.classList.remove('layout-quiet');
    clearTimeout(quietLayoutMotion._t);
  } else {
    // Re-focus: skip FLIP, but do NOT quiet CSS — that made the rearranger look dead.
    skipFlipOnce = true;
  }
  scheduleGravityDrift(animateOpen ? 1300 : 700);
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
  const opening = expand && folder.id !== displayRoot()?.id && !expandedFolders.has(folder.id);
  // Only morph when actually opening — re-focus must not FLIP then constellation.
  beginFocusAlignMotion({ animateOpen: opening });
  if (opening) {
    clearSeatLock();
    markExpandAnchor(folder.id);
    pinNestedSeatFromDom(folder.id);
    pendingAlignAfterMorph = 160;
  }
  activateFocus(folder);
  layoutAnchorFileId = folder.id;
  if (expand && folder.id !== displayRoot()?.id) {
    expandedFolders.add(folder.id);
    ensureTopLevelFoldersOpen();
  }
  selectItem(folder.id, { record: false });
  flowMode = true;
  rebuildTrace();
  render();
  updateInspector();
  requestAnimationFrame(() => {
    animateReflowEdges(opening ? 1100 : 700);
    pulseSelection();
    if (!opening) scheduleTraceAlign(120);
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
  const opening = expand && !expandedFiles.has(file.id);
  beginFocusAlignMotion({ animateOpen: opening });
  if (opening) {
    clearSeatLock();
    markExpandAnchor(file.id);
    pinNestedSeatFromDom(file.id);
    clearNestedSeatsFor(file);
    pendingAlignAfterMorph = 160;
  }
  activateFocus(file);
  layoutAnchorFileId = file.id;
  if (expand) expandedFiles.add(file.id);
  selectItem(file.id, { record: false });
  flowMode = true;
  rebuildTrace();
  render();
  updateInspector();
  requestAnimationFrame(() => {
    animateReflowEdges(opening ? 1100 : 700);
    pulseSelection();
    if (!opening) scheduleTraceAlign(120);
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
function flowCodeLinesHtml(file, start, end, hitStart, hitEnd) {
  const lines = (file?.meta?.source || '').split('\n');
  if (!lines.length || start > end) {
    return '<span class="flow-line"><i>-</i><code>No source</code></span>';
  }
  const from = Math.max(1, start);
  const to = Math.min(lines.length, end);
  return lines.slice(from - 1, to).map((text, index) => {
    const line = from + index;
    const hit = hitStart != null && line >= hitStart && line <= (hitEnd ?? hitStart);
    const edgeHit = hit && hitStart === hitEnd && line === hitStart;
    return `<span class="flow-line${hit ? ' hit' : ''}${edgeHit ? ' hit-edge' : ''}"><i>${line}</i><code>${highlightLine(text, file?.language)}</code></span>`;
  }).join('');
}
/** Line window for a flow card — full relevant source; panel scroll handles overflow. */
function flowCodeRanges(item, file, edge) {
  const lines = (file?.meta?.source || '').split('\n');
  const total = lines.length;
  let hitStart = null;
  let hitEnd = null;
  let start = 1;
  let end = Math.min(total, 120);
  if (item.kind === 'module' && item.loc) {
    start = item.loc.start;
    end = Math.min(total, Math.max(start, item.loc.end || start));
  }
  if (edge?.line) {
    const line = Math.max(1, Math.min(total, edge.line));
    hitStart = line;
    hitEnd = line;
    if (item.kind === 'module' && item.loc) {
      start = item.loc.start;
      end = Math.min(total, Math.max(start, item.loc.end || start));
    } else {
      start = Math.max(1, line - 40);
      end = Math.min(total, line + 80);
    }
  }
  if (!total) return { start: 1, end: 1, hitStart, hitEnd };
  return { start, end, hitStart, hitEnd };
}
function flowModuleRailHtml(file) {
  if (!file || file.kind !== 'file') return '';
  const mods = modules(file).slice(0, 28);
  if (!mods.length) return '';
  return `<div class="flow-module-rail" role="list" aria-label="Modules in file">
    ${mods.map(mod => `<button type="button" class="flow-mod-chip" data-flow-mod="${mod.id}" title="Open ${escape(mod.label)}() flow">${escape(mod.label)}()</button>`).join('')}
  </div>`;
}
function codeBlockHtml(item, { edge, role } = {}) {
  const file = fileOf(item) || (item.kind === 'file' ? item : null);
  const ranges = flowCodeRanges(item, file, edge);
  const code = flowCodeLinesHtml(file, ranges.start, ranges.end, ranges.hitStart, ranges.hitEnd);
  const glyph = file ? fileGlyph(file) : { g: '·', c: 'var(--muted)' };
  const title = item.kind === 'module' ? `${item.label}()` : item.label;
  const meta = edge
    ? `${edge.type}${edge.line ? ` · L${edge.line}` : ''}`
    : (item.kind === 'module' ? `L${ranges.start}-${ranges.end}` : file?.path || '');
  const tint = itemTint(item) || glyph.c || 'var(--green)';
  const originTint = edge ? (originTintForEdge(edge) || tint) : tint;
  const destTint = edge ? (destinationTintForEdge(edge) || tint) : tint;
  const edgeTone = role === 'from' ? originTint : role === 'to' ? destTint : tint;
  const sideTag = role === 'from' ? 'OUT' : role === 'to' ? 'IN' : 'HERE';
  const moduleRail = role === 'here' && item.kind === 'file' ? flowModuleRailHtml(item) : '';
  return `<article class="flow-card ${role || ''}" data-flow-jump="${item.id}" data-flow-role="${role || ''}" data-flow-edge="${edge?.id || ''}" style="--flow-tint:${escape(edgeTone)};--flow-origin:${escape(originTint)};--flow-dest:${escape(destTint)}">
    <div class="flow-card-head">
      <span class="file-glyph" style="--glyph:${glyph.c}">${escape(glyph.g)}</span>
      <b>${escape(title)}</b>
      <span class="flow-edge-meta">${edge ? `<i class="flow-side-tag ${role === 'from' ? 'out' : 'in'}">${sideTag}</i>${escape(meta)}` : escape(meta)}</span>
    </div>
    <small>${escape(file?.path || item.path || '')}</small>
    ${moduleRail}
    <div class="flow-code-wrap">
      <pre class="flow-code">${code}</pre>
    </div>
  </article>`;
}
function bindFlowCodeBlocks(root, onResize) {
  root?.querySelectorAll('.flow-code').forEach(pre => {
    pre.addEventListener('wheel', event => event.stopPropagation(), { passive: true });
    pre.addEventListener('click', event => event.stopPropagation());
    pre.addEventListener('scroll', () => onResize?.(), { passive: true });
    const hit = pre.querySelector('.flow-line.hit-edge, .flow-line.hit');
    if (hit) requestAnimationFrame(() => hit.scrollIntoView({ block: 'center', behavior: 'auto' }));
  });
  root?.querySelectorAll('[data-flow-mod]').forEach(btn => {
    btn.addEventListener('click', event => {
      event.preventDefault();
      event.stopPropagation();
      const mod = node(btn.dataset.flowMod);
      if (mod) openFlowOverlay(mod);
    });
  });
}
function flowNeighbors(focus) {
  const seeds = new Set(sourceSeeds(focus));
  const upstream = [];
  const downstream = [];
  // Respect the ribbon edge toggles so the three planes match the map.
  for (const edge of edgeTypes()) {
    if (seeds.has(edge.to) && !seeds.has(edge.from)) {
      const other = node(edge.from);
      if (other && (other.kind === 'file' || other.kind === 'module')) upstream.push({ edge, other });
    }
    if (seeds.has(edge.from) && !seeds.has(edge.to)) {
      const other = node(edge.to);
      if (other && (other.kind === 'file' || other.kind === 'module')) downstream.push({ edge, other });
    }
  }
  const rank = type => ({ inherits: 0, calls: 1, dataflow: 2, events: 3, imports: 4, references: 5, reexports: 6 }[type] ?? 9);
  const dedupe = list => {
    const best = new Map();
    for (const entry of list) {
      const key = entry.other.id;
      const prev = best.get(key);
      if (!prev || rank(entry.edge.type) < rank(prev.edge.type)) best.set(key, entry);
    }
    return [...best.values()]
      .sort((a, b) => rank(a.edge.type) - rank(b.edge.type) || (a.other.label || '').localeCompare(b.other.label || ''))
      .slice(0, 16);
  };
  return { upstream: dedupe(upstream), downstream: dedupe(downstream) };
}
function drawFlowOverlayWires(upstream, downstream, focusItem = null) {
  const svg = $('#flow-wires');
  const body = svg?.closest('.flow-body');
  if (!svg || !body) return;
  const bodyRect = body.getBoundingClientRect();
  const focusCard = $('#flow-focus')?.querySelector('.flow-card.here');
  if (!focusCard) { svg.innerHTML = ''; return; }
  const cardRect = focusCard.getBoundingClientRect();
  // Gutter docks just outside the focus card.
  const fxIn = cardRect.left - bodyRect.left - 6;
  const fxOut = cardRect.right - bodyRect.left + 6;
  const focusTint = itemTint(focusItem) || 'var(--green)';
  const parts = ['<defs></defs>'];
  let gradN = 0;
  const clampCardY = (card, preferred) => {
    const rect = card.getBoundingClientRect();
    // Stay in the upper chrome band so nodes never drop under the code body.
    const top = rect.top - bodyRect.top + 22;
    const bot = rect.top - bodyRect.top + Math.min(72, Math.max(40, rect.height * 0.22));
    return Math.min(Math.max(preferred, top), bot);
  };
  const cardDockY = card => {
    const rect = card.getBoundingClientRect();
    const head = card.querySelector('.flow-card-head');
    const headRect = head?.getBoundingClientRect();
    // Prefer the title row — hit lines inside scrolled <pre> can sit below the card.
    const midY = headRect
      ? headRect.top - bodyRect.top + headRect.height * 0.5
      : rect.top - bodyRect.top + 36;
    return clampCardY(card, midY);
  };
  const fy = cardDockY(focusCard);
  const stiffLink = (card, side, entry, railIndex = 0, railCount = 1) => {
    if (!card || !entry) return;
    const rect = card.getBoundingClientRect();
    const edge = entry.edge;
    const familyLift = CONTEXT_TYPES.has(edge?.type) ? 16 : -12;
    const otherY = cardDockY(card) + familyLift;
    // Fan focus docks slightly so many rails don't stack on one point.
    const spread = (railIndex - (railCount - 1) / 2) * Math.min(10, 56 / Math.max(railCount, 1));
    const focusY = clampCardY(focusCard, fy + spread + familyLift * 0.45);
    let x1, y1, x2, y2;
    if (side === 'from') {
      // Upstream card OUT → focus IN
      x1 = rect.right - bodyRect.left + 7;
      y1 = otherY;
      x2 = fxIn;
      y2 = focusY;
    } else {
      // Focus OUT → downstream card IN  (was wrongly using dest Y at both ends)
      x1 = fxOut;
      y1 = focusY;
      x2 = rect.left - bodyRect.left - 7;
      y2 = otherY;
    }
    const dx = x2 - x1;
    const c1x = x1 + dx * 0.28;
    const c2x = x1 + dx * 0.72;
    const other = entry.other;
    const kind = escape(edge?.type || 'calls');
    const originTint = side === 'from'
      ? (originTintForEdge(edge) || itemTint(other) || focusTint)
      : (originTintForEdge(edge) || focusTint);
    const destTint = side === 'from'
      ? (destinationTintForEdge(edge) || focusTint)
      : (destinationTintForEdge(edge) || itemTint(other) || focusTint);
    const gid = `flow-grad-${gradN++}`;
    parts[0] = parts[0].replace('</defs>',
      `<linearGradient id="${gid}" gradientUnits="userSpaceOnUse" x1="${x1}" y1="${y1}" x2="${x2}" y2="${y2}"><stop offset="0%" stop-color="${originTint}"/><stop offset="100%" stop-color="${destTint}"/></linearGradient></defs>`);
    parts.push(`<path class="flow-wire flow-wire-live ${kind}" stroke="url(#${gid})" d="M${x1},${y1} C${c1x},${y1} ${c2x},${y2} ${x2},${y2}" />`);
    parts.push(`<circle class="flow-node origin out" cx="${x1}" cy="${y1}" r="4.5" stroke="${originTint}" fill="${originTint}" fill-opacity="0.22" />`);
    parts.push(`<circle class="flow-node dest in" cx="${x2}" cy="${y2}" r="5" stroke="${destTint}" fill="${destTint}" fill-opacity="0.22" />`);
  };
  const upStack = $('#flow-upstream');
  const downStack = $('#flow-downstream');
  const upById = new Map((upstream || []).map(entry => [entry.other.id, entry]));
  const downById = new Map((downstream || []).map(entry => [entry.other.id, entry]));
  const upCards = [...(upStack?.querySelectorAll('.flow-card') || [])];
  const downCards = [...(downStack?.querySelectorAll('.flow-card') || [])];
  upCards.forEach((card, index) => {
    const entry = upById.get(card.dataset.flowJump) || upstream[index];
    stiffLink(card, 'from', entry, index, upCards.length);
  });
  downCards.forEach((card, index) => {
    const entry = downById.get(card.dataset.flowJump) || downstream[index];
    stiffLink(card, 'to', entry, index, downCards.length);
  });
  const moreLeft = (upstream?.length || 0) >= 16
    || (upStack && (upStack.scrollTop > 8 || upStack.scrollHeight > upStack.clientHeight + 24));
  const moreRight = (downstream?.length || 0) >= 16
    || (downStack && (downStack.scrollTop > 8 || downStack.scrollHeight > downStack.clientHeight + 24));
  if (moreLeft) {
    for (let i = 0; i < 3; i++) {
      const y = fy - 36 + i * 36;
      const x0 = -28;
      const c1x = x0 + (fxIn - x0) * 0.28;
      const c2x = x0 + (fxIn - x0) * 0.72;
      parts.push(`<path class="flow-wire flow-wire-live flow-wire-exit exit-left" stroke="${focusTint}" d="M${x0},${y} C${c1x},${y} ${c2x},${fy} ${fxIn},${fy}" />`);
      parts.push(`<circle class="flow-node in exit" cx="${fxIn}" cy="${fy}" r="3.5" stroke="${focusTint}" fill="${focusTint}" fill-opacity="0.2" />`);
    }
  }
  if (moreRight) {
    const xEnd = bodyRect.width + 28;
    for (let i = 0; i < 3; i++) {
      const y = fy - 36 + i * 36;
      const x1 = fxOut;
      const c1x = x1 + (xEnd - x1) * 0.28;
      const c2x = x1 + (xEnd - x1) * 0.72;
      parts.push(`<path class="flow-wire flow-wire-live flow-wire-exit exit-right" stroke="${focusTint}" d="M${x1},${fy} C${c1x},${fy} ${c2x},${y} ${xEnd},${y}" />`);
      parts.push(`<circle class="flow-node out exit" cx="${x1}" cy="${fy}" r="3.5" stroke="${focusTint}" fill="${focusTint}" fill-opacity="0.2" />`);
    }
  }
  if (upstream?.length || downstream?.length) {
    parts.push(`<circle class="flow-node hub" cx="${(fxIn + fxOut) / 2}" cy="${fy}" r="6.5" stroke="${focusTint}" fill="${focusTint}" fill-opacity="0.28" />`);
  }
  svg.setAttribute('viewBox', `0 0 ${Math.max(1, bodyRect.width)} ${Math.max(1, bodyRect.height)}`);
  svg.innerHTML = parts.join('');
}

function openFlowOverlay(item, { narrative, fromNav = false } = {}) {
  if (!item || !graph) return;
  // Keep files as FILE FLOW (don't silently swap to first module).
  const focus = item;
  const file = fileOf(focus) || (focus.kind === 'file' ? focus : null);
  const { upstream, downstream } = flowNeighbors(focus);
  flowNavCache = { upstream, downstream };
  const dialog = $('#flow-overlay');
  if (!dialog) return;
  cancelTraceAlign();
  cancelSoftSettle();
  stripFlipTransforms();
  skipFlipOnce = true;
  alignMotionPending = false;
  // Maintain back/forward trail for the top nav arrows.
  if (!fromNav) {
    if (flowTrailIndex >= 0 && flowTrail[flowTrailIndex] === focus.id) {
      // same node - keep trail
    } else {
      flowTrail = flowTrail.slice(0, Math.max(0, flowTrailIndex + 1));
      if (flowTrail[flowTrail.length - 1] !== focus.id) flowTrail.push(focus.id);
      flowTrailIndex = flowTrail.length - 1;
    }
  } else if (flowTrail[flowTrailIndex] !== focus.id) {
    const at = flowTrail.indexOf(focus.id);
    if (at >= 0) flowTrailIndex = at;
  }
  $('#flow-kicker').textContent = focus.kind === 'module' ? 'MODULE FLOW' : focus.kind === 'file' ? 'FILE FLOW' : 'CODE FLOW';
  $('#flow-title').textContent = focus.kind === 'module' ? `${focus.label}()` : focus.label;
  $('#flow-path').textContent = file?.path || focus.path || '';
  $('#flow-focus-meta').textContent = focus.kind === 'module'
    ? `lines ${focus.loc?.start || '?'}-${focus.loc?.end || '?'}`
    : focus.kind === 'file'
      ? `${modules(focus).length} modules`
      : `${file ? modules(file).length : 0} modules`;
  const story = narrative || [
    upstream.length ? `${upstream.length} upstream` : 'no upstream',
    downstream.length ? `${downstream.length} downstream` : 'no downstream'
  ].join(' · ');
  const narrativeEl = $('#flow-narrative');
  if (narrativeEl) {
    narrativeEl.hidden = !story;
    narrativeEl.textContent = story;
  }
  $('#flow-upstream').innerHTML = upstream.map(({ edge, other }) => codeBlockHtml(other, { edge, role: 'from' })).join('')
    || '<p class="flow-empty">Nothing feeds into this node with the current edge filters.</p>';
  $('#flow-focus').innerHTML = codeBlockHtml(focus, { role: 'here' });
  $('#flow-downstream').innerHTML = downstream.map(({ edge, other }) => codeBlockHtml(other, { edge, role: 'to' })).join('')
    || '<p class="flow-empty">Nothing consumes this node with the current edge filters.</p>';
  const redrawSoon = () => requestAnimationFrame(() => drawFlowOverlayWires(upstream, downstream, focus));
  bindFlowCodeBlocks(dialog, redrawSoon);
  dialog.querySelectorAll('[data-flow-jump]').forEach(card => {
    card.addEventListener('click', event => {
      if (card.classList.contains('here')) return;
      if (event.target.closest('.flow-code, .flow-code-wrap, .flow-module-rail, .flow-connect, [data-flow-mod]')) return;
      const target = node(card.dataset.flowJump);
      if (!target || target.id === focus.id) return;
      openFlowOverlay(target);
    });
  });
  updateFlowNavButtons();
  // Competing dialogs block showModal - dismiss them first.
  document.querySelectorAll('dialog[open]').forEach(other => {
    if (other === dialog) return;
    try { other.close(); } catch { other.removeAttribute('open'); }
  });
  try {
    if (!dialog.open) dialog.showModal();
  } catch {
    dialog.setAttribute('open', '');
  }
  selectItem(focus.id, { record: false });
  activateFocus(focus);
  if (file) expandedFiles.add(file.id);
  rebuildTrace();
  if (dialog._flowWireAbort) dialog._flowWireAbort.abort();
  dialog._flowWireAbort = new AbortController();
  const { signal } = dialog._flowWireAbort;
  const redraw = () => drawFlowOverlayWires(upstream, downstream, focus);
  // Soft map sync under the glass - never FLIP/align while the overlay owns focus.
  requestAnimationFrame(() => {
    skipFlipOnce = true;
    alignMotionPending = false;
    try { render(); } catch (_) { /* keep overlay open */ }
    animateReflowEdges(700);
    requestAnimationFrame(() => {
      redraw();
      dialog.querySelectorAll('.flow-stack').forEach(el => {
        el.addEventListener('scroll', redraw, { passive: true, signal });
      });
      dialog.querySelectorAll('.flow-columns').forEach(el => {
        el.addEventListener('scroll', redraw, { passive: true, signal });
      });
      window.addEventListener('resize', redraw, { passive: true, signal });
    });
  });
}
function flowNavTargetLabel(item) {
  if (!item) return '—';
  return item.kind === 'module' ? `${item.label}()` : item.label;
}
function flowNavPeek(dir) {
  if (dir < 0) {
    if (flowTrailIndex > 0) {
      const target = node(flowTrail[flowTrailIndex - 1]);
      return { kind: 'Back', item: target, via: 'trail' };
    }
    const up = flowNavCache.upstream?.[0]?.other;
    return { kind: 'Upstream', item: up || null, via: 'edge' };
  }
  if (flowTrailIndex >= 0 && flowTrailIndex < flowTrail.length - 1) {
    const target = node(flowTrail[flowTrailIndex + 1]);
    return { kind: 'Forward', item: target, via: 'trail' };
  }
  const down = flowNavCache.downstream?.[0]?.other;
  return { kind: 'Downstream', item: down || null, via: 'edge' };
}
function updateFlowNavButtons() {
  const prev = $('#flow-nav-prev');
  const next = $('#flow-nav-next');
  if (!prev || !next) return;
  const left = flowNavPeek(-1);
  const right = flowNavPeek(1);
  prev.disabled = !left.item;
  next.disabled = !right.item;
  const prevKind = $('#flow-nav-prev-kind');
  const prevLabel = $('#flow-nav-prev-label');
  const nextKind = $('#flow-nav-next-kind');
  const nextLabel = $('#flow-nav-next-label');
  if (prevKind) prevKind.textContent = left.item ? left.kind : 'Upstream';
  if (prevLabel) prevLabel.textContent = left.item ? flowNavTargetLabel(left.item) : 'None';
  if (nextKind) nextKind.textContent = right.item ? right.kind : 'Downstream';
  if (nextLabel) nextLabel.textContent = right.item ? flowNavTargetLabel(right.item) : 'None';
  prev.title = left.item ? `${left.kind}: ${flowNavTargetLabel(left.item)}` : 'No previous';
  next.title = right.item ? `${right.kind}: ${flowNavTargetLabel(right.item)}` : 'No next';
  prev.setAttribute('aria-label', prev.title);
  next.setAttribute('aria-label', next.title);
}
function flowNavStep(dir) {
  if (dir < 0) {
    if (flowTrailIndex > 0) {
      flowTrailIndex -= 1;
      const target = node(flowTrail[flowTrailIndex]);
      if (target) return openFlowOverlay(target, { fromNav: true });
    }
    const up = flowNavCache.upstream?.[0]?.other;
    // Push onto trail so Forward can return.
    if (up) return openFlowOverlay(up);
    return;
  }
  if (flowTrailIndex >= 0 && flowTrailIndex < flowTrail.length - 1) {
    flowTrailIndex += 1;
    const target = node(flowTrail[flowTrailIndex]);
    if (target) return openFlowOverlay(target, { fromNav: true });
  }
  const down = flowNavCache.downstream?.[0]?.other;
  if (down) return openFlowOverlay(down);
}
function closeFlowOverlay() {
  const dialog = $('#flow-overlay');
  if (dialog?._flowWireAbort) {
    dialog._flowWireAbort.abort();
    dialog._flowWireAbort = null;
  }
  const svg = $('#flow-wires');
  if (svg) svg.innerHTML = '';
  if (dialog?.open) dialog.close();
  flowTrail = [];
  flowTrailIndex = -1;
  flowNavCache = { upstream: [], downstream: [] };
  updateFlowNavButtons();
}
function waitMs(ms) {
  return new Promise(resolve => setTimeout(resolve, ms));
}
/** Final collapsed chrome size — same math render() will use after minimize. */
function collapsedFrameSize(item) {
  if (!item) return { w: 360, h: 86 };
  if (item.kind === 'file') {
    const header = frameLabelMetrics(item.label, { kind: 'file' });
    return { w: header.w, h: Math.max(78, header.h), headerH: header.h };
  }
  if (item.kind === 'folder') {
    const depth = Math.max(0, (item.depth || 1) - 1);
    const header = frameLabelMetrics(item.label, {
      kind: 'folder',
      minW: depth ? 320 : FRAME_LABEL_CHROME.folder.minW
    });
    return { w: header.w, h: Math.max(86, header.h), headerH: header.h };
  }
  return { w: 360, h: 86, headerH: 86 };
}
/**
 * Minimize morph — two phases so the title never gets flex-crushed.
 *
 * RCA: `.frame.float` is `display:flex; flex-direction:column`. Animating the
 * frame height down to the final bar size WHILE the canvas still has height
 * makes flex shrink the `.frame-bar`, clipping the title. Measuring endH alone
 * cannot fix that — the bar is compressed mid-transition regardless of target.
 *
 * Phase 1: collapse canvas → 0 with the bar flex-locked; frame ends at bar height.
 * Phase 2: ease width/height to the final collapsed metrics (wrap at final width).
 */
async function morphCollapseFrame(el) {
  if (!el || document.body.classList.contains('reduce-motion')) return false;
  const canvasEl = el.querySelector(':scope > .frame-canvas');
  const header = el.querySelector(':scope > .frame-bar');
  const item = node(el.dataset.dragId);
  if (!header) return false;
  const startH = el.offsetHeight;
  const startW = el.offsetWidth;
  const canvasStart = canvasEl ? canvasEl.offsetHeight : 0;
  const measuredHeaderH = Math.ceil(header.getBoundingClientRect().height || header.offsetHeight || 64);
  const predicted = collapsedFrameSize(item);
  // Phase-1 lock: never shorter than the bar as it is now (pre-wrap).
  const lockH = Math.max(measuredHeaderH, 74);
  const endH = Math.max(predicted.h, lockH);
  const endW = Math.max(120, predicted.w || startW);
  if (startH - endH < 8 && Math.abs(startW - endW) < 8 && canvasStart < 8) return false;
  cancelSoftSettle();

  const parentCanvas = el.parentElement?.classList.contains('frame-canvas') ? el.parentElement : null;
  const freed = Math.max(0, startH - endH);
  const elTop = parseFloat(el.style.top) || 0;
  const elLeft = parseFloat(el.style.left) || 0;
  const elBottom = elTop + startH;
  const siblings = parentCanvas
    ? [...parentCanvas.querySelectorAll(':scope > .frame.float[data-drag-id]')].filter(sib => sib !== el)
    : [];
  const easePos = 'left .55s cubic-bezier(.22, 1, .36, 1), top .55s cubic-bezier(.22, 1, .36, 1)';
  for (const sib of siblings) {
    const top = parseFloat(sib.style.top) || 0;
    if (top < elBottom - 2) continue;
    const newTop = Math.max(NEST_PAD, top - freed);
    sib.style.transition = easePos;
    sib.style.top = `${newTop}px`;
    const sibId = sib.dataset.dragId;
    if (sibId) {
      nestedSeats.set(sibId, { x: parseFloat(sib.style.left) || 0, y: newTop });
      userArranged.add(sibId);
    }
  }
  const selfId = el.dataset.dragId;
  if (selfId && parentCanvas) {
    nestedSeats.set(selfId, { x: elLeft, y: elTop });
    userArranged.add(selfId);
  }

  const parentFrame = parentCanvas?.closest?.('.frame.float');
  const parentHeader = parentFrame?.querySelector(':scope > .frame-bar');
  const parentHeaderH = Math.ceil(parentHeader?.getBoundingClientRect().height || 74);
  if (parentFrame && parentCanvas && freed > 0) {
    parentFrame.classList.add('flipping', 'size-morph', 'collapsing');
    parentHeader && (parentHeader.style.flexShrink = '0');
    parentFrame.style.transition = 'height .55s cubic-bezier(.22, 1, .36, 1)';
    parentCanvas.style.transition = 'height .55s cubic-bezier(.22, 1, .36, 1)';
    const parentH = parentFrame.offsetHeight;
    const parentCanvasH = parentCanvas.offsetHeight;
    parentFrame.style.height = `${parentH}px`;
    parentCanvas.style.height = `${parentCanvasH}px`;
    void parentFrame.offsetWidth;
    // Never crush the parent below its own bar + leftover canvas.
    const parentEnd = Math.max(parentHeaderH + Math.max(0, parentCanvasH - freed) + 12, parentH - freed);
    parentFrame.style.height = `${parentEnd}px`;
    parentCanvas.style.height = `${Math.max(0, parentCanvasH - freed)}px`;
  }

  el.classList.add('flipping', 'size-morph', 'collapsing');
  el.style.overflow = 'visible';
  // Lock bar so flex cannot crush the title while the canvas closes.
  header.style.flexShrink = '0';
  header.style.minHeight = `${lockH}px`;

  // —— Phase 1: collapse canvas only; frame settles to the locked bar height ——
  el.style.transition = 'height .48s cubic-bezier(.22, 1, .36, 1)';
  el.style.height = `${startH}px`;
  el.style.width = `${startW}px`;
  if (canvasEl) {
    canvasEl.style.overflow = 'hidden';
    canvasEl.style.flex = '1 1 auto';
    canvasEl.style.minHeight = '0';
    canvasEl.style.transition = 'height .48s cubic-bezier(.22, 1, .36, 1), opacity .28s ease';
    canvasEl.style.height = `${canvasStart}px`;
    void el.offsetWidth;
    canvasEl.style.height = '0px';
    canvasEl.style.opacity = '0';
  }
  void el.offsetWidth;
  el.style.height = `${lockH}px`;
  await waitMs(canvasStart > 4 ? 500 : 40);

  // —— Phase 2: ease to final collapsed metrics (width may reflow the title) ——
  header.style.minHeight = `${endH}px`;
  el.style.transition = 'height .4s cubic-bezier(.22, 1, .36, 1), width .4s cubic-bezier(.22, 1, .36, 1)';
  void el.offsetWidth;
  el.style.width = `${endW}px`;
  el.style.height = `${endH}px`;
  el.dataset.layoutW = String(Math.round(endW));
  el.dataset.layoutH = String(Math.round(endH));
  await waitMs(420);

  if (parentFrame) {
    parentFrame.classList.remove('collapsing');
    if (parentHeader) parentHeader.style.flexShrink = '';
  }
  return true;
}
function bindScene() {
  scene.querySelectorAll('.frame.float[data-drag-id]').forEach(bindFrameDrag);
  scene.querySelectorAll('[data-folder-expand]').forEach(button => button.addEventListener('click', async event => {
    event.stopPropagation();
    const id = button.dataset.folderExpand;
    const item = node(id);
    if (!item) return;
    remember();
    captureClickAnchor(id, event);
    markExpandAnchor(id);
    const opening = !expandedFolders.has(id);
    if (!opening) {
      const el = scene.querySelector(`[data-drag-id="${CSS.escape(id)}"]`);
      collapseMotion = true;
      lockCurrentIslandSeats();
      await morphCollapseFrame(el);
      markExpandAnchor(id);
      collapseMotion = true;
      // No constellation / settle after minimize — that pulled small folders to the center.
      pendingAlignAfterMorph = 0;
      toggleFolder(id);
      selectItem(id, { record: false });
      flowMode = true;
      rebuildTrace();
      skipFlipOnce = false;
      app.classList.remove('layout-quiet');
      clearTimeout(quietLayoutMotion._t);
      render();
      updateInspector();
      requestAnimationFrame(() => {
        animateReflowEdges(700);
        pulseSelection();
      });
      return;
    }
    // Pin seat first so the parent grows around this folder instead of moving it.
    clearSeatLock();
    pinNestedSeatFromDom(id);
    markExpandAnchor(id);
    pendingAlignAfterMorph = 120;
    toggleFolder(id);
    selectItem(id, { record: false });
    flowMode = true;
    rebuildTrace();
    skipFlipOnce = false;
    app.classList.remove('layout-quiet');
    clearTimeout(quietLayoutMotion._t);
    render();
    updateInspector();
    requestAnimationFrame(() => {
      animateReflowEdges(1100);
      pulseSelection();
    });
  }));
  scene.querySelectorAll('[data-expand]').forEach(button => button.addEventListener('click', async event => {
    event.stopPropagation();
    const file = node(button.dataset.expand);
    if (!file) return;
    if (expandedFiles.has(file.id)) {
      remember();
      captureClickAnchor(file.id, event);
      const el = scene.querySelector(`[data-drag-id="${CSS.escape(file.id)}"]`);
      collapseMotion = true;
      lockCurrentIslandSeats();
      await morphCollapseFrame(el);
      markExpandAnchor(file.id);
      collapseMotion = true;
      pendingAlignAfterMorph = 0;
      expandedFiles.delete(file.id);
      selectItem(file.id, { record: false });
      skipFlipOnce = false;
      app.classList.remove('layout-quiet');
      clearTimeout(quietLayoutMotion._t);
      render();
      updateInspector();
      requestAnimationFrame(() => {
        animateReflowEdges(700);
      });
    } else {
      pinNestedSeatFromDom(file.id);
      focusFileFrame(file, { expand: true, event });
    }
  }));
  scene.querySelectorAll('[data-focus-file]').forEach(button => button.addEventListener('click', event => {
    if (Date.now() - Number(button.closest('.frame')?.dataset.dragged || 0) < 220) return;
    const flowHit = event.target.closest('[data-open-file-flow]');
    if (flowHit) {
      event.preventDefault();
      event.stopPropagation();
      const file = node(flowHit.dataset.openFileFlow || button.dataset.focusFile);
      if (file) openFlowOverlay(file);
      return;
    }
    event.stopPropagation();
    focusFileFrame(node(button.dataset.focusFile), { expand: true, event });
  }));
  scene.querySelectorAll('[data-focus-file]').forEach(button => button.addEventListener('dblclick', event => {
    event.preventDefault();
    event.stopPropagation();
    const file = node(button.dataset.focusFile);
    if (file) openFlowOverlay(file);
  }));
  scene.querySelectorAll('[data-open-file-flow]').forEach(hint => {
    hint.addEventListener('click', event => {
      event.preventDefault();
      event.stopPropagation();
      const file = node(hint.dataset.openFileFlow);
      if (file) openFlowOverlay(file);
    });
  });
  scene.querySelectorAll('.outline-label[data-inline]:not([data-focus-file])').forEach(row => {
    row.addEventListener('click', event => {
      if (event.target.closest('[data-pin]') || Date.now() - Number(row.closest('.frame')?.dataset.dragged || 0) < 220) return;
      event.stopPropagation();
      const item = node(row.dataset.inline);
      if (!item) return;
      if (item.kind === 'file') return focusFileFrame(item, { expand: true, event });
      if (item.kind === 'folder') return focusFolderFrame(item, { expand: true, event });
      // Module / inline: open ancestors first, then one constellation (never align mid-FLIP).
      const file = fileOf(item);
      const openingFile = !!(file && !expandedFiles.has(file.id));
      beginFocusAlignMotion({ animateOpen: openingFile });
      if (openingFile) {
        clearSeatLock();
        markExpandAnchor(file.id);
        pinNestedSeatFromDom(file.id);
        clearNestedSeatsFor(file);
        pendingAlignAfterMorph = 160;
        expandedFiles.add(file.id);
      }
      activateFocus(item);
      captureClickAnchor(item.id, event);
      selectItem(item.id, { record: false });
      flowMode = true;
      rebuildTrace();
      render();
      updateInspector();
      requestAnimationFrame(() => {
        animateReflowEdges(openingFile ? 1100 : 700);
        pulseSelection();
        if (!openingFile) scheduleTraceAlign(120);
      });
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
  scene.querySelectorAll('.frame-fn[data-open-flow]').forEach(element => {
    element.addEventListener('click', event => {
      if (event.target.closest('[data-pin]')) return;
      // Ignore only real drags - never swallow title / flow-hint clicks.
      const fromEntry = event.target.closest('[data-open-flow], .frame-title, .fn-kind, .fn-flow-hint, b');
      if (!fromEntry && element.dataset.dragged && Date.now() - Number(element.dataset.dragged) < 280) return;
      const id = element.dataset.openFlow;
      const module = node(id);
      if (!module) return;
      event.preventDefault();
      event.stopPropagation();
      openFlowOverlay(module);
    });
  });
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
  $('#flow-nav-prev')?.addEventListener('click', event => {
    event.stopPropagation();
    flowNavStep(-1);
  });
  $('#flow-nav-next')?.addEventListener('click', event => {
    event.stopPropagation();
    flowNavStep(1);
  });
  $('#flow-overlay')?.addEventListener('click', event => {
    // Only the backdrop / empty dialog chrome closes - not the three planes.
    if (event.target === $('#flow-overlay')) closeFlowOverlay();
  });
  $('#flow-overlay')?.addEventListener('cancel', event => {
    event.preventDefault();
    closeFlowOverlay();
  });
  $('#flow-overlay')?.addEventListener('keydown', event => {
    if (!$('#flow-overlay')?.open) return;
    // Don't steal keys while the user is selecting/scrolling code.
    if (event.target?.closest?.('.flow-code, input, textarea')) return;
    if (event.key === 'ArrowLeft') {
      event.preventDefault();
      flowNavStep(-1);
    } else if (event.key === 'ArrowRight') {
      event.preventDefault();
      flowNavStep(1);
    } else if (event.key === 'Escape') {
      event.preventDefault();
      closeFlowOverlay();
    }
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
function selectItem(id, { record = true } = {}) {
  if (record && selectedId !== id) remember();
  // New selection releases the previous constellation pack.
  if (selectedId !== id) traceArranged.clear();
  selectedId = id; selectedImportEdgeId = undefined; rebuildTrace(); refreshFocusClasses(); drawEdges(); renderMinimap(); updateInspector(); writeDeepLink();
  // Park gravity only — constellation pack is one-shot via scheduleTraceAlign.
  // Don't kick gravity early during focus align; that nudged islands before the flight.
  if (traceEdges.size && !app.classList.contains('dragging') && !alignMotionPending && !stickyExpandId) {
    scheduleGravityDrift(180);
  }
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
    ? `${related.length} live relationship${related.length === 1 ? '' : 's'}. Related islands gather once around focus on click.`
    : 'No direct relationships with the current edge filters.';
  const structure = $('#inspect-structure');
  if (structure) {
    const glyph = file?.kind === 'file' ? fileGlyph(file) : null;
    const mods = file?.kind === 'file' ? modules(file).slice(0, 8) : [];
    const folderKids = item.kind === 'folder' ? folderItems(item).slice(0, 8) : [];
    structure.innerHTML = [
      glyph ? `<div class="struct-row"><span class="file-glyph" style="--glyph:${glyph.c}">${escape(glyph.g)}</span><span>${escape(file.extension || 'file')} · ${file.language || 'asset'}</span></div>` : '',
      item.kind === 'folder' ? `<div class="struct-row muted">${folderKids.length} direct · ${filesBelow(item).length} files</div>` : '',
      ...folderKids.map(child => {
        const g = child.kind === 'file' ? fileGlyph(child) : null;
        return `<button type="button" class="struct-jump" data-jump="${child.id}">${g ? `<span class="file-glyph" style="--glyph:${g.c}">${escape(g.g)}</span>` : (() => { const fi = folderIcon(child); return `<span class="folder-glyph compact" style="--accent:${fi.c}">${fi.g}</span>`; })()}<span>${escape(child.label)}</span></button>`;
      }),
      ...mods.map(module => `<button type="button" class="struct-jump" data-jump="${module.id}" data-open-flow-jump="${module.id}"><em>fn</em><span>${escape(module.label)}()</span></button>`),
      file?.kind === 'file' ? `<button type="button" class="struct-jump" data-jump="${file.id}" data-open-flow-jump="${file.id}"><em>flow</em><span>Open file flow</span></button>` : ''
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
/**
 * Reset presentation seats to a fresh shelf pack and fit the view.
 * Explicit feature via `forceFreshPack` — clears drag offsets, nested seats,
 * and layout memory so islands re-pack cleanly (not a side-effect of stale DOM).
 * Keeps expand/selection state; only repositions the map.
 */
function resetPresentation() {
  remember();
  exitFlow();
  cancelTraceAlign();
  cancelSoftSettle();
  offsets.clear();
  localOffsets.clear();
  nestedSeats.clear();
  userArranged.clear();
  layoutModes.clear();
  pinnedLayout.clear();
  traceArranged.clear();
  seatLock = new Set();
  collapseMotion = false;
  basePlacements.clear();
  layoutMemory.clear();
  basePlacementKey = '';
  alignMotionPending = false;
  forceFreshPack = true;
  skipFlipOnce = false;
  render();
  requestAnimationFrame(() => {
    fitMap();
    // Soft in-folder cleanup with the current padding rules after the fresh pack.
    scene.querySelectorAll('.frame.expanded[data-drag-id]').forEach(el => {
      const id = el.dataset.dragId;
      if (id) cleanupNestedLayout(id, { duration: 640 });
    });
    scheduleGravityDrift(500);
  });
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
    cancelTraceAlign();
    selectedImportEdgeId = undefined;
    exitFlow();
    pinned.clear();
    selectedId = rootFolder()?.id;
    rebuildTrace();
    // Keep the current map seats - only clear selection/trace chrome.
    refreshFocusClasses();
    drawEdges();
    updateInspector();
    syncToolbar();
    writeDeepLink();
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
    else if (flowMode || pinned.size || (selectedId && selectedId !== rootFolder()?.id)) {
      // Clear focus/trace first so related islands stay put instead of vanishing.
      remember();
      cancelTraceAlign();
      exitFlow();
      pinned.clear();
      selectedId = rootFolder()?.id;
      selectedImportEdgeId = undefined;
      rebuildTrace();
      refreshFocusClasses();
      drawEdges();
      updateInspector();
      syncToolbar();
    }
    else if (expandedFiles.size) { remember(); expandedFiles.clear(); render(); }
    else if (expandedFolders.size) { remember(); ensureDefaultOutlineExpanded(); pruneFolderDepth(); render(); }
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
        args: ['<path-to-DeepFlow>/mcp-server.js']
      }
    }
  }, null, 2) + '\n\nThen ask your agent to call deepflow_open_workspace with the absolute repo path before it starts editing, and deepflow_after_edit after file changes.';
}
function showOpenDialog() {
  const dialog = $('#open-dialog');
  if (dialog?.showModal) dialog.showModal();
  else openWorkspace();
}
function initWelcomeSplash() {
  const dialog = $('#welcome-splash');
  if (!dialog) return;
  const seen = localStorage.getItem('deepflow-welcome-seen') === '1';
  const startTour = async () => {
    localStorage.setItem('deepflow-welcome-seen', '1');
    if (!graph) {
      try { await loadGraph(); } catch {}
    }
    playLocalCapabilityDemo();
  };
  $('#welcome-start-tour')?.addEventListener('click', event => {
    event.preventDefault();
    dialog.close('tour');
    startTour();
  });
  $('#welcome-skip')?.addEventListener('click', () => {
    localStorage.setItem('deepflow-welcome-seen', '1');
  });
  dialog.addEventListener('close', () => {
    if (dialog.returnValue === 'tour') return;
    localStorage.setItem('deepflow-welcome-seen', '1');
  });
  if (!seen && dialog.showModal) {
    requestAnimationFrame(() => {
      try { dialog.showModal(); } catch {}
    });
  }
}
async function playLocalCapabilityDemo() {
  try {
    const response = await fetch('/api/demo-steps');
    if (response.ok) {
      const data = await response.json();
      if (data.steps?.length) {
        await playTour(data.steps);
        return;
      }
    }
  } catch {}
  // Minimal fallback if the viewer isn't serving demo steps yet.
  await playTour([
    { title: 'Welcome', narrative: 'Nested frames for architecture. Drag freely; neighbors yield when you drop.', dwellMs: 5200, legend: { kicker: 'Tour', title: 'DeepFlow', body: 'Agent-native architecture map.' }, command: { type: 'set-mode', mode: 'outline' } },
    { title: 'Live traces', narrative: 'Turn on Live and hover to follow wires without changing selection.', dwellMs: 5000, legend: { kicker: 'Live', title: 'Hover traces', body: 'Ribbon → Live' }, command: { type: 'set-live', enabled: true } }
  ]);
}
function initSettings() {
  const savedTheme = localStorage.getItem('deepflow-theme') || 'ocean';
  const knownThemes = new Set([...($('#theme-grid')?.querySelectorAll('[data-theme-choice]') || [])].map(button => button.dataset.themeChoice));
  const theme = knownThemes.has(savedTheme) ? savedTheme : 'ocean';
  if (theme !== savedTheme) localStorage.setItem('deepflow-theme', theme);
  const motion = localStorage.getItem('deepflow-motion') !== 'reduced';
  autoRevealChanges = localStorage.getItem('deepflow-auto-reveal') !== 'false';
  agentRevealDwellMs = Math.max(3000, Math.min(20000, Number(localStorage.getItem('deepflow-reveal-dwell') || 8000)));
  const knownEditAnims = new Set(['pulse', 'ripple', 'flash', 'scan', 'fire', 'spark', 'hearts', 'lines']);
  const savedEditAnim = localStorage.getItem('deepflow-edit-anim') || 'spark';
  editAnimStyle = knownEditAnims.has(savedEditAnim) ? savedEditAnim : 'pulse';
  traceMode = localStorage.getItem('deepflow-live-trace') !== 'false';
  document.body.dataset.theme = theme;
  document.body.classList.toggle('reduce-motion', !motion);
  syncEditAnim();
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
  $('#edit-anim-grid')?.querySelectorAll('[data-edit-anim]').forEach(button => button.addEventListener('click', () => {
    editAnimStyle = button.dataset.editAnim;
    localStorage.setItem('deepflow-edit-anim', editAnimStyle);
    syncEditAnim();
    // Preview the style on the selected/focused file if present.
    const previewId = agentRevealExpandedId || fileOf(selected())?.id || selectedId;
    if (previewId) applyEditAnimBurst(previewId);
  }));
  // Seed live particles into the fire and hearts preview thumbnails
  seedPreviewParticles();
  // Seed the lines preview with animated bars
  seedLinesPreview();
  // Wire copy agent instructions button
  document.querySelectorAll('#copy-agent-instructions, #copy-agent-instructions-open').forEach(copyBtn => {
    copyBtn.addEventListener('click', () => {
      fetch('/agent-setup.txt')
        .then(r => r.text())
        .then(instructions => {
          navigator.clipboard.writeText(instructions).then(() => {
            const toast = $('#copy-agent-toast');
            if (toast) { toast.style.opacity = '1'; setTimeout(() => { toast.style.opacity = '0'; }, 2800); }
            copyBtn.textContent = 'Copied!';
            copyBtn.style.background = 'var(--green)';
            copyBtn.style.color = 'var(--paper)';
            setTimeout(() => {
              copyBtn.textContent = 'Copy Agent Setup';
              copyBtn.style.background = 'var(--panel)';
              copyBtn.style.color = 'var(--green)';
            }, 2200);
          }).catch(() => {
            const ta = document.createElement('textarea');
            ta.value = instructions; ta.style.position = 'fixed'; ta.style.opacity = '0';
            document.body.appendChild(ta); ta.select();
            document.execCommand('copy');
            document.body.removeChild(ta);
          });
        })
        .catch(() => console.warn('DeepFlow: could not load /agent-setup.txt'));
    });
  });
}
function seedPreviewParticles() {
  const configs = {
    fire: {
      glyphs: ['\u25cf', '\u25cb', '\u2022', '\u25e6', '\u00b0', '\u25cf', '\u25cb', '\u2022', '\u25e6', '\u00b0'],
      colors: ['#ff9f1c', '#ff6b35', '#dc2f02', '#ffb347', '#ffd080', '#ff4500', '#ff9f1c', '#ffcf77', '#dc2f02', '#ff6b35'],
      count: 14,
    },
    hearts: {
      glyphs: ['\u2665', '\u2661', '\u2665', '\u2661', '\u2665', '\u2661', '\u2665', '\u2661', '\u2665', '\u2661'],
      colors: ['#e83e8c', '#ff7eb6', '#ff4daa', '#ffb3d9', '#e83e8c', '#c2185b', '#ff7eb6', '#e83e8c', '#ff4daa', '#ffb3d9'],
      count: 14,
    },
  };
  for (const [kind, cfg] of Object.entries(configs)) {
    const preview = document.querySelector(`.edit-anim-preview.${kind}`);
    if (!preview) continue;
    // Remove any previously seeded particles
    preview.querySelectorAll('.preview-particle').forEach(el => el.remove());
    for (let i = 0; i < cfg.count; i++) {
      const span = document.createElement('span');
      span.className = 'preview-particle';
      const glyph = cfg.glyphs[i % cfg.glyphs.length];
      span.textContent = glyph;
      const leftPct = 10 + Math.random() * 80; // spread across preview width
      const sizePx = 6 + Math.random() * 10;   // 6–16px: big size variability
      const delay = (Math.random() * 1.4).toFixed(2);
      const dur = (1.0 + Math.random() * 0.8).toFixed(2);
      const drift = ((Math.random() - 0.5) * 12).toFixed(1); // ±6px horizontal drift
      const color = cfg.colors[i % cfg.colors.length];
      span.style.cssText = `
        position: absolute;
        bottom: 2px;
        left: ${leftPct}%;
        font-size: ${sizePx}px;
        color: ${color};
        text-shadow: 0 0 ${Math.round(sizePx * 0.8)}px ${color};
        opacity: 0;
        pointer-events: none;
        animation: preview-particle-rise ${dur}s ease-out ${delay}s infinite;
        --drift: ${drift}px;
      `;
      preview.appendChild(span);
    }
  }
}
function seedLinesPreview() {
  const preview = document.querySelector('.edit-anim-preview.lines');
  if (!preview) return;
  // Clear any existing bar spans (leave ::before/::after pseudo elements)
  preview.querySelectorAll('.preview-line-bar').forEach(el => el.remove());
  // The lines preview already shows 2 bars via ::before/::after CSS - add 3 more for depth
  const widths = [80, 55, 70, 38, 62];
  const colors = [
    'var(--green)', 'var(--amber)', 'var(--green)', 'var(--teal)', 'var(--amber)'
  ];
  widths.forEach((w, i) => {
    const bar = document.createElement('span');
    bar.className = 'preview-line-bar';
    bar.style.cssText = `
      position: absolute;
      left: 18%;
      height: 2px;
      border-radius: 99px;
      width: ${w}%;
      background: ${colors[i]};
      box-shadow: 0 0 6px ${colors[i]};
      transform-origin: left center;
      opacity: 0;
      animation: edit-anim-line-run 1.15s ease-in-out ${(i * 0.18).toFixed(2)}s infinite;
      top: ${22 + i * 14}%;
    `;
    preview.appendChild(bar);
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
let tourPlaying = false;
let traceDialects = false;
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
function showDemoLegend(step, index, total) {
  const legend = $('#demo-legend');
  if (!legend) return;
  const meta = step.legend || {};
  $('#demo-legend-kicker').textContent = meta.kicker || `Step ${index + 1}`;
  $('#demo-legend-title').textContent = meta.title || step.title || 'DeepFlow';
  $('#demo-legend-body').textContent = meta.body || step.narrative || '';
  $('#demo-legend-step').textContent = `${index + 1} / ${total}`;
  const bar = $('#demo-legend-bar');
  if (bar) bar.style.width = `${((index + 1) / Math.max(1, total)) * 100}%`;
  legend.hidden = false;
  requestAnimationFrame(() => legend.classList.add('visible'));
}
function hideDemoLegend() {
  const legend = $('#demo-legend');
  if (!legend) return;
  legend.classList.remove('visible');
  setTimeout(() => { legend.hidden = true; }, 400);
}
function clearDemoSpotlight() {
  const spot = $('#demo-spotlight');
  if (spot) {
    spot.hidden = true;
    spot.innerHTML = '';
  }
  app.classList.remove('demo-spotlight-on');
  scene.querySelectorAll('.demo-focus').forEach(el => el.classList.remove('demo-focus'));
}
function applyDemoSpotlight(step) {
  clearDemoSpotlight();
  const target = step?.spotlight;
  if (!target) return;
  let el = null;
  if (target.module) {
    const file = target.path ? fileByPath(target.path) : null;
    const mod = file ? modules(file).find(m => m.label === target.module) : null;
    if (mod) el = scene.querySelector(`[data-module-box="${CSS.escape(mod.id)}"],[data-drag-id="${CSS.escape(mod.id)}"]`);
  }
  if (!el && target.path) {
    const item = fileByPath(target.path) || folderByPath(target.path);
    if (item) el = scene.querySelector(`[data-id="${CSS.escape(item.id)}"],[data-drag-id="${CSS.escape(item.id)}"]`);
  }
  if (!el) return;
  el.classList.add('demo-focus');
  const boardRect = board.getBoundingClientRect();
  const rect = el.getBoundingClientRect();
  const pad = 16;
  const spot = $('#demo-spotlight');
  if (!spot) return;
  const hole = document.createElement('div');
  hole.className = 'demo-spotlight-hole';
  Object.assign(hole.style, {
    left: `${rect.left - boardRect.left - pad}px`,
    top: `${rect.top - boardRect.top - pad}px`,
    width: `${rect.width + pad * 2}px`,
    height: `${rect.height + pad * 2}px`
  });
  spot.appendChild(hole);
  spot.hidden = false;
  app.classList.add('demo-spotlight-on');
}
function spawnParticleBurst(el, kind = 'hearts') {
  if (!el || document.body.classList.contains('reduce-motion')) return;
  const layer = document.createElement('div');
  layer.className = `particle-burst ${kind}`;
  const glyphs = kind === 'fire' ? ['🔥', '⚡', '✦', '✧'] : kind === 'sparks' ? ['.', '+', '*'] : ['♥', '♡'];
  const count = kind === 'hearts' ? 18 : kind === 'fire' ? 16 : 14;
  for (let i = 0; i < count; i++) {
    const p = document.createElement('span');
    p.textContent = glyphs[i % glyphs.length];
    const angle = (i / count) * Math.PI * 2 + (Math.random() - .5) * .4;
    const dist = kind === 'hearts' ? 36 + Math.random() * 54 : 28 + Math.random() * 50;
    p.style.setProperty('--dx', `${Math.cos(angle) * dist}px`);
    p.style.setProperty('--dy', `${Math.sin(angle) * dist - (kind === 'hearts' ? 28 : 10)}px`);
    p.style.setProperty('--delay', `${Math.random() * 220}ms`);
    p.style.setProperty('--spin', `${(Math.random() - .5) * 80}deg`);
    p.style.setProperty('--scale', `${0.7 + Math.random() * 0.7}`);
    layer.appendChild(p);
  }
  el.appendChild(layer);
  setTimeout(() => layer.remove(), kind === 'hearts' ? 1900 : 1600);
}
function hideEditTheater() {
  const theater = $('#edit-theater');
  if (!theater) return;
  theater.classList.remove('visible', 'folding');
  theater.hidden = true;
}
function showEditTheater(file) {
  const theater = $('#edit-theater');
  if (!theater || !file) return;
  const diff = String(file.git?.diff || '');
  const rows = diff.split('\n').filter(line => /^[+-]/.test(line) && !/^(\+\+\+|---)/.test(line)).slice(0, 12);
  let lineNo = file.loc?.start || 1;
  const html = (rows.length ? rows : ['+ // agent edit…', '+ // refreshing map', '- // stale guard']).map((line, index) => {
    const kind = line.startsWith('+') ? 'add' : 'remove';
    const n = lineNo + index;
    return `<div class="edit-theater-row ${kind}"><i>${n}</i><span></span><code>${escape(line.slice(0, 42))}</code></div>`;
  }).join('');
  $('#edit-theater-title').textContent = file.label || 'Editing';
  $('#edit-theater-meta').textContent = file.git?.change || 'live edit';
  $('#edit-theater-lines').innerHTML = html || '<div class="edit-theater-row add"><i>·</i><span></span><code>writing…</code></div>';
  const host = scene.querySelector(`[data-id="${CSS.escape(file.id)}"]`);
  const boardRect = board.getBoundingClientRect();
  if (host) {
    const rect = host.getBoundingClientRect();
    theater.style.left = `${Math.min(boardRect.width - 220, Math.max(12, rect.right - boardRect.left + 14))}px`;
    theater.style.top = `${Math.max(56, rect.top - boardRect.top)}px`;
  } else {
    theater.style.left = '24px';
    theater.style.top = '72px';
  }
  theater.hidden = false;
  requestAnimationFrame(() => theater.classList.add('visible'));
  return theater;
}
async function playEditTheater(file) {
  const theater = showEditTheater(file);
  if (!theater) return;
  await new Promise(r => setTimeout(r, 2200));
  theater.classList.add('folding');
  await new Promise(r => setTimeout(r, 700));
  hideEditTheater();
  updateInspector();
  $('#diff-panel')?.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
  $('#diff-panel')?.classList.add('diff-reveal');
  setTimeout(() => $('#diff-panel')?.classList.remove('diff-reveal'), 1600);
}
async function playTour(steps = []) {
  if (tourPlaying) return;
  tourPlaying = true;
  app.classList.add('demo-playing');
  try {
    for (let index = 0; index < steps.length; index++) {
      const step = steps[index];
      const dwell = Math.max(5600, Number(step.dwellMs) || 6400);
      showDemoLegend(step, index, steps.length);
      // Legend carries the story during the capability demo; keep the floating
      // tour card off so it never fights the minimap / spotlight.
      const card = $('#tour-card');
      if (card) { card.classList.remove('visible'); card.hidden = true; }
      if (step.command) await Promise.resolve(handleViewerCommand({ ...step.command, type: step.command.type }));
      requestAnimationFrame(() => applyDemoSpotlight(step));
      // Re-fit spotlight after layout settles from jump/expand.
      setTimeout(() => applyDemoSpotlight(step), 420);
      await new Promise(resolve => setTimeout(resolve, dwell));
    }
  } finally {
    tourPlaying = false;
    app.classList.remove('demo-playing');
    clearDemoSpotlight();
    hideDemoLegend();
    hideEditTheater();
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
  if (command.type === 'set-live') {
    traceMode = command.enabled !== false;
    localStorage.setItem('deepflow-live-trace', String(traceMode));
    syncToolbar();
    drawEdges();
    return;
  }
  if (command.type === 'set-theme') {
    const theme = command.theme || 'ocean';
    document.body.dataset.theme = theme;
    localStorage.setItem('deepflow-theme', theme);
    $('#theme-grid')?.querySelectorAll('[data-theme-choice]').forEach(button => {
      button.classList.toggle('active', button.dataset.themeChoice === theme);
    });
    if (graph) render();
    return;
  }
  if (command.type === 'set-edit-anim') {
    const known = new Set(['pulse', 'ripple', 'flash', 'scan', 'fire', 'spark', 'hearts', 'lines']);
    editAnimStyle = known.has(command.style) ? command.style : 'pulse';
    localStorage.setItem('deepflow-edit-anim', editAnimStyle);
    syncEditAnim();
    const file = command.path ? fileByPath(command.path) : null;
    if (file) {
      applyEditAnimBurst(file.id);
      const el = scene.querySelector(`[data-id="${CSS.escape(file.id)}"]`);
      el?.classList.add('agent-editing');
      setTimeout(() => el?.classList.remove('agent-editing'), 2200);
    }
    return;
  }
  if (command.type === 'set-trace-dialects') {
    traceDialects = command.enabled !== false;
    document.body.classList.toggle('trace-dialects', traceDialects);
    drawEdges();
    return;
  }
  if (command.type === 'particle-burst') {
    const file = fileByPath(command.path);
    const el = file ? scene.querySelector(`[data-id="${CSS.escape(file.id)}"]`) : null;
    if (el) {
      el.classList.add('demo-focus');
      spawnParticleBurst(el, command.kind || 'hearts');
      setTimeout(() => el.classList.remove('demo-focus'), 1600);
    }
    return;
  }
  if (command.type === 'pop-in') {
    const file = fileByPath(command.path);
    const el = file ? scene.querySelector(`[data-id="${CSS.escape(file.id)}"]`) : null;
    if (el) {
      el.classList.remove('file-pop-in');
      void el.offsetWidth;
      el.classList.add('file-pop-in');
      setTimeout(() => el.classList.remove('file-pop-in'), 1400);
    }
    return;
  }
  if (command.type === 'focus-folder') {
    const folder = folderByPath(command.path) || graph?.nodes.find(n => n.kind === 'folder' && (n.path === command.path || n.label === command.path));
    if (!folder) return;
    focusFolderFrame(folder, { expand: command.expand !== false });
    if (command.pulse) requestAnimationFrame(pulseSelection);
    return;
  }
  if (command.type === 'simulate-edit') {
    const path = command.path;
    if (!path) return;
    markRecent([path]);
    playAgentEditReveal(path, { theater: !!command.theater });
    return;
  }
  if (command.type === 'clear-highlights') {
    remember(); closeFlowOverlay(); pinned.clear(); exitFlow(); recentPaths.clear(); traceDialects = false;
    document.body.classList.remove('trace-dialects');
    clearDemoSpotlight(); hideEditTheater();
    rebuildTrace(); render(); updateInspector(); writeDeepLink(); return;
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
    if (command.legend) showDemoLegend({ legend: command.legend, title: command.title, narrative: command.narrative }, command.index || 0, command.total || 1);
    if (command.command) handleViewerCommand(command.command);
    if (command.spotlight) requestAnimationFrame(() => applyDemoSpotlight(command));
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
  if (!preserve) { offsets.clear(); localOffsets.clear(); nestedSeats.clear(); userArranged.clear(); layoutModes.clear(); pinnedLayout.clear(); traceArranged.clear(); seatLock = new Set(); collapseMotion = false; basePlacements.clear(); layoutMemory.clear(); basePlacementKey = ''; exitFlow(); expandedFiles.clear(); expandedFolders.clear(); expandedModules.clear(); sourceFiles.clear(); pinned.clear(); recentPaths.clear(); activityItems.clear(); archivedActivity.length = 0; undoStack.length = 0; redoStack.length = 0; }
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
      const linked = applyDeepLink();
      if (!linked) writeDeepLink();
      // After layout + optional deep-link focus, start rubber-band even if
      // partners begin outside the viewfinder.
      requestAnimationFrame(() => {
        rebuildTrace();
        if (traceEdges.size > 0) {
          scheduleTraceAlign(linked ? 640 : 320);
          scheduleGravityDrift(720);
        } else {
          scheduleGravityDrift(300);
        }
      });
    });
  }
}
async function loadGraph({ preserve = false } = {}) { const response = await fetch('/api/graph', { method: 'POST', headers: { 'content-type': 'application/json' }, body: JSON.stringify({}) }); if (!response.ok) throw new Error(await response.text()); sourceMode = 'live'; if ($('#tracking-status')) $('#tracking-status').textContent = 'live local map'; applyGraph(await response.json(), { preserve }); }
initSettings();
initSearch();
initFlowOverlay();
initWelcomeSplash();
$('#history-back').addEventListener('click', () => moveHistory(true)); $('#history-forward').addEventListener('click', () => moveHistory(false)); $('#reset-view').addEventListener('click', resetPresentation); $('#open-workspace').addEventListener('click', showOpenDialog); $('#choose-folder').addEventListener('click', openWorkspace); $('#workspace-files').addEventListener('change', event => { if (event.target.files.length) snapshotFiles([...event.target.files]); event.target.value = ''; }); $('#inspector-toggle').addEventListener('click', () => app.classList.toggle('inspector-closed'));
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
