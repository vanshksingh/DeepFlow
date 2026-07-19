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
let autoRevealChanges = false;
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

const FLOW_TYPES = new Set(['calls', 'dataflow', 'events', 'inherits', 'imports', 'references', 'reexports']);
const WALK_TYPES = new Set(['calls', 'dataflow', 'events', 'inherits']);
const CONTEXT_TYPES = new Set(['imports', 'references', 'reexports']);
const SOURCE_EXTENSIONS = new Set(['.js', '.mjs', '.cjs', '.ts', '.tsx', '.jsx']);
// The map opens with the two relationships people can read at a glance. Other
// semantic edge types remain available to the trace engine without flooding
// the architectural overview.
const edgeVisibility = { calls: true, dataflow: false, events: false, inherits: false, imports: true, references: false, reexports: false };
const edgeTypes = () => graph.edges.filter(edge => FLOW_TYPES.has(edge.type) && edgeVisibility[edge.type] !== false);
const node = id => graph?.nodes.find(item => item.id === id);
const rootFolder = () => graph.nodes.find(item => item.kind === 'folder' && item.depth === 0);
const children = id => graph.nodes.filter(item => item.parentId === id);
const folder = () => node(scopeId) || rootFolder();
const selected = () => node(selectedId);
const fileOf = item => item?.kind === 'module' ? node(item.fileId) : item?.kind === 'file' ? item : null;
const modules = file => children(file.id).filter(item => item.kind === 'module').sort((a, b) => a.loc.start - b.loc.start);
const filesBelow = item => graph.nodes.filter(entry => entry.kind === 'file' && ancestors(entry).some(parent => parent.id === item.id));
const directItems = item => children(item.id).filter(child => child.kind === 'folder' || child.kind === 'file');
const escape = value => String(value ?? '').replaceAll('&', '&amp;').replaceAll('<', '&lt;').replaceAll('>', '&gt;');
const colors = ['#087c66', '#6056a7', '#ad6b25', '#a84b68', '#287e98', '#72843d'];
const color = value => colors[[...String(value)].reduce((sum, letter) => sum + letter.charCodeAt(0), 0) % colors.length];

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
function rebuildTrace() {
  const data = collectTrace(selected() || entryItem());
  trace = data.nodes; traceEdges = data.edges;
  for (const pin of pinned) {
    const pinnedData = collectTrace(node(pin));
    for (const id of pinnedData.nodes) trace.add(id);
    for (const id of pinnedData.edges) traceEdges.add(id);
  }
}
function hasTrace(item) {
  if (!item) return false;
  if (trace.has(item.id)) return true;
  if (item.kind === 'file') return modules(item).some(module => trace.has(module.id));
  if (item.kind === 'folder') return filesBelow(item).some(hasTrace);
  return false;
}
function traceActive() { return traceMode; }
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
  if (/(^|\/)(apps?|gateway|console|web|api)(\/|$)/.test(path)) return 'application';
  if (/(^|\/)(services?|workers?|server)(\/|$)/.test(path)) return 'service';
  if (/(^|\/)(packages?|shared|common|lib|core)(\/|$)/.test(path)) return 'package';
  if (/(^|\/)(tests?|__tests__|specs?|fixtures)(\/|$)/.test(path)) return 'test';
  if (/(^|\/)(generated|dist|build|coverage|vendor)(\/|$)/.test(path)) return 'generated';
  if (/(^|\/)(docs?|readme|examples?)(\/|$)/.test(path)) return 'docs';
  if (/(^|\/)(config|infra|scripts|assets|docker|deploy)(\/|$)/.test(path) || isInfrastructure(item)) return 'infrastructure';
  return 'context';
}
const mapRegionPriority = { application: 0, service: 1, package: 2, context: 3, infrastructure: 4, docs: 5, generated: 6, test: 7 };
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
  return directItems(item).sort((a, b) => {
    if (a.kind !== b.kind) return a.kind === 'folder' ? -1 : 1;
    if (a.kind === 'folder') return (mapRegionPriority[mapRegion(a)] ?? 9) - (mapRegionPriority[mapRegion(b)] ?? 9) || a.label.localeCompare(b.label);
    return fileOrder(a, b);
  });
}
function primaryTraceScore(item) {
  const score = hasTrace(item) ? 1000 : 0;
  return score + externalRelationshipCount(item) * 22 + relationshipCount(item) * 3 + (item.entrypoint ? 80 : 0) + (isInfrastructure(item) ? -40 : 0) - (item.orphan ? 120 : 0);
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
  return direct.sort((a, b) => primaryTraceScore(b) - primaryTraceScore(a) || a.label.localeCompare(b.label))[0] || entryFile(item) || item;
}
function snapshot() {
  return { scopeId, selectedId, selectedImportEdgeId, layoutAnchorFileId, flowMode, traceMode, presentationMode, expanded: [...expandedFiles], expandedFolders: [...expandedFolders], expandedModules: [...expandedModules], source: [...sourceFiles], pinned: [...pinned], offsets: [...offsets.entries()].map(([id, value]) => [id, { ...value }]), canvas: { ...canvas }, edgeVisibility: { ...edgeVisibility } };
}
function updateHistory() { $('#history-back').disabled = !undoStack.length; $('#history-forward').disabled = !redoStack.length; }
function remember() { if (!graph) return; undoStack.push(snapshot()); if (undoStack.length > 70) undoStack.shift(); redoStack.length = 0; updateHistory(); }
function restore(state) {
  scopeId = state.scopeId; selectedId = state.selectedId; selectedImportEdgeId = state.selectedImportEdgeId; layoutAnchorFileId = state.layoutAnchorFileId; flowMode = state.flowMode; traceMode = state.traceMode ?? true; presentationMode = !!state.presentationMode;
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
    return 50 + (expanded ? 20 + imports * 34 + moduleRows * 42 + sourceRows : 0);
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
  const moduleHeight = !collapsed && expandedFiles.has(item.id) ? Math.max(0, modules(item).length * 44 + 46 + sourceHeight) : 0;
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
function softenedPlacement(item, target, locked = false) {
  if (locked) return target;
  const previous = layoutMemory.get(item.id);
  if (!previous) return target;
  const maxMove = hasTrace(item) ? 280 : 180;
  const dx = target.x - previous.x, dy = target.y - previous.y;
  const distance = Math.hypot(dx, dy);
  if (distance <= maxMove) return target;
  const ratio = maxMove / distance;
  return { ...target, x: previous.x + dx * ratio, y: previous.y + dy * ratio };
}
function requestLayoutSettle(item) {
  const file = fileOf(item);
  if (file) activateFocus(item);
  else {
    const origin = captureItemOrigin(item);
    if (origin) layoutMemory.set(origin.id, origin);
    flowMode = true;
  }
  basePlacements.clear();
  basePlacementKey = '';
}
function focusAnchorElement() {
  const item = selected();
  if (item?.kind === 'module') return scene.querySelector(`[data-module="${CSS.escape(item.id)}"]`);
  const file = fileOf(item);
  return file ? scene.querySelector(`.card[data-id="${CSS.escape(file.id)}"], [data-inline-file="${CSS.escape(file.id)}"]`) : null;
}
function lockFocusedAnchor(previousRect) {
  const item = selected(); const file = fileOf(item);
  const anchor = focusAnchorElement();
  if (!previousRect || !anchor || !file || focusedFileId !== file.id) return;
  const current = anchor.getBoundingClientRect();
  const dx = (previousRect.left - current.left) / canvas.scale;
  const dy = (previousRect.top - current.top) / canvas.scale;
  if (Math.abs(dx) < .5 && Math.abs(dy) < .5) return;
  const value = offsets.get(file.id) || { x: 0, y: 0 };
  const next = { x: value.x + dx, y: value.y + dy };
  offsets.set(file.id, next);
  const card = scene.querySelector(`.card[data-id="${CSS.escape(file.id)}"]`);
  if (card) card.style.translate = `${next.x}px ${next.y}px`;
}
function activateFocus(item) {
  const file = fileOf(item); if (!file) return;
  // Capture the *rendered* position at pointer time. That location becomes the
  // file's new anchor before a single neighbouring card begins to move.
  focusOrigin = captureFocusOrigin(file);
  focusedFileId = file.id;
  flowMode = true;
  layoutAnchorFileId = file.id;
  basePlacements.clear();
  basePlacementKey = '';
}
function settleDragAnchor(item) {
  const file = fileOf(item) || (item?.kind === 'file' ? item : null);
  if (!file) return false;
  const origin = captureCardOrigin(file.id) || captureFocusOrigin(file);
  if (!origin) return false;
  focusOrigin = origin;
  focusedFileId = file.id;
  flowMode = true;
  layoutAnchorFileId = file.id;
  offsets.delete(file.id);
  if (!selected() || fileOf(selected())?.id !== file.id) selectedId = file.id;
  basePlacements.clear();
  basePlacementKey = '';
  rebuildTrace();
  return true;
}
function automaticLayout() {
  const current = folder();
  const direct = directItems(current);
  const directIds = new Set(direct.map(item => item.id));
  const anchor = node(layoutAnchorFileId)?.kind === 'file' ? node(layoutAnchorFileId) : entryFile(current);
  const focusItem = selected();
  const focusMode = focusedFileId === fileOf(focusItem)?.id && (focusItem?.kind === 'module' || focusItem?.kind === 'file');
  const focusFiles = focusMode ? focusTraceFiles(focusItem) : [];
  const related = focusMode ? focusFiles : flowMode ? traceFilesFor(anchor).filter(file => !directIds.has(file.id) && file.id !== anchor?.id).slice(0, 18) : [];
  const contextItems = (focusMode ? [...direct.filter(item => !hasTrace(item)), ...related] : [...direct, ...related]).filter((item, index, list) => list.findIndex(other => other.id === item.id) === index);
  const pad = 72;
  const gap = 42;
  const minColumn = 300;
  const maxColumn = 720;
  const viewportWidth = Math.max(980, board.clientWidth);
  const viewportHeight = Math.max(680, board.clientHeight);
  const usableWidth = Math.max(900, viewportWidth - pad * 2);
  const worldWidth = Math.max(viewportWidth, usableWidth + pad * 2);
  const placements = [];
  const layoutKey = `${scopeId}:${focusMode ? `focus:${focusItem.id}:` : ''}${contextItems.map(item => item.id).sort().join('|')}`;
  const collides = (a, b, verticalGap = 32, horizontalGap = gap) => !(a.x + a.w + horizontalGap < b.x || b.x + b.w + horizontalGap < a.x || a.y + a.h + verticalGap < b.y || b.y + b.h + verticalGap < a.y);
  const clampX = (x, width) => Math.max(pad, Math.min(pad + usableWidth - width, x));
  const clampY = (y, height) => Math.max(56, Math.min(Math.max(56, viewportHeight - height - 26), y));
  const openSpot = (box, placed, keepInFrame = false) => {
    const fits = candidate => !placed.some(other => collides(candidate, other));
    const normalized = candidate => ({
      ...candidate,
      x: clampX(candidate.x, candidate.w),
      y: keepInFrame ? clampY(candidate.y, candidate.h) : Math.max(56, candidate.y)
    });
    const first = normalized(box);
    if (fits(first)) return first;
    const directions = [[1, 0], [-1, 0], [0, 1], [0, -1], [1, 1], [-1, 1], [1, -1], [-1, -1]];
    for (let ring = 1; ring <= 6; ring++) {
      const distance = ring * 56;
      for (const [dx, dy] of directions) {
        const candidate = normalized({ ...box, x: box.x + dx * distance, y: box.y + dy * distance });
        if (fits(candidate)) return candidate;
      }
    }
    let y = first.y, attempts = 0;
    while (placed.some(other => collides({ ...first, y }, other)) && attempts++ < 60) {
      const blockers = placed.filter(other => collides({ ...first, y }, other));
      y = Math.max(y + 28, ...blockers.map(other => other.y + other.h + 44));
    }
    return { ...first, y };
  };
  const relaxTraceSprings = items => {
    const lockedId = focusMode ? focusedFileId : null;
    const move = new Map();
    const center = placement => ({ x: placement.x + placement.w / 2, y: placement.y + placement.h / 2 });
    const add = (id, dx, dy) => {
      if (!id || id === lockedId) return;
      const value = move.get(id) || { x: 0, y: 0 };
      value.x += dx; value.y += dy; move.set(id, value);
    };
    for (const { from, to, weight } of traceSpringPairs(items).slice(0, 28)) {
      const a = basePlacements.get(from.id), b = basePlacements.get(to.id);
      if (!a || !b) continue;
      const ac = center(a), bc = center(b);
      const dx = bc.x - ac.x, dy = bc.y - ac.y;
      const distance = Math.max(1, Math.hypot(dx, dy));
      const desired = 390 + Math.min(90, Math.abs(dy) * .22);
      const stretch = Math.max(-90, Math.min(180, distance - desired));
      const pull = Math.max(-20, Math.min(46, stretch * .09 * Math.min(2.2, weight)));
      if (Math.abs(pull) > .5) {
        const ux = dx / distance, uy = dy / distance;
        add(from.id, ux * pull, uy * pull);
        add(to.id, -ux * pull, -uy * pull);
      }
      if (bc.x < ac.x + 180) {
        const correction = Math.min(54, (ac.x + 180 - bc.x) * .16 * Math.min(2, weight));
        add(from.id, -correction, 0);
        add(to.id, correction, 0);
      }
    }
    for (const [id, delta] of move) {
      const placement = basePlacements.get(id); if (!placement) continue;
      const length = Math.hypot(delta.x, delta.y);
      const cap = hasTrace(node(id)) ? 72 : 38;
      const ratio = length > cap ? cap / length : 1;
      basePlacements.set(id, {
        ...placement,
        x: clampX(placement.x + delta.x * ratio, placement.w),
        y: clampY(placement.y + delta.y * ratio, placement.h)
      });
    }
  };

  // Root and folder scopes are composed as an architectural map. Regions are
  // semantic, fixed in meaning, and packed to the current landscape viewport.
  // Connections are deliberately absent from this primary placement pass.
  if (layoutKey !== basePlacementKey) {
    basePlacements.clear();
    if (focusMode) {
      const seeded = [];
      const selectedFile = fileOf(focusItem);
      const focusSize = cardSize(selectedFile, true);
      const preserved = focusOrigin?.id === selectedFile.id ? focusOrigin : layoutMemory.get(selectedFile.id) || basePlacements.get(selectedFile.id);
      const centerX = Math.max(pad, Math.min(pad + usableWidth - focusSize.w, preserved?.x ?? pad + usableWidth * .5 - focusSize.w / 2));
      const centerY = Math.max(56, preserved?.y ?? 62 + viewportHeight * .44 - focusSize.h / 2);
      const place = (item, x, y, lane) => {
        const size = cardSize(item, true);
        const target = { x, y, w: size.w, h: size.h, lane };
        const placement = softenedPlacement(item, target, item.id === selectedFile.id);
        seeded.push(placement); basePlacements.set(item.id, placement);
      };
      place(selectedFile, centerX, centerY, 'focus');
      const others = focusFiles.filter(file => file.id !== selectedFile.id);
      const left = others.filter(file => connectionPressure(file, selectedFile).ratio <= .5);
      const right = others.filter(file => connectionPressure(file, selectedFile).ratio > .5);
      const distribute = (files, side) => files.forEach((file, index) => {
        const size = cardSize(file, true);
        const x = side === 'left' ? Math.max(pad, centerX - size.w - 150) : Math.min(pad + usableWidth - size.w, centerX + focusSize.w + 150);
        const y = centerY + (index - (files.length - 1) / 2) * (size.h + 34);
        place(file, x, Math.max(70, y), side === 'left' ? 'upstream' : 'downstream');
      });
      distribute(left, 'left'); distribute(right, 'right');
      const quiet = contextItems.filter(item => !focusFiles.some(file => file.id === item.id));
      quiet.forEach((item, index) => {
        const size = cardSize(item, true); const width = Math.min(224, size.w);
        // Quiet context is parked around the perimeter of the current frame,
        // rather than sent to a distant column or piled under the trace.
        const corners = [
          [pad + 18, 66], [pad + usableWidth - width - 18, 66],
          [pad + 18, Math.max(66, viewportHeight - size.h - 42)], [pad + usableWidth - width - 18, Math.max(66, viewportHeight - size.h - 42)]
        ];
        const corner = corners[index % corners.length], layer = Math.floor(index / corners.length);
        const x = corner[0] + (layer % 2) * (width + 18) * (corner[0] < centerX ? 1 : -1);
        const y = corner[1] + layer * (size.h + 18) * (corner[1] < centerY ? 1 : -1);
        const target = {
          x: Math.max(pad, Math.min(pad + usableWidth - width, x)),
          y: Math.max(56, Math.min(viewportHeight - size.h - 26, y)),
          w: width, h: size.h, lane: 'context'
        };
        const placement = softenedPlacement(item, target);
        seeded.push(placement); basePlacements.set(item.id, placement);
      });
    } else {
    const regions = new Map();
    for (const item of contextItems) {
      const region = mapRegion(item); const list = regions.get(region) || [];
      list.push(item); regions.set(region, list);
    }
    const slots = {
      // A deliberate, magazine-like composition: core architecture lives at
      // the top and centre; supporting material frames it rather than cutting
      // through it. This remains useful on both compact and ultrawide screens.
      application: [0.04, 0.09, 0.30, 0.25], package: [0.66, 0.09, 0.30, 0.25], service: [0.35, 0.40, 0.30, 0.24],
      infrastructure: [0.04, 0.62, 0.42, 0.28], docs: [0.62, 0.62, 0.34, 0.24], context: [0.34, 0.10, 0.32, 0.24],
      generated: [0.62, 0.84, 0.34, 0.16], test: [0.35, 0.76, 0.27, 0.18]
    };
    const seeded = [];
    for (const [region, items] of [...regions.entries()].sort(([a], [b]) => (mapRegionPriority[a] ?? 9) - (mapRegionPriority[b] ?? 9))) {
      const slot = slots[region] || slots.context;
      const slotX = pad + usableWidth * slot[0], slotY = 56 + viewportHeight * slot[1];
      const slotW = Math.max(minColumn, usableWidth * slot[2]), slotH = Math.max(140, viewportHeight * slot[3]);
      const ranked = [...items].sort((a, b) => primaryTraceScore(b) - primaryTraceScore(a) || a.label.localeCompare(b.label));
      const compact = ['infrastructure', 'docs', 'generated', 'test', 'context'].includes(region);
      const localGap = compact ? 20 : gap;
      const compactWidth = Math.max(196, Math.min(236, (slotW - localGap) / 2));
      const cellW = compact ? compactWidth : Math.min(Math.max(minColumn, slotW / Math.min(2, Math.ceil(Math.sqrt(ranked.length)))), maxColumn);
      const columns = compact ? Math.max(1, Math.min(2, Math.floor((slotW + localGap) / (cellW + localGap)))) : Math.max(1, Math.min(2, Math.floor((slotW + gap) / (cellW + gap))));
      ranked.forEach((item, index) => {
        const size = cardSize(item, true);
        const width = compact ? Math.min(cellW, slotW) : Math.min(Math.max(size.w, minColumn), Math.max(minColumn, slotW));
        const column = index % columns, row = Math.floor(index / columns);
        let x = slotX + column * (width + localGap);
        let y = slotY + row * (size.h + localGap);
        x = Math.max(pad, Math.min(pad + usableWidth - width, x));
        // Small local refinement only: strong architectural neighbours sit
        // closer, but never leave their semantic region.
        const pressure = connectionPressure(item, anchor);
        if (pressure.total) x += (pressure.ratio - .5) * Math.min(34, slotW * .12);
        let attempts = 0;
        while (seeded.some(other => collides({ x, y, w: width, h: size.h }, other, 22, localGap)) && attempts++ < 24) y += size.h + localGap;
        const placement = softenedPlacement(item, { x, y, w: width, h: size.h, lane: region });
        seeded.push(placement); basePlacements.set(item.id, placement);
      });
    }
    }
    basePlacementKey = layoutKey;
  }
  relaxTraceSprings(contextItems);

  // Expand in place. Only cards that physically collide with the enlarged
  // container are pushed down; unrelated clusters never get re-laid out.
  const flowOrder = [...contextItems].sort((a, b) => {
    const ap = basePlacements.get(a.id), bp = basePlacements.get(b.id);
    return (ap?.y || 0) - (bp?.y || 0) || (ap?.x || 0) - (bp?.x || 0);
  });
  for (const item of flowOrder) {
    const base = basePlacements.get(item.id);
    const size = cardSize(item);
    const width = Math.min(Math.max(size.w, minColumn), maxColumn);
    let x = base?.x ?? pad;
    let y = base?.y ?? 132;
    // The clicked file is a physical anchor. It is never collision-resolved;
    // every other card yields around it.
    if (focusMode && item.id === focusedFileId) {
      placements.push({ item, x, y, w: width, h: size.h, lane: 'focus' });
      continue;
    }
    const resolved = openSpot({ x, y, w: width, h: size.h, lane: roleFor(item) }, placements, true);
    placements.push({ item, ...resolved });
  }
  const rows = placements.map(placement => placement.y + placement.h);
  const boundariesByKey = new Map();
  for (const placement of placements) {
    const group = groupFolder(placement.item, current); const key = `${group.id}:${placement.lane}`; placement.groupId = group.id; placement.boundaryKey = key;
    const list = boundariesByKey.get(key) || { key, group, lane: placement.lane, placements: [] }; list.placements.push(placement); boundariesByKey.set(key, list);
  }
  const boundaries = [...boundariesByKey.values()].filter(group => {
    if (group.group.id === current.id) return current.depth > 0 && group.placements.length > 1;
    return group.group.kind === 'folder' && group.placements.length > 1;
  }).map(group => {
    const boxes = group.placements.map(placement => { const offset = offsets.get(placement.item.id) || { x: 0, y: 0 }; return { left: placement.x + offset.x, top: placement.y + offset.y, right: placement.x + offset.x + placement.w, bottom: placement.y + offset.y + placement.h }; });
    const left = Math.min(...boxes.map(box => box.left)) - 18, top = Math.min(...boxes.map(box => box.top)) - 25, right = Math.max(...boxes.map(box => box.right)) + 18, bottom = Math.max(...boxes.map(box => box.bottom)) + 18;
    return { ...group, x: left, y: top, w: right - left, h: bottom - top, label: group.placements.length > 1 || current.depth > 0 };
  });
  return { placements, boundaries, w: Math.max(worldWidth + pad, ...placements.map(item => item.x + item.w + pad)), h: Math.max(720, ...rows) + 92 };
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
function diffHtml(file) {
  const diff = file.git?.diff; if (!file.git?.change) return '';
  if (!diff) return `<section class="diff"><header><b>LOCAL CHANGE</b></header><pre>New or untracked file. Source is available above.</pre></section>`;
  return `<section class="diff"><header><b>LOCAL DIFF</b></header><pre>${diff.split('\n').slice(0, 90).map(line => `<span class="${line.startsWith('+') ? 'add' : line.startsWith('-') ? 'remove' : ''}">${escape(line)}</span>`).join('')}</pre></section>`;
}
function diffPreviewHtml(file) {
  return '';
}
function folderRowsHtml(item, depth = 0) {
  if (!expandedFolders.has(item.id) || depth > 4) return '';
  const rows = folderItems(item).slice(0, 18).map(child => {
    if (child.kind === 'folder') {
      const nested = expandedFolders.has(child.id) ? `<div class="folder-contents nested">${folderRowsHtml(child, depth + 1)}</div>` : '';
      const childFolders = children(child.id).filter(entry => entry.kind === 'folder').length;
      return `<section class="folder-nest folder-tile ${expandedFolders.has(child.id) ? 'expanded' : ''} ${selectedId === child.id ? 'selected' : ''} ${traceActive() && !hasTrace(child) ? 'dim' : ''}" data-inline="${child.id}" data-kind="folder" data-id="${child.id}" style="--node:${color(child.path || child.label)}"><span class="port edge-port in endpoint-port ${pinned.has(child.id) ? 'pinned' : ''}" data-pin="${child.id}" data-port-for="${child.id}" data-port-side="in" title="Folder input"></span><span class="port edge-port out endpoint-port ${pinned.has(child.id) ? 'pinned' : ''}" data-pin="${child.id}" data-port-for="${child.id}" data-port-side="out" title="Folder output"></span><button class="folder-row folder-tile-head" data-inline="${child.id}" data-kind="folder"><i></i><span title="${escape(child.path || child.label)}">${expandedFolders.has(child.id) ? '⌄ ' : '› '}${escape(child.label)}</span><em>${filesBelow(child).length} files${childFolders ? ` · ${childFolders} folders` : ''}</em><span class="port ${pinned.has(child.id) ? 'pinned' : ''}" data-pin="${child.id}" title="Pin trace"></span></button>${nested}</section>`;
    }
    return inlineFileCardHtml(child);
  }).join('');
  return rows || '<div class="folder-empty">No files in this folder.</div>';
}
function inlineFileCardHtml(file) {
  const expanded = shouldInlineExpandFile(file);
  const selectedClass = selectedId === file.id || fileOf(selected())?.id === file.id ? 'selected' : '';
  const traceClass = traceActive() && !hasTrace(file) ? 'dim' : '';
  const imports = importSummaries(file);
  const offset = offsets.get(file.id) || { x: 0, y: 0 };
  return `<section class="inline-file-card ${expanded ? 'expanded' : ''} ${selectedClass} ${traceClass}" data-inline="${file.id}" data-drag-id="${file.id}" data-kind="file" data-inline-file="${file.id}" style="--node:${color(file.path || file.label)};translate:${offset.x}px ${offset.y}px">
    <span class="port edge-port in endpoint-port ${pinned.has(file.id) ? 'pinned' : ''}" data-pin="${file.id}" data-port-for="${file.id}" data-port-side="in" title="File input"></span>
    <span class="port edge-port out endpoint-port ${pinned.has(file.id) ? 'pinned' : ''}" data-pin="${file.id}" data-port-for="${file.id}" data-port-side="out" title="File output"></span>
    <button class="inline-file-head" data-inline="${file.id}" data-kind="file" data-inline-file="${file.id}">
      <span class="file-chevron">${expanded ? '⌄' : '›'}</span><b title="${escape(file.path)}">${escape(file.label)}</b><em>${file.meta?.loc || 0} lines · ${modules(file).length} modules</em><span class="port ${pinned.has(file.id) ? 'pinned' : ''}" data-pin="${file.id}" title="Pin file trace"></span>
    </button>
    ${expanded ? inlineFileDetails(file, imports) : ''}
  </section>`;
}
function inlineFileDetails(file, importEdges = importSummaries(file)) {
  const imports = importEdges.map(edge => `<button class="inline-import ${selectedImportEdgeId === edge.id ? 'selected' : ''} ${traceActive() && !traceEdges.has(edge.id) ? 'dim' : ''}" data-inline-import="${edge.id}" title="${escape(edge.evidence)}"><span>import</span><b>${escape(edge.evidence)}</b></button>`).join('');
  const moduleRows = displayModules(file).map(module => moduleHtml(file, module, true)).join('');
  return `<div class="inline-file-detail">${imports ? `<div class="inline-imports">${imports}</div>` : ''}<div class="inline-modules">${moduleRows || '<span class="inline-empty">No semantic modules found.</span>'}</div></div>`;
}
function moduleHtml(file, module, inline = false) {
  const expanded = expandedModules.has(module.id);
  const klass = inline ? 'inline-module' : 'module';
  const inlineAttr = inline ? `data-inline-module="${module.id}"` : '';
  return `<section class="module-block ${expanded ? 'expanded' : ''} ${selectedId === module.id ? 'selected' : ''} ${selected()?.kind === 'module' && !hasTrace(module) ? 'dim' : ''}">
    <button class="${klass}" data-module="${module.id}" data-drag-id="${file.id}" data-drag-anchor="${module.id}" ${inlineAttr}>
      <span class="port edge-port in ${pinned.has(module.id) ? 'pinned' : ''}" data-pin="${module.id}" data-port-for="${module.id}" data-port-side="in"></span>
      <b>${expanded ? '⌄ ' : '› '}${escape(module.label)}()</b><em>line ${module.loc.start}</em>
      <span class="port edge-port out ${pinned.has(module.id) ? 'pinned' : ''}" data-pin="${module.id}" data-port-for="${module.id}" data-port-side="out"></span>
    </button>
    ${expanded ? moduleSourceHtml(file, module) : ''}
  </section>`;
}
function fileHtml(file, placement) {
  const offset = offsets.get(file.id) || { x: 0, y: 0 }; const traceClass = traceActive() && !hasTrace(file) ? 'dim' : ''; const selectedClass = selectedId === file.id || fileOf(selected())?.id === file.id ? 'selected' : ''; const expanded = expandedFiles.has(file.id); const list = modules(file); const liveClass = recentFor(file) ? 'live-changed' : ''; const focusClass = focusedFileId === file.id ? 'focus-anchor' : '';
  return `<article class="card file-card ${expanded ? 'expanded' : ''} ${traceClass} ${selectedClass} ${liveClass} ${focusClass}" data-id="${file.id}" data-drag-id="${file.id}" data-kind="file" data-parent="${file.parentId}" data-group="${placement.groupId}" data-boundary="${placement.boundaryKey}" style="left:${placement.x}px;top:${placement.y}px;width:${placement.w}px;--node:${color(file.path)};translate:${offset.x}px ${offset.y}px"><span class="port edge-port in endpoint-port ${pinned.has(file.id) ? 'pinned' : ''}" data-pin="${file.id}" data-port-for="${file.id}" data-port-side="in" title="File input"></span><span class="port edge-port out endpoint-port ${pinned.has(file.id) ? 'pinned' : ''}" data-pin="${file.id}" data-port-for="${file.id}" data-port-side="out" title="File output"></span><div class="file-head"><button class="chevron" data-expand="${file.id}" title="${expanded ? 'Collapse modules' : 'Show modules'}">${expanded ? '⌄' : '›'}</button><small class="file-path">${escape(file.path)}</small><b>${escape(file.label)}</b><span>${file.meta?.loc || 0} lines · ${list.length} modules · ${relationshipCount(file)} links</span><button class="port ${pinned.has(file.id) ? 'pinned' : ''}" data-pin="${file.id}" title="Pin file trace"></button>${file.git?.change ? `<button class="change" data-diff="${file.id}">${escape(file.git.change)} diff</button>` : ''}</div>${diffPreviewHtml(file)}${expanded ? `<div class="module-list">${displayModules(file).map(module => moduleHtml(file, module)).join('') || '<div class="module">No semantic modules found.</div>'}</div>${diffHtml(file)}` : ''}</article>`;
}
function folderHtml(item, placement) {
  const offset = offsets.get(item.id) || { x: 0, y: 0 }; const traceClass = traceActive() && !hasTrace(item) ? 'dim' : ''; const nested = children(item.id).filter(child => child.kind === 'folder').length; const files = filesBelow(item).length; const live = recentDescendants(item).length; const expanded = expandedFolders.has(item.id);
  return `<article class="card folder-card ${expanded ? 'expanded' : ''} ${traceClass} ${selectedId === item.id ? 'selected' : ''} ${live ? 'live-changed' : ''}" data-id="${item.id}" data-drag-id="${item.id}" data-kind="folder" data-parent="${item.parentId}" data-group="${placement.groupId}" data-boundary="${placement.boundaryKey}" style="left:${placement.x}px;top:${placement.y}px;width:${placement.w}px;--node:${color(item.path)};translate:${offset.x}px ${offset.y}px"><span class="port edge-port in endpoint-port ${pinned.has(item.id) ? 'pinned' : ''}" data-pin="${item.id}" data-port-for="${item.id}" data-port-side="in" title="Folder input"></span><span class="port edge-port out endpoint-port ${pinned.has(item.id) ? 'pinned' : ''}" data-pin="${item.id}" data-port-for="${item.id}" data-port-side="out" title="Folder output"></span><header><button class="folder-toggle" data-folder-expand="${item.id}" title="${expanded ? 'Collapse folder' : 'Reveal files'}">${expanded ? '⌄' : '›'}</button><b>${escape(item.label)}</b><small>${live ? `${live} live` : files}</small><button class="folder-pin ${pinned.has(item.id) ? 'pinned' : ''}" data-pin="${item.id}" title="Pin folder trace">•</button><p><strong>${escape(mapRegion(item))}</strong>${nested ? ` · ${nested} folders` : ''} · ${files} files · ${relationshipCount(item)} links${live ? ` · ${live} changed` : ''}</p></header>${expanded ? `<div class="folder-contents">${folderRowsHtml(item)}</div>` : ''}</article>`;
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
function render() {
  if (!graph) return;
  const previousFocusRect = focusAnchorElement()?.getBoundingClientRect();
  const previousRects = new Map([...scene.querySelectorAll('.card[data-id], .zone[data-zone]')].map(element => [element.dataset.id ? `card:${element.dataset.id}` : `zone:${element.dataset.zone}`, element.getBoundingClientRect()]));
  rememberLayoutPositions();
  const layout = automaticLayout(); world.style.width = `${layout.w}px`; world.style.height = `${layout.h}px`;
  const zones = layout.boundaries.map(zone => `<div class="zone" data-zone="${zone.key}" style="left:${zone.x}px;top:${zone.y}px;width:${zone.w}px;height:${zone.h}px;--zone:${color(zone.group.path)}"></div>${zone.label ? `<div class="zone-label" style="left:${zone.x + 9}px;top:${zone.y + 7}px;--zone:${color(zone.group.path)}"><i></i><b title="${escape(zone.group.path || zone.group.label)}">${escape(zone.group.label)}</b><small>${zone.lane === 'in' ? 'upstream' : zone.lane === 'out' ? 'downstream' : zone.lane === 'focus' ? 'focus' : roleFor(zone.group)}</small></div>` : ''}`).join('');
  scene.innerHTML = zones + layout.placements.map(placement => placement.item.kind === 'folder' ? folderHtml(placement.item, placement) : fileHtml(placement.item, placement)).join('');
  lockFocusedAnchor(previousFocusRect);
  bindScene(); applyCanvas(); drawEdges(); animateReflowEdges(5200); renderMinimap(); renderActivityFeed();
  // Rendering is deliberately stateless, so use FLIP to make a changed layout
  // read as objects being gently pushed aside rather than being recreated.
  requestAnimationFrame(() => {
    for (const element of scene.querySelectorAll('.card[data-id], .zone[data-zone]')) {
      const key = element.dataset.id ? `card:${element.dataset.id}` : `zone:${element.dataset.zone}`;
      const before = previousRects.get(key); if (!before) continue;
      const after = element.getBoundingClientRect();
      const dx = (before.left - after.left) / canvas.scale, dy = (before.top - after.top) / canvas.scale;
      if (Math.abs(dx) < .5 && Math.abs(dy) < .5) continue;
      const item = element.dataset.id ? node(element.dataset.id) : null;
      const duration = element.classList.contains('focus-anchor') ? 0 : item && hasTrace(item) ? 5000 : 8000;
      if (duration) element.animate([{ transform: `translate(${dx}px, ${dy}px)` }, { transform: 'translate(0, 0)' }], { duration, easing: 'cubic-bezier(.16, 1, .3, 1)' });
    }
  });
}
function folderOwnsEndpoint(folder) {
  return !expandedFolders.has(folder.id);
}
function fileOwnsEndpoint(file) {
  return !(expandedFiles.has(file.id) || shouldInlineExpandFile(file));
}
function endpointFor(edge, side) {
  const id = side === 'from' ? edge.from : edge.to; const item = node(id); const file = fileOf(item);
  const sourcePort = `source:${edge.id}:${side === 'from' ? 'out' : 'in'}`;
  if (scene.querySelector(`[data-source-port="${CSS.escape(sourcePort)}"]`)) return sourcePort;
  if (item?.kind === 'module' && scene.querySelector(`[data-inline-module="${CSS.escape(item.id)}"]`)) return `inline-module:${item.id}`;
  if (item?.kind === 'module' && expandedFiles.has(item.fileId) && scene.querySelector(`[data-module="${item.id}"]`)) return `module:${item.id}`;
  if (file && fileOwnsEndpoint(file) && scene.querySelector(`[data-inline-file="${CSS.escape(file.id)}"]`)) return `inline:${file.id}`;
  if (file && fileOwnsEndpoint(file) && scene.querySelector(`[data-id="${CSS.escape(file.id)}"]`)) return file.id;
  const visible = nearestVisibleFolder(file || item);
  if (visible && folderOwnsEndpoint(visible)) return visible.id;
  return null;
}
function isDetailedEndpoint(id) {
  return id?.startsWith('inline-module:') || id?.startsWith('module:') || id?.startsWith('source:');
}
function sameModuleOrInternalContainer(edge) {
  if (edge.from === edge.to) return true;
  const from = node(edge.from), to = node(edge.to);
  const fromFile = fileOf(from), toFile = fileOf(to);
  if (!fromFile || !toFile || fromFile.id !== toFile.id) return false;
  if (from?.kind === 'module' && to?.kind === 'module' && from.id === to.id) return true;
  return (from?.kind === 'file' && to?.kind === 'module') || (from?.kind === 'module' && to?.kind === 'file');
}
function markEndpoint(id, side) {
  const selector = id.startsWith('source:') ? `[data-source-port="${CSS.escape(id)}"]` : id.startsWith('inline-module:') ? `[data-inline-module="${CSS.escape(id.slice(14))}"]` : id.startsWith('module:') ? `[data-module="${CSS.escape(id.slice(7))}"]` : id.startsWith('inline:') ? `[data-inline-file="${CSS.escape(id.slice(7))}"]` : `[data-id="${CSS.escape(id)}"]`;
  const element = scene.querySelector(selector); if (!element) return;
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
function showOverviewEdge(edge) {
  // The overview should communicate the main architecture, not every incidental
  // test/config/import relationship. Detail appears naturally as containers open.
  if (folder()?.depth > 0 || expandedFolders.size || expandedFiles.size || expandedModules.size || pinned.size) return true;
  const fromRegion = mapRegion(fileOf(node(edge.from)) || node(edge.from));
  const toRegion = mapRegion(fileOf(node(edge.to)) || node(edge.to));
  const core = new Set(['application', 'service', 'package']);
  return core.has(fromRegion) && core.has(toRegion);
}
function moduleBusPath(a, b, spread, cross, backwards) {
  const lanePad = 34 + Math.min(46, Math.abs(cross) * .55);
  const sourceLaneX = a.x + (backwards ? -lanePad : lanePad);
  const targetLaneX = b.x + (backwards ? lanePad : -lanePad);
  const midY = (a.y + b.y) / 2 + cross;
  return `M ${a.x} ${a.y + spread * .18} C ${sourceLaneX} ${a.y + spread * .18}, ${sourceLaneX} ${midY}, ${sourceLaneX} ${midY} L ${targetLaneX} ${midY} C ${targetLaneX} ${midY}, ${targetLaneX} ${b.y + spread * .18}, ${b.x} ${b.y + spread * .18}`;
}
function drawEdges() {
  wires.innerHTML = '';
  scene.querySelectorAll('.connected-port').forEach(port => port.classList.remove('connected-port'));
  const unique = new Map();
  for (const edge of edgeTypes()) {
    if (!traceEdges.has(edge.id)) continue;
    if (!showOverviewEdge(edge)) continue;
    if (sameModuleOrInternalContainer(edge)) continue;
    const from = endpointFor(edge, 'from'), to = endpointFor(edge, 'to'); if (!from || !to || from === to) continue;
    const key = isDetailedEndpoint(from) || isDetailedEndpoint(to) ? edge.id : `${from}:${to}:${edge.type}`;
    if (!unique.has(key)) unique.set(key, { ...edge, from, to });
  }
  const rendered = [...unique.values()].map((edge, index) => ({ edge, index, a: point(edge.from, 'out'), b: point(edge.to, 'in') })).filter(item => item.a && item.b);
  const relaxedFocus = !!draggingTraceAnchorId || (!!focusedFileId && (selected()?.kind === 'module' || selected()?.kind === 'file'));
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
    const spread = (pairIndex - (total - 1) / 2) * Math.min(18, Math.max(8, 42 / total));
    const cross = crossOffsets.get(edge.id) || 0;
    const span = Math.max(58, Math.min(230, Math.abs(b.x - a.x) * .5));
    const backwards = b.x < a.x;
    const bend = (backwards ? 110 + (index % 3) * 24 : 0) + spread + cross;
    const startY = a.y + spread * .3 + cross * .22, endY = b.y + spread * .3 - cross * .22;
    const midLift = cross * .65;
    const moduleRoute = !relaxedFocus && (usesModulePort(edge.from) || usesModulePort(edge.to));
    // In focused tracing, a single Bézier segment continuously relaxes toward
    // the least-kinked route as endpoints move. The stage layout keeps this
    // clean curve in an unobstructed central corridor.
    const focusHandle = Math.max(76, Math.min(300, Math.abs(b.x - a.x) * .46));
    const focusDirection = b.x >= a.x ? 1 : -1;
    const pathData = relaxedFocus
      ? `M ${a.x} ${a.y} C ${a.x + focusDirection * focusHandle} ${a.y}, ${b.x - focusDirection * focusHandle} ${b.y}, ${b.x} ${b.y}`
      : moduleRoute ? moduleBusPath(a, b, spread, cross, backwards) : backwards
      ? `M ${a.x} ${startY} C ${a.x + span} ${startY + bend}, ${b.x - span} ${endY + bend + midLift}, ${b.x} ${endY}`
      : `M ${a.x} ${startY} C ${a.x + span} ${startY + spread + cross}, ${b.x - span} ${endY + spread - cross}, ${b.x} ${endY}`;
    const path = document.createElementNS('http://www.w3.org/2000/svg', 'path'); path.setAttribute('d', pathData); path.setAttribute('class', `wire moving ${edge.type} ${moduleRoute ? 'module-bus' : ''} ${Math.abs(cross) > 18 ? 'resolved-crossing' : ''}`); path.style.setProperty('--delay', `${index * -0.14}s`); path.append(Object.assign(document.createElementNS('http://www.w3.org/2000/svg', 'title'), { textContent: `${edge.type}: ${edge.evidence}` })); wires.append(path);
  });
}
function point(id, side) {
  const selector = id.startsWith('source:') ? `[data-source-port="${CSS.escape(id)}"]` : id.startsWith('inline-module:') ? `[data-inline-module="${CSS.escape(id.slice(14))}"]` : id.startsWith('module:') ? `[data-module="${CSS.escape(id.slice(7))}"]` : id.startsWith('inline:') ? `[data-inline-file="${CSS.escape(id.slice(7))}"]` : `[data-id="${CSS.escape(id)}"]`;
  const element = scene.querySelector(selector); if (!element) return null; const worldRect = world.getBoundingClientRect(), rect = element.getBoundingClientRect();
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
function bindDrag(card) {
  let drag;
  card.addEventListener('pointerdown', event => {
    const isModuleHandle = !!card.dataset.module;
    if (event.button !== 0 || event.target.closest('[data-pin]') || (event.target.closest('button,a') && !isModuleHandle)) return;
    event.stopPropagation(); const item = node(card.dataset.dragId);
    const topCard = scene.querySelector(`.card[data-id="${CSS.escape(card.dataset.dragId)}"]`);
    const inlineCard = card.closest(`[data-inline-file="${CSS.escape(card.dataset.dragId)}"]`);
    const dragElement = topCard || inlineCard || card.closest('.card[data-id]') || card;
    const members = visibleDragMembers(dragElement, item);
    draggingTraceAnchorId = item?.kind === 'file' ? item.id : fileOf(item)?.id || null;
    drag = { x: event.clientX, y: event.clientY, moved: false, remembered: false, members: members.map(member => ({ member, id: member.dataset.dragId, offset: offsets.get(member.dataset.dragId) || { x: 0, y: 0 }, boundary: member.dataset.boundary })) };
    card.setPointerCapture(event.pointerId); dragElement.classList.add('dragging'); app.classList.add('dragging');
  });
  card.addEventListener('pointermove', event => {
    if (!drag) return; const dx = (event.clientX - drag.x) / canvas.scale, dy = (event.clientY - drag.y) / canvas.scale; drag.moved ||= Math.abs(dx) + Math.abs(dy) > 3; if (drag.moved && !drag.remembered) { remember(); drag.remembered = true; }
    const zones = new Set(); for (const item of drag.members) { const value = { x: item.offset.x + dx, y: item.offset.y + dy }; offsets.set(item.id, value); item.member.style.translate = `${value.x}px ${value.y}px`; if (item.boundary) zones.add(item.boundary); } resizeZones(zones); scheduleDraw(); animateReflowEdges(180);
  });
  const end = event => {
    if (!drag) return;
    const moved = drag.moved;
    const item = node(card.dataset.dragId);
    const topCard = scene.querySelector(`.card[data-id="${CSS.escape(card.dataset.dragId)}"]`);
    const inlineCard = card.closest(`[data-inline-file="${CSS.escape(card.dataset.dragId)}"]`);
    const dragElement = topCard || inlineCard || card.closest('.card[data-id]') || card;
    if (moved) { card.dataset.dragged = String(Date.now()); dragElement.dataset.dragged = card.dataset.dragged; event?.preventDefault(); }
    drag = null; dragElement.classList.remove('dragging'); app.classList.remove('dragging');
    draggingTraceAnchorId = null;
    if (moved && settleDragAnchor(item)) render();
    else { drawEdges(); renderMinimap(); }
  };
  card.addEventListener('pointerup', end); card.addEventListener('pointercancel', end);
}
function bindScene() {
  scene.querySelectorAll('[data-drag-id]').forEach(bindDrag);
  scene.querySelectorAll('[data-folder-expand]').forEach(button => button.addEventListener('click', event => { event.stopPropagation(); const id = button.dataset.folderExpand; remember(); const item = node(id); requestLayoutSettle(item); expandedFolders.has(id) ? expandedFolders.delete(id) : expandedFolders.add(id); selectItem(id); render(); updateInspector(); }));
  scene.querySelectorAll('[data-inline]').forEach(row => {
    row.addEventListener('click', event => {
      if (event.target.closest('[data-pin]') || Date.now() - Number(row.dataset.dragged || 0) < 240) return;
      event.stopPropagation();
      const item = node(row.dataset.inline); if (!item) return;
      if (item.kind === 'file') activateFocus(item);
      selectItem(item.id);
      layoutAnchorFileId = item.kind === 'file' ? item.id : layoutAnchorFileId;
      rebuildTrace(); render(); updateInspector();
    });
    row.addEventListener('dblclick', event => { event.stopPropagation(); const item = node(row.dataset.inline); if (!item) return; remember(); requestLayoutSettle(item); if (item.kind === 'file') { layoutAnchorFileId = item.id; expandedFiles.add(item.id); } else expandedFolders.add(item.id); render(); updateInspector(); });
  });
  scene.querySelectorAll('[data-inline-import]').forEach(row => row.addEventListener('click', event => {
    event.stopPropagation(); remember(); selectedImportEdgeId = row.dataset.inlineImport;
    const edge = edgeTypes().find(item => item.id === selectedImportEdgeId); const file = fileOf(node(edge?.from)) || fileOf(node(edge?.to));
    if (file) selectedId = file.id;
    rebuildTrace(); render(); updateInspector();
  }));
  scene.querySelectorAll('[data-expand]').forEach(button => button.addEventListener('click', event => { event.stopPropagation(); const id = button.dataset.expand; remember(); const item = node(id); requestLayoutSettle(item); layoutAnchorFileId = id; expandedFiles.has(id) ? (expandedFiles.delete(id), sourceFiles.delete(id)) : expandedFiles.add(id); render(); }));
  scene.querySelectorAll('[data-source]').forEach(button => button.addEventListener('click', event => { event.stopPropagation(); const id = button.dataset.source; remember(); const item = node(id); requestLayoutSettle(item); layoutAnchorFileId = id; expandedFiles.add(id); sourceFiles.has(id) ? sourceFiles.delete(id) : sourceFiles.add(id); render(); }));
  scene.querySelectorAll('[data-diff]').forEach(button => button.addEventListener('click', event => { event.stopPropagation(); selectItem(button.dataset.diff); }));
  scene.querySelectorAll('[data-pin]').forEach(button => button.addEventListener('click', event => { event.stopPropagation(); const id = button.dataset.pin; remember(); pinned.has(id) ? pinned.delete(id) : pinned.add(id); rebuildTrace(); render(); updateInspector(); }));
  scene.querySelectorAll('[data-module]').forEach(element => {
    element.addEventListener('click', event => { if (event.target.closest('[data-pin]') || Date.now() - Number(element.dataset.dragged || 0) < 240) return; event.stopPropagation(); const module = node(element.dataset.module); requestLayoutSettle(module); selectItem(module.id); render(); });
    element.addEventListener('dblclick', event => {
      event.stopPropagation(); const module = node(element.dataset.module); if (!module) return;
      remember(); requestLayoutSettle(module); layoutAnchorFileId = module.fileId; expandedFiles.add(module.fileId);
      expandedModules.has(module.id) ? expandedModules.delete(module.id) : expandedModules.add(module.id);
      render(); updateInspector();
    });
  });
  scene.querySelectorAll('.card[data-id]').forEach(card => { card.addEventListener('click', event => { if (Date.now() - Number(card.dataset.dragged || 0) < 240 || event.target.closest('button,[data-module],[data-inline]')) return; const item = node(card.dataset.id); requestLayoutSettle(item); selectItem(card.dataset.id); render(); }); card.addEventListener('dblclick', event => { if (event.target.closest('button,[data-module],[data-inline]')) return; const item = node(card.dataset.id); remember(); requestLayoutSettle(item); if (item.kind === 'folder') expandedFolders.has(item.id) ? expandedFolders.delete(item.id) : expandedFolders.add(item.id); else { layoutAnchorFileId = item.id; expandedFiles.add(item.id); sourceFiles.add(item.id); } render(); updateInspector(); }); });
}
function bindActivityFeed() {
  $('#activity-list')?.querySelectorAll('[data-open-change]').forEach(button => button.addEventListener('click', event => {
    event.stopPropagation(); const file = fileForPath(button.dataset.openChange); if (!file) return;
    remember(); selectedId = file.id; layoutAnchorFileId = file.id; flowMode = true; expandedFiles.add(file.id);
    for (const parent of ancestors(file).filter(item => item.kind === 'folder').slice(-3)) expandedFolders.add(parent.id);
    rebuildTrace(); render(); updateInspector();
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
  scene.querySelectorAll('.card[data-id]').forEach(card => {
    const item = node(card.dataset.id);
    card.classList.toggle('selected', card.dataset.id === selectedId || card.dataset.id === selectedFile?.id);
    card.classList.toggle('dim', traceActive() && !hasTrace(item));
  });
  scene.querySelectorAll('[data-module]').forEach(element => element.classList.toggle('selected', element.dataset.module === selectedId));
  scene.querySelectorAll('[data-module]').forEach(element => element.classList.toggle('dim', selected()?.kind === 'module' && !hasTrace(node(element.dataset.module))));
  scene.querySelectorAll('[data-inline]').forEach(element => {
    const item = node(element.dataset.inline);
    element.classList.toggle('selected', element.dataset.inline === selectedId || fileOf(selected())?.id === element.dataset.inline);
    element.classList.toggle('dim', traceActive() && !hasTrace(item));
  });
  const activeModule = selected()?.kind === 'module' ? selected() : null;
  document.querySelectorAll('.line[data-line]').forEach(line => {
    const n = Number(line.dataset.line);
    const hasBadge = !!line.querySelector('.line-badge');
    line.classList.toggle('dim', !!activeModule && line.dataset.file === activeModule.fileId && (n < activeModule.loc.start || n > activeModule.loc.end) && !hasBadge);
  });
}
function selectItem(id) {
  if (selectedId !== id) remember();
  selectedId = id; selectedImportEdgeId = undefined; rebuildTrace(); refreshFocusClasses(); drawEdges(); renderMinimap(); updateInspector();
}
function updateInspector() {
  const item = selected() || entryFile(); if (!item) return; const file = fileOf(item) || item; const related = edgeTypes().filter(edge => edge.from === item.id || edge.to === item.id || edge.from === file.id || edge.to === file.id);
  $('#inspect-kind').textContent = `${item.kind.toUpperCase()} · ${traceActive() && hasTrace(item) ? 'ACTIVE TRACE' : isInfrastructure(file) ? 'INFRASTRUCTURE' : 'CONTEXT'}`; $('#inspect-title').textContent = item.kind === 'module' ? `${item.label}()` : item.label; $('#inspect-path').textContent = item.path || '/'; $('#inspect-trace').textContent = related.length ? `${related.length} semantic relationship${related.length === 1 ? '' : 's'} visible. Single click did not move the map.` : 'No direct semantic relationship was found.';
  $('#inspect-edges').innerHTML = related.slice(0, 9).map(edge => `<div><code>${edge.from === item.id ? '→' : '←'}</code> ${escape(edge.type)} · ${escape(edge.evidence)}${edge.line ? ` · line ${edge.line}` : ''}</div>`).join('') || '<div>No direct relationships.</div>';
  const sourcePanel = $('#source-panel'), sourceTarget = $('#inspect-source');
  if (file?.kind === 'file' && file.meta?.source) { sourcePanel.hidden = false; sourceTarget.innerHTML = sourceHtml(file); bindInspectorSource(); }
  else { sourcePanel.hidden = true; sourceTarget.innerHTML = ''; }
  if (item.kind === 'module') requestAnimationFrame(() => $('#inspect-source .line.active-module')?.scrollIntoView({ block: 'center', behavior: 'smooth' }));
  const panel = $('#diff-panel'); panel.hidden = !file.git?.change; $('#diff-code').textContent = file.git?.diff || 'New or untracked file. Full source is available in the canvas.';
}
function bindInspectorSource() {
  $('#inspect-source').querySelectorAll('[data-pin]').forEach(button => button.addEventListener('click', event => { event.stopPropagation(); const id = button.dataset.pin; remember(); pinned.has(id) ? pinned.delete(id) : pinned.add(id); rebuildTrace(); render(); updateInspector(); }));
}
function renderMinimap() {
  if (!graph) return; const w = 160, h = 104, scale = Math.min(w / Math.max(1, world.offsetWidth), h / Math.max(1, world.offsetHeight)); const zones = [...scene.querySelectorAll('.zone')].map(zone => `<i class="mini-zone" style="left:${zone.offsetLeft * scale}px;top:${zone.offsetTop * scale}px;width:${Math.max(4, zone.offsetWidth * scale)}px;height:${Math.max(4, zone.offsetHeight * scale)}px"></i>`).join(''); const cards = [...scene.querySelectorAll('.card')].map(card => `<i class="mini-node ${card.dataset.id === selectedId ? 'selected' : ''}" style="left:${(card.offsetLeft + card.offsetWidth / 2) * scale}px;top:${(card.offsetTop + card.offsetHeight / 2) * scale}px"></i>`).join(''); minimap.innerHTML = `${zones}${cards}<i class="mini-viewport" style="left:${-canvas.x * scale}px;top:${-canvas.y * scale}px;width:${board.clientWidth * scale / canvas.scale}px;height:${board.clientHeight * scale / canvas.scale}px"></i>`;
}
function fitMap() {
  const cards = [...scene.querySelectorAll('.card,.zone')]; if (!cards.length) return; const left = Math.min(...cards.map(card => card.offsetLeft)), top = Math.min(...cards.map(card => card.offsetTop)), right = Math.max(...cards.map(card => card.offsetLeft + card.offsetWidth)), bottom = Math.max(...cards.map(card => card.offsetTop + card.offsetHeight));
  canvas.scale = Math.min(1, Math.max(.35, Math.min((board.clientWidth - 48) / (right - left + 1), (board.clientHeight - 48) / (bottom - top + 1)))); canvas.x = board.clientWidth / 2 - (left + right) / 2 * canvas.scale; canvas.y = board.clientHeight / 2 - (top + bottom) / 2 * canvas.scale; applyCanvas();
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
  if (item.kind === 'module') return scene.querySelector(`[data-inline-module="${CSS.escape(item.id)}"],[data-module="${CSS.escape(item.id)}"]`);
  const file = fileOf(item);
  if (file) return scene.querySelector(`.card[data-id="${CSS.escape(file.id)}"]`) || scene.querySelector(`[data-inline-file="${CSS.escape(file.id)}"]`);
  return scene.querySelector(`.card[data-id="${CSS.escape(item.id)}"]`) || scene.querySelector(`.folder-tile[data-id="${CSS.escape(item.id)}"]`);
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
function resetPresentation() { remember(); offsets.clear(); basePlacements.clear(); layoutMemory.clear(); basePlacementKey = ''; focusOrigin = null; focusedFileId = null; flowMode = false; render(); requestAnimationFrame(fitMap); }
function canvasControls() {
  let pan, lastPanMoved = false, wheelRemainder = 0;
  const stopPan = () => { lastPanMoved = !!pan?.moved; pan = null; board.classList.remove('panning'); setTimeout(() => { lastPanMoved = false; }, 0); };
  board.addEventListener('pointerdown', event => { if (event.button !== 0 || event.target.closest('.card,button,#minimap')) return; pan = { x: event.clientX, y: event.clientY, left: canvas.x, top: canvas.y, moved: false }; board.classList.add('panning'); board.setPointerCapture(event.pointerId); });
  board.addEventListener('pointermove', event => { if (!pan) return; const dx = event.clientX - pan.x, dy = event.clientY - pan.y; pan.moved ||= Math.abs(dx) + Math.abs(dy) > 8; canvas.x = pan.left + dx; canvas.y = pan.top + dy; applyCanvas(); });
  board.addEventListener('pointerup', stopPan); board.addEventListener('pointercancel', stopPan);
  board.addEventListener('click', event => { if (event.target.closest('.card,button,#minimap') || lastPanMoved) return; const fallback = entryItem(folder()); if (!fallback) return; remember(); selectedId = fallback.id; selectedImportEdgeId = undefined; traceMode = true; flowMode = false; focusOrigin = null; focusedFileId = null; rebuildTrace(); render(); updateInspector(); syncToolbar(); });
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
  window.addEventListener('keydown', event => { if (event.key === 'Escape') { if (expandedModules.size) { remember(); expandedModules.clear(); render(); } else if (sourceFiles.size) { remember(); sourceFiles.clear(); render(); } else if (expandedFiles.size) { remember(); expandedFiles.clear(); render(); } else if (expandedFolders.size) { remember(); expandedFolders.clear(); render(); } else if (scopeId !== rootFolder().id) { remember(); scopeId = node(scopeId)?.parentId || rootFolder().id; layoutAnchorFileId = entryFile(folder())?.id; render(); } } });
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
  const theme = localStorage.getItem('deepflow-theme') || 'aurora';
  const motion = localStorage.getItem('deepflow-motion') !== 'reduced';
  autoRevealChanges = localStorage.getItem('deepflow-auto-reveal') === 'true';
  document.body.dataset.theme = theme;
  document.body.classList.toggle('reduce-motion', !motion);
  $('#motion-toggle').checked = motion;
  $('#auto-reveal-toggle').checked = autoRevealChanges;
  const syncThemeButtons = () => $('#theme-grid')?.querySelectorAll('[data-theme-choice]').forEach(button => button.classList.toggle('active', button.dataset.themeChoice === document.body.dataset.theme));
  syncThemeButtons();
  $('#settings-open')?.addEventListener('click', () => $('#settings-dialog')?.showModal?.());
  $('#theme-grid')?.querySelectorAll('[data-theme-choice]').forEach(button => button.addEventListener('click', () => {
    document.body.dataset.theme = button.dataset.themeChoice;
    localStorage.setItem('deepflow-theme', button.dataset.themeChoice);
    syncThemeButtons();
    renderMinimap();
  }));
  $('#motion-toggle')?.addEventListener('change', event => {
    document.body.classList.toggle('reduce-motion', !event.target.checked);
    localStorage.setItem('deepflow-motion', event.target.checked ? 'full' : 'reduced');
  });
  $('#auto-reveal-toggle')?.addEventListener('change', event => {
    autoRevealChanges = event.target.checked;
    localStorage.setItem('deepflow-auto-reveal', String(autoRevealChanges));
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
  const fresh = [...recentPaths.entries()].filter(([, at]) => Date.now() - at < 12_000).map(([path]) => path);
  if (!fresh.length) return;
  const changedFiles = fresh.map(path => graph.nodes.find(item => item.kind === 'file' && item.path === path)).filter(Boolean);
  const target = changedFiles.find(file => SOURCE_EXTENSIONS.has(file.extension)) || changedFiles[0];
  if (!target) return;
  for (const parent of ancestors(target).filter(item => item.kind === 'folder').slice(-3)) expandedFolders.add(parent.id);
  if (SOURCE_EXTENSIONS.has(target.extension)) expandedFiles.add(target.id);
  selectedId = target.id; layoutAnchorFileId = target.id; flowMode = true;
}
function fileByPath(path) {
  return graph?.nodes.find(item => item.kind === 'file' && item.path === String(path || '').replaceAll('\\', '/'));
}
function folderByPath(path) {
  const normalized = String(path || '').replaceAll('\\', '/').replace(/\/$/, '');
  return graph?.nodes.find(item => item.kind === 'folder' && item.path === normalized);
}
function revealItem(item, { moduleName, line, pin = false } = {}) {
  if (!item || !graph) return;
  remember();
  const file = item.kind === 'file' ? item : item.kind === 'module' ? fileOf(item) : null;
  const folderTarget = item.kind === 'folder' ? item : null;
  const targetFile = file || (folderTarget ? entryFile(folderTarget) : null);
  for (const parent of ancestors(file || folderTarget || item).filter(entry => entry.kind === 'folder')) expandedFolders.add(parent.id);
  if (folderTarget) expandedFolders.add(folderTarget.id);
  let target = item;
  if (targetFile) {
    expandedFiles.add(targetFile.id);
    layoutAnchorFileId = targetFile.id;
    const module = moduleName
      ? modules(targetFile).find(entry => entry.label === moduleName || `${entry.label}()` === moduleName)
      : line ? modules(targetFile).find(entry => line >= entry.loc.start && line <= entry.loc.end) : null;
    if (module) { expandedModules.add(module.id); target = module; }
  }
  selectedId = target.id;
  if (pin) pinned.add(target.id);
  flowMode = true;
  rebuildTrace(); render(); updateInspector(); syncToolbar();
  requestAnimationFrame(focusSelection);
}
function handleViewerCommand(command = {}) {
  if (command.type === 'clear-highlights') { remember(); pinned.clear(); recentPaths.clear(); rebuildTrace(); render(); updateInspector(); return; }
  if (command.type === 'highlight-paths') {
    remember();
    for (const path of command.paths || []) {
      const item = fileByPath(path) || folderByPath(path);
      if (!item) continue;
      if (command.pin) pinned.add(item.id);
      for (const parent of ancestors(item).filter(entry => entry.kind === 'folder')) expandedFolders.add(parent.id);
      if (item.kind === 'folder') expandedFolders.add(item.id);
      if (item.kind === 'file') expandedFiles.add(item.id);
      selectedId = item.id;
    }
    rebuildTrace(); render(); updateInspector(); syncToolbar(); requestAnimationFrame(focusSelection); return;
  }
  if (command.type === 'jump') {
    const item = fileByPath(command.path) || folderByPath(command.path);
    revealItem(item, { moduleName: command.module, line: command.line, pin: command.pin });
  }
}
function applyGraph(next, { preserve = false } = {}) {
  const previousSelected = selectedId, previousScope = scopeId, previousAnchor = layoutAnchorFileId; graph = next;
  if (!preserve) { offsets.clear(); basePlacements.clear(); layoutMemory.clear(); basePlacementKey = ''; focusOrigin = null; focusedFileId = null; expandedFiles.clear(); expandedFolders.clear(); expandedModules.clear(); sourceFiles.clear(); pinned.clear(); recentPaths.clear(); activityItems.clear(); archivedActivity.length = 0; flowMode = false; undoStack.length = 0; redoStack.length = 0; }
  scopeId = preserve && node(previousScope)?.kind === 'folder' ? previousScope : rootFolder().id; selectedId = preserve && node(previousSelected) ? previousSelected : entryItem(folder())?.id || rootFolder().id; layoutAnchorFileId = preserve && node(previousAnchor)?.kind === 'file' ? previousAnchor : fileOf(node(selectedId))?.id || entryFile(folder())?.id;
  if (preserve) revealRecentChanges();
  $('#repo-name').textContent = graph.roots.map(root => root.label).join(' + '); rebuildTrace(); render(); updateInspector(); updateHistory(); renderActivityFeed(); syncToolbar(); if (!preserve) fitMap();
}
async function loadGraph({ preserve = false } = {}) { const response = await fetch('/api/graph', { method: 'POST', headers: { 'content-type': 'application/json' }, body: JSON.stringify({}) }); if (!response.ok) throw new Error(await response.text()); sourceMode = 'live'; if ($('#tracking-status')) $('#tracking-status').textContent = 'live local map'; applyGraph(await response.json(), { preserve }); }
initSettings();
$('#history-back').addEventListener('click', () => moveHistory(true)); $('#history-forward').addEventListener('click', () => moveHistory(false)); $('#reset-view').addEventListener('click', resetPresentation); $('#open-workspace').addEventListener('click', showOpenDialog); $('#choose-folder').addEventListener('click', openWorkspace); $('#copy-mcp').addEventListener('click', async () => { await navigator.clipboard?.writeText($('#mcp-snippet').textContent); $('#copy-mcp').textContent = 'Copied'; setTimeout(() => $('#copy-mcp').textContent = 'Copy MCP setup', 1200); }); $('#workspace-files').addEventListener('change', event => { if (event.target.files.length) snapshotFiles([...event.target.files]); event.target.value = ''; }); $('#inspector-toggle').addEventListener('click', () => app.classList.toggle('inspector-closed'));
$('#focus-selection')?.addEventListener('click', focusSelection);
document.querySelectorAll('[data-toolbar-toggle]').forEach(button => button.addEventListener('click', () => {
  remember();
  if (button.dataset.toolbarToggle === 'trace') traceMode = !traceMode;
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
