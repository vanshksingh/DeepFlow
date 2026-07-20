/** Compact analytics over a DeepFlow repository graph (no source payloads). */

const FLOW = new Set(['calls', 'dataflow', 'events', 'inherits', 'imports', 'references', 'reexports']);

export function stripSources(graph) {
  return {
    ...graph,
    nodes: graph.nodes.map(node => {
      if (!node.meta?.source) return node;
      const { source, ...meta } = node.meta;
      return { ...node, meta };
    })
  };
}

export function summarizeGraph(graph) {
  const files = graph.nodes.filter(n => n.kind === 'file');
  const modules = graph.nodes.filter(n => n.kind === 'module');
  const flowEdges = graph.edges.filter(e => FLOW.has(e.type));
  const byType = {};
  for (const edge of flowEdges) byType[edge.type] = (byType[edge.type] || 0) + 1;
  const byLang = {};
  for (const file of files) byLang[file.language || 'asset'] = (byLang[file.language || 'asset'] || 0) + 1;
  const regions = {};
  for (const file of files.filter(f => f.language !== 'asset')) {
    const region = regionFor(file.path);
    regions[region] = (regions[region] || 0) + 1;
  }
  return {
    workspace: graph.roots?.[0]?.label || 'workspace',
    analyzer: graph.analyzer,
    stats: graph.stats,
    languages: byLang,
    rails: regions,
    edgeTypes: byType,
    entrypoints: entrypoints(graph).slice(0, 12),
    orphans: orphans(graph).slice(0, 12),
    diagnostics: (graph.diagnostics || []).slice(0, 20).map(d => ({
      severity: d.severity, path: d.path, line: d.line, message: d.message
    })),
    hotFiles: hotFiles(graph).slice(0, 10)
  };
}

export function regionFor(path = '') {
  const p = String(path).toLowerCase();
  if (/(^|\/)(apps?|gateway|console|web|frontend|backend)(\/|$)/.test(p)) return 'application';
  if (/(^|\/)(services?|workers?|server|tasks?)(\/|$)/.test(p)) return 'service';
  if (/(^|\/)(packages?|shared|common|lib|core|utils?)(\/|$)/.test(p)) return 'package';
  if (/(^|\/)(tests?|__tests__|specs?|fixtures)(\/|$)/.test(p)) return 'test';
  if (/(^|\/)(docs?|readme|examples?)(\/|$)/.test(p)) return 'docs';
  if (/(^|\/)(config|infra|scripts|assets|generated|vendor|docker|deploy|migrations?)(\/|$)/.test(p)) return 'infrastructure';
  return 'context';
}

export function entrypoints(graph) {
  return graph.nodes
    .filter(n => n.kind === 'file' && n.entrypoint)
    .map(n => ({ path: n.path, label: n.label, language: n.language, links: degree(graph, n.id) }))
    .sort((a, b) => b.links - a.links || a.path.localeCompare(b.path));
}

export function orphans(graph) {
  return graph.nodes
    .filter(n => n.orphan && (n.kind === 'file' || n.kind === 'module'))
    .map(n => ({
      kind: n.kind,
      path: n.path,
      label: n.label,
      reason: n.orphanReason || 'No static execution references were found.'
    }))
    .sort((a, b) => a.path.localeCompare(b.path));
}

export function findInGraph(graph, query, { limit = 24 } = {}) {
  const q = String(query || '').trim().toLowerCase();
  if (!q) return [];
  const scored = [];
  for (const node of graph.nodes) {
    if (node.kind !== 'file' && node.kind !== 'module' && node.kind !== 'folder') continue;
    const hay = `${node.path || ''} ${node.label || ''}`.toLowerCase();
    if (!hay.includes(q)) continue;
    let score = 0;
    if ((node.label || '').toLowerCase() === q) score += 100;
    if ((node.path || '').toLowerCase().endsWith(q)) score += 80;
    if ((node.label || '').toLowerCase().startsWith(q)) score += 40;
    if ((node.path || '').toLowerCase().includes(q)) score += 20;
    if (node.entrypoint) score += 10;
    if (node.orphan) score -= 5;
    scored.push({
      kind: node.kind,
      path: node.path,
      label: node.label,
      language: node.language,
      moduleKind: node.moduleKind,
      entrypoint: !!node.entrypoint,
      orphan: !!node.orphan,
      links: degree(graph, node.id),
      score
    });
  }
  return scored.sort((a, b) => b.score - a.score || a.path.localeCompare(b.path)).slice(0, limit);
}

export function impactOf(graph, path, { direction = 'both', depth = 3 } = {}) {
  const target = resolveNode(graph, path);
  if (!target) return { error: `No file/module found for path: ${path}` };
  const seeds = seedIds(graph, target);
  const upstream = walk(graph, seeds, 'in', depth);
  const downstream = walk(graph, seeds, 'out', depth);
  const pack = ids => [...ids]
    .map(id => graph.nodes.find(n => n.id === id))
    .filter(n => n && (n.kind === 'file' || n.kind === 'module'))
    .map(n => ({ kind: n.kind, path: n.path, label: n.label }))
    .filter((item, index, list) => list.findIndex(other => other.kind === item.kind && other.path === item.path && other.label === item.label) === index);
  return {
    target: { kind: target.kind, path: target.path, label: target.label },
    upstream: direction === 'out' ? [] : pack(upstream),
    downstream: direction === 'in' ? [] : pack(downstream),
    tip: 'Use deepflow_jump_to on the target path to show the signal path in the viewer.'
  };
}

export function pathBetween(graph, fromPath, toPath, { maxDepth = 8 } = {}) {
  const from = resolveNode(graph, fromPath);
  const to = resolveNode(graph, toPath);
  if (!from || !to) return { error: 'Both from and to paths must resolve to files or modules.', from: !!from, to: !!to };
  const start = seedIds(graph, from)[0];
  const goals = new Set(seedIds(graph, to));
  const queue = [{ id: start, path: [start], edges: [] }];
  const seen = new Set([start]);
  while (queue.length) {
    const current = queue.shift();
    if (current.path.length > maxDepth + 1) continue;
    if (goals.has(current.id) && current.path.length > 1) {
      return {
        found: true,
        hops: current.edges.length,
        nodes: current.path.map(id => describe(graph, id)),
        edges: current.edges.map(edge => ({ type: edge.type, evidence: edge.evidence, line: edge.line }))
      };
    }
    for (const edge of graph.edges.filter(e => FLOW.has(e.type) && e.from === current.id)) {
      if (seen.has(edge.to)) continue;
      seen.add(edge.to);
      queue.push({ id: edge.to, path: [...current.path, edge.to], edges: [...current.edges, edge] });
    }
  }
  return { found: false, message: `No directed path within ${maxDepth} hops from ${fromPath} to ${toPath}.` };
}

export function explainNode(graph, path) {
  const target = resolveNode(graph, path);
  if (!target) return { error: `Nothing found for: ${path}` };
  const related = graph.edges.filter(e => FLOW.has(e.type) && (e.from === target.id || e.to === target.id));
  const file = target.kind === 'module' ? graph.nodes.find(n => n.id === target.fileId) : target.kind === 'file' ? target : null;
  return {
    kind: target.kind,
    path: target.path,
    label: target.label,
    language: file?.language || target.language,
    region: regionFor(target.path),
    entrypoint: !!target.entrypoint,
    orphan: !!target.orphan,
    orphanReason: target.orphanReason || null,
    modules: target.kind === 'file'
      ? graph.nodes.filter(n => n.fileId === target.id).map(n => ({ label: n.label, line: n.loc?.start, exported: n.exported }))
      : undefined,
    relationships: related.slice(0, 24).map(edge => ({
      type: edge.type,
      direction: edge.from === target.id ? 'out' : 'in',
      evidence: edge.evidence,
      line: edge.line,
      other: describe(graph, edge.from === target.id ? edge.to : edge.from)
    })),
    git: file?.git?.change ? { change: file.git.change, hasDiff: !!file.git.diff } : null
  };
}

function degree(graph, nodeId) {
  return graph.edges.filter(e => FLOW.has(e.type) && (e.from === nodeId || e.to === nodeId)).length;
}

function resolveNode(graph, path) {
  const normalized = String(path || '').replaceAll('\\', '/').replace(/\/$/, '');
  if (!normalized) return null;
  if (normalized.includes('::') || normalized.includes('#')) {
    const [filePath, moduleName] = normalized.split(/::|#/);
    const file = graph.nodes.find(n => n.kind === 'file' && n.path === filePath);
    if (!file || !moduleName) return file || null;
    return graph.nodes.find(n => n.kind === 'module' && n.fileId === file.id && (n.label === moduleName || n.label.endsWith(`.${moduleName}`))) || file;
  }
  return graph.nodes.find(n => (n.kind === 'file' || n.kind === 'folder') && n.path === normalized)
    || graph.nodes.find(n => n.kind === 'module' && n.label === normalized)
    || graph.nodes.find(n => n.kind === 'file' && n.path.endsWith('/' + normalized));
}

function seedIds(graph, target) {
  if (target.kind === 'module') return [target.id];
  if (target.kind === 'file') {
    const modules = graph.nodes.filter(n => n.fileId === target.id).map(n => n.id);
    return [target.id, ...modules];
  }
  if (target.kind === 'folder') {
    const files = graph.nodes.filter(n => n.kind === 'file' && (n.path === target.path || n.path.startsWith(target.path + '/')));
    return files.flatMap(file => [file.id, ...graph.nodes.filter(n => n.fileId === file.id).map(n => n.id)]);
  }
  return [target.id];
}

function walk(graph, seeds, direction, maxDepth) {
  const found = new Set(seeds);
  const queue = seeds.map(id => ({ id, depth: 0 }));
  const seen = new Set(seeds.map(id => `${direction}:${id}`));
  while (queue.length) {
    const current = queue.shift();
    if (current.depth >= maxDepth) continue;
    for (const edge of graph.edges.filter(e => FLOW.has(e.type))) {
      const next = direction === 'out' && edge.from === current.id ? edge.to
        : direction === 'in' && edge.to === current.id ? edge.from : null;
      if (!next || found.has(next)) continue;
      found.add(next);
      const key = `${direction}:${next}`;
      if (!seen.has(key)) { seen.add(key); queue.push({ id: next, depth: current.depth + 1 }); }
    }
  }
  return found;
}

function describe(graph, id) {
  const node = graph.nodes.find(n => n.id === id);
  if (!node) return { id };
  return { kind: node.kind, path: node.path, label: node.label };
}

export function hotFiles(graph) {
  return graph.nodes
    .filter(n => n.kind === 'file' && n.language !== 'asset')
    .map(n => ({ path: n.path, label: n.label, language: n.language, links: degree(graph, n.id), entrypoint: !!n.entrypoint, orphan: !!n.orphan }))
    .sort((a, b) => b.links - a.links || a.path.localeCompare(b.path));
}

function snippetFor(graph, node, maxLines = 28) {
  const file = node.kind === 'module'
    ? graph.nodes.find(n => n.id === node.fileId)
    : node.kind === 'file' ? node : null;
  const source = file?.meta?.source;
  if (!source) return { path: node.path, label: node.label, code: '// Source unavailable in this response (stripped).', start: 1, end: 1 };
  const lines = source.split('\n');
  let start = 1, end = Math.min(lines.length, maxLines);
  if (node.kind === 'module' && node.loc) {
    start = node.loc.start;
    end = Math.min(lines.length, Math.max(start, node.loc.end || start));
    if (end - start > maxLines) end = start + maxLines - 1;
  }
  return {
    kind: node.kind,
    path: file.path,
    label: node.kind === 'module' ? `${node.label}()` : node.label,
    start,
    end,
    code: lines.slice(start - 1, end).join('\n')
  };
}

/** Agent-facing flow story: upstream inherits/callers, focus code, downstream consumers. */
export function explainFlow(graph, pathRef) {
  const target = resolveNode(graph, pathRef);
  if (!target) return { error: `Nothing found for: ${pathRef}` };
  const focus = target.kind === 'file'
    ? graph.nodes.find(n => n.fileId === target.id && n.kind === 'module') || target
    : target;
  const focusFile = focus.kind === 'module' ? graph.nodes.find(n => n.id === focus.fileId) : focus;
  const focusIds = new Set(seedIds(graph, focus));
  const upstream = [];
  const downstream = [];
  for (const edge of graph.edges.filter(e => FLOW.has(e.type))) {
    if (focusIds.has(edge.to) && !focusIds.has(edge.from)) {
      const other = graph.nodes.find(n => n.id === edge.from);
      if (other) upstream.push({ type: edge.type, evidence: edge.evidence, line: edge.line, other: describe(graph, other.id), snippet: snippetFor(graph, other) });
    }
    if (focusIds.has(edge.from) && !focusIds.has(edge.to)) {
      const other = graph.nodes.find(n => n.id === edge.to);
      if (other) downstream.push({ type: edge.type, evidence: edge.evidence, line: edge.line, other: describe(graph, other.id), snippet: snippetFor(graph, other) });
    }
  }
  const uniq = list => list.filter((item, index, arr) => arr.findIndex(x => x.other.path === item.other.path && x.other.label === item.other.label && x.type === item.type) === index).slice(0, 12);
  const up = uniq(upstream);
  const down = uniq(downstream);
  const narrative = [
    `${focus.kind === 'module' ? focus.label + '()' : focus.label} in ${focusFile?.path || focus.path}`,
    up.length ? `receives from ${up.length} upstream node(s): ${up.slice(0, 4).map(u => u.other.label).join(', ')}` : 'has no static upstream callers in this graph',
    down.length ? `emits to ${down.length} downstream node(s): ${down.slice(0, 4).map(d => d.other.label).join(', ')}` : 'has no static downstream consumers in this graph'
  ].join(' — ');
  return {
    path: focusFile?.path || focus.path,
    module: focus.kind === 'module' ? focus.label : null,
    narrative,
    focus: snippetFor(graph, focus, 40),
    upstream: up,
    downstream: down,
    tip: 'Open the viewer overlay with deepflow_open_flow to walk this story visually.'
  };
}

export const DEMO_TOUR_STEPS = [
  {
    title: 'Nested frames',
    narrative: 'DeepFlow opens like a Figma artboard: folders are frames that encapsulate files, which encapsulate functions.',
    command: { type: 'set-mode', mode: 'outline' }
  },
  {
    title: 'Gateway entry',
    narrative: 'Jump into the gateway ingest route and open startIngest(). The function frame owns the first signal.',
    command: { type: 'jump', path: 'apps/gateway/src/documentRoutes.ts', module: 'startIngest', pin: true }
  },
  {
    title: 'Ingest worker',
    narrative: 'Follow the trace into the ingest service. Wires land on the deepest open frame ports.',
    command: { type: 'jump', path: 'services/ingest/src/worker/contentGuard.ts', module: 'rejectOversized', pin: true }
  },
  {
    title: 'Shared package',
    narrative: 'Shared libraries sit inside the packages frame, reused across apps and services.',
    command: { type: 'jump', path: 'packages/shared/src/id.ts', module: 'createId' }
  },
  {
    title: 'Orphan detection',
    narrative: 'DeepFlow flags code with no static callers: dead weight or future hooks.',
    command: { type: 'show-orphans', pulse: true }
  },
  {
    title: 'Agent loop',
    narrative: 'When your agent edits a file, the outline refreshes live and the activity feed pulses. Call deepflow_after_edit after writes.',
    command: { type: 'highlight-paths', paths: ['services/ingest/src/worker/contentGuard.ts', 'apps/gateway/src/documentRoutes.ts'], pin: true }
  }
];

/**
 * Full capability showcase: slow enough to read, with spotlight + legend beats.
 * Best on fixtures/atlas-workspace.
 */
export const CAPABILITY_DEMO_STEPS = [
  {
    title: 'Welcome to the map',
    narrative: 'DeepFlow turns a messy monorepo into nested frames. Folders hold files; files hold functions. This tour walks every major capability.',
    dwellMs: 7000,
    legend: { kicker: '01 · Map', title: 'Architecture frames', body: 'Folders → files → functions as nested islands. Drag freely; neighbors yield on drop.' },
    command: { type: 'set-mode', mode: 'outline' }
  },
  {
    title: 'Relationship filters',
    narrative: 'Ribbon toggles pick which wires matter. Calls + Imports stay on, the two relationships people can read at a glance.',
    dwellMs: 6200,
    legend: { kicker: '02 · Edges', title: 'Filter the signal', body: 'Toggle Calls, Imports, Data, Events from the ribbon.' },
    command: { type: 'set-edges', edges: { calls: true, imports: true, dataflow: false, events: false, inherits: false } }
  },
  {
    title: 'Live hover traces',
    narrative: 'Live mode draws hover traces without changing selection. Skim the map and the wires follow your pointer.',
    dwellMs: 6200,
    legend: { kicker: '03 · Live', title: 'Hover to trace', body: 'Live toggle = pointer-driven wires.' },
    command: { type: 'set-live', enabled: true }
  },
  {
    title: 'Bubblegum mood',
    narrative: 'Themes are first-class. Each paints paper, ink, accents, and folder glass. Here is Bubblegum.',
    dwellMs: 5800,
    legend: { kicker: '04 · Theme', title: 'Bubblegum', body: 'Settings → Theme for light and dark packs.' },
    command: { type: 'set-theme', theme: 'bubblegum' }
  },
  {
    title: 'Tokyo Night',
    narrative: 'Dark themes work too. Tokyo Night for a moment, then we return to Aurora for clear contrast.',
    dwellMs: 5600,
    legend: { kicker: '04 · Theme', title: 'Tokyo Night', body: 'Accent swatches show Light vs Dark at a glance.' },
    command: { type: 'set-theme', theme: 'tokyo' }
  },
  {
    title: 'Back to Aurora',
    narrative: 'Return to Aurora (light) for the rest of the tour.',
    dwellMs: 5000,
    legend: { kicker: '04 · Theme', title: 'Aurora · Light', body: 'Default light canvas mood.' },
    command: { type: 'set-theme', theme: 'aurora' }
  },
  {
    title: 'Focus a service folder',
    narrative: 'Folders open under the pointer. Level-1 stays open; depth caps at two so the map stays readable.',
    dwellMs: 6800,
    legend: { kicker: '05 · Focus', title: 'services/ingest', body: 'Spotlight dims the rest of the map.' },
    spotlight: { path: 'services/ingest' },
    command: { type: 'focus-folder', path: 'services/ingest', expand: true, pulse: true }
  },
  {
    title: 'Jump into an entrypoint',
    narrative: 'Agents call deepflow_jump_to to pin a file and flash it. Gateway startIngest() is the front door.',
    dwellMs: 6800,
    legend: { kicker: '06 · Jump', title: 'startIngest()', body: 'Pin + pulse for the human watching.' },
    spotlight: { path: 'apps/gateway/src/documentRoutes.ts', module: 'startIngest' },
    command: { type: 'jump', path: 'apps/gateway/src/documentRoutes.ts', module: 'startIngest', pin: true, pulse: true }
  },
  {
    title: 'Code-flow overlay',
    narrative: 'Three columns: upstream → you are here → downstream. Scrollable snippets with syntax color and connect windows on the linked lines.',
    dwellMs: 9000,
    legend: { kicker: '07 · Flow', title: 'Inherit · call · emit', body: 'deepflow_explain_flow opens this overlay. Scroll sideways across columns.' },
    command: {
      type: 'open-flow',
      path: 'apps/gateway/src/documentRoutes.ts',
      module: 'startIngest',
      narrative: 'Gateway ingest is the front door. Callers arrive here, then work fans out into services.'
    }
  },
  {
    title: 'Follow the worker',
    narrative: 'Close the overlay and land deeper. Wires leave out-ports outward and enter in-ports from outside.',
    dwellMs: 5600,
    legend: { kicker: '08 · Trace path', title: 'Into the worker', body: 'Same graph, deeper frame.' },
    command: { type: 'close-flow' }
  },
  {
    title: 'Worker frame',
    narrative: 'rejectOversized() sits inside the ingest worker, a concrete module frame with ports for Live traces.',
    dwellMs: 6400,
    legend: { kicker: '08 · Module', title: 'rejectOversized()', body: 'Function chips live inside file tiles.' },
    spotlight: { path: 'services/ingest/src/worker/contentGuard.ts', module: 'rejectOversized' },
    command: { type: 'jump', path: 'services/ingest/src/worker/contentGuard.ts', module: 'rejectOversized', pin: true, pulse: true }
  },
  {
    title: 'Edit animation · Ripple',
    narrative: 'Agent edits can pulse, ripple, flash, scan, beacon, or spark. Pick one in Settings. Watch Ripple on this file.',
    dwellMs: 6400,
    legend: { kicker: '09 · Motion', title: 'Ripple edit', body: 'Configurable in Settings → Edit animation.' },
    command: { type: 'set-edit-anim', style: 'ripple', path: 'services/ingest/src/worker/contentGuard.ts' }
  },
  {
    title: 'Agent edit theater',
    narrative: 'When the agent writes code, DeepFlow opens the file, plays a side strip of running lines with diff line numbers, then folds the diff into the inspector.',
    dwellMs: 9200,
    legend: { kicker: '10 · Agent loop', title: 'after_edit', body: 'Theater strip → file focus → sidebar diff.' },
    spotlight: { path: 'services/ingest/src/worker/contentGuard.ts' },
    command: { type: 'simulate-edit', path: 'services/ingest/src/worker/contentGuard.ts', theater: true }
  },
  {
    title: 'Celebration particles',
    narrative: 'New or hot files can bloom. Soft hearts rise from the frame so the eye finds what just changed.',
    dwellMs: 5800,
    legend: { kicker: '11 · Bloom', title: 'Hearts', body: 'Particle accents on hot frames.' },
    command: { type: 'particle-burst', path: 'packages/shared/src/id.ts', kind: 'hearts' }
  },
  {
    title: 'Fire bloom',
    narrative: 'Or fire and sparks, for edits that feel hotter. Same API, different mood.',
    dwellMs: 5600,
    legend: { kicker: '11 · Bloom', title: 'Fire', body: 'kind: fire | hearts | sparks' },
    command: { type: 'particle-burst', path: 'apps/gateway/src/documentRoutes.ts', kind: 'fire' }
  },
  {
    title: 'Shared utilities',
    narrative: 'Cross-cutting packages are their own islands. createId() is reused across apps and services.',
    dwellMs: 6200,
    legend: { kicker: '12 · Packages', title: 'createId()', body: 'Shared code as a first-class island.' },
    spotlight: { path: 'packages/shared/src/id.ts', module: 'createId' },
    command: { type: 'jump', path: 'packages/shared/src/id.ts', module: 'createId', pin: true }
  },
  {
    title: 'Orphan hunt',
    narrative: 'deepflow_orphans pins files with no static callers: dead weight, stubs, or future hooks.',
    dwellMs: 7200,
    legend: { kicker: '13 · Orphans', title: 'No static callers', body: 'Amber dots in the edge legend.' },
    command: { type: 'show-orphans', pulse: true }
  },
  {
    title: 'Trace dialects',
    narrative: 'Wires can speak dialects. Unreviewed edges feel dashed and soft; removed edges fade. Live calls stay solid.',
    dwellMs: 6800,
    legend: { kicker: '14 · Dialects', title: 'Wire styles', body: 'Solid · dashed unreviewed · faded removed.' },
    command: { type: 'set-trace-dialects', enabled: true }
  },
  {
    title: 'Pin the change set',
    narrative: 'Highlight the files the agent just touched so the human sees the blast radius without a wall of text.',
    dwellMs: 6400,
    legend: { kicker: '15 · Pins', title: 'Change set', body: 'Multi-path pin from the agent.' },
    command: {
      type: 'highlight-paths',
      paths: ['services/ingest/src/worker/contentGuard.ts', 'apps/gateway/src/documentRoutes.ts', 'packages/shared/src/id.ts'],
      pin: true
    }
  },
  {
    title: 'New file pop-in',
    narrative: 'When a brand-new file appears on the map, it calms in with a soft pop, never a hard snap.',
    dwellMs: 5800,
    legend: { kicker: '16 · Birth', title: 'New file pop', body: 'calm-in + scale for arrivals.' },
    command: { type: 'pop-in', path: 'packages/shared/src/id.ts' }
  },
  {
    title: 'You are ready',
    narrative: 'That is the loop: open workspace → jump / explain_flow → edit → after_edit. Call deepflow_demo anytime for the full showcase.',
    dwellMs: 7200,
    legend: { kicker: 'Done', title: 'Agent-native map', body: 'deepflow_demo · autoPlay: true' },
    command: { type: 'clear-highlights' }
  }
];
