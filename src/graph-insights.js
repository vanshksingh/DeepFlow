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
    narrative: 'DeepFlow opens like a Figma artboard — folders are frames that encapsulate files, which encapsulate functions.',
    command: { type: 'set-mode', mode: 'outline' }
  },
  {
    title: 'Gateway entry',
    narrative: 'Jump into the gateway ingest route and open startIngest() — the function frame owns the first signal.',
    command: { type: 'jump', path: 'apps/gateway/src/documentRoutes.ts', module: 'startIngest', pin: true }
  },
  {
    title: 'Ingest worker',
    narrative: 'Follow the trace into the ingest service. Wires land on the deepest open frame ports.',
    command: { type: 'jump', path: 'services/ingest/src/worker/contentGuard.ts', module: 'rejectOversized', pin: true }
  },
  {
    title: 'Shared package',
    narrative: 'Shared libraries sit inside the packages frame — reused across apps and services.',
    command: { type: 'jump', path: 'packages/shared/src/id.ts', module: 'createId' }
  },
  {
    title: 'Orphan detection',
    narrative: 'DeepFlow flags code with no static callers — dead weight or future hooks.',
    command: { type: 'show-orphans', pulse: true }
  },
  {
    title: 'Agent loop',
    narrative: 'When your agent edits a file, the outline refreshes live and the activity feed pulses. Call deepflow_after_edit after writes.',
    command: { type: 'highlight-paths', paths: ['services/ingest/src/worker/contentGuard.ts', 'apps/gateway/src/documentRoutes.ts'], pin: true }
  }
];
