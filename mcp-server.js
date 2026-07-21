#!/usr/bin/env node
/** Local-only MCP bridge for DeepFlow, agent-native architecture map. */
import { createInterface } from 'node:readline';
import { stat } from 'node:fs/promises';
import { existsSync, realpathSync } from 'node:fs';
import { resolve, relative, sep, dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { createRepositoryGraph } from './src/repository-graph.js';
import {
  summarizeGraph, stripSources, findInGraph, impactOf, pathBetween,
  explainNode, orphans, entrypoints, DEMO_TOUR_STEPS, CAPABILITY_DEMO_STEPS, explainFlow
} from './src/graph-insights.js';

const run = promisify(execFile);
const HERE = dirname(fileURLToPath(import.meta.url));
const DEFAULT_VIEWER = 'http://127.0.0.1:4317';
const send = message => process.stdout.write(`${JSON.stringify(message)}\n`);
const result = value => ({ content: [{ type: 'text', text: typeof value === 'string' ? value : JSON.stringify(value, null, 2) }] });

const rootProp = { type: 'string', description: 'Absolute path to the local workspace.' };
const viewerProp = { type: 'string', description: 'Local DeepFlow viewer URL.', default: DEFAULT_VIEWER };
const withRoot = (properties = {}, required = ['root']) => ({
  type: 'object',
  properties: { root: rootProp, viewerUrl: viewerProp, ...properties },
  required,
  additionalProperties: false
});

const tools = [
  {
    name: 'deepflow_status',
    description: 'Health-check the DeepFlow viewer and report tracked workspace, client count, and setup hints. Call this first if unsure whether the map is running.',
    inputSchema: { type: 'object', properties: { viewerUrl: viewerProp }, additionalProperties: false }
  },
  {
    name: 'deepflow_open_workspace',
    description: 'Connect a local workspace to the running DeepFlow viewer and start the filesystem watcher. Always call this before editing so the map stays live.',
    inputSchema: withRoot()
  },
  {
    name: 'deepflow_analyze_workspace',
    description: 'Build the semantic repository graph (JS/TS/Python via Tree-sitter), connect the viewer, and return a source-stripped graph JSON plus a compact summary.',
    inputSchema: withRoot({ includeSource: { type: 'boolean', description: 'Include full file sources (large). Default false.' } })
  },
  {
    name: 'deepflow_summary',
    description: 'Return a compact architecture briefing: rails, languages, entrypoints, orphans, hot files, diagnostics. Prefer this over full analyze for agent planning.',
    inputSchema: withRoot()
  },
  {
    name: 'deepflow_find',
    description: 'Search files, folders, and modules by path or name substring.',
    inputSchema: withRoot({ query: { type: 'string' }, limit: { type: 'number' } }, ['root', 'query'])
  },
  {
    name: 'deepflow_explain',
    description: 'Explain one file/module: region, orphan status, modules, and typed relationships with evidence lines.',
    inputSchema: withRoot({ path: { type: 'string', description: 'Workspace-relative path, optionally file.py::function' } }, ['root', 'path'])
  },
  {
    name: 'deepflow_impact',
    description: 'Show upstream callers and downstream consumers for a path (static impact radius).',
    inputSchema: withRoot({
      path: { type: 'string' },
      direction: { type: 'string', enum: ['in', 'out', 'both'], default: 'both' },
      depth: { type: 'number', default: 3 }
    }, ['root', 'path'])
  },
  {
    name: 'deepflow_path_between',
    description: 'Find a directed relationship path between two files/modules for storytelling or reviews.',
    inputSchema: withRoot({ from: { type: 'string' }, to: { type: 'string' }, maxDepth: { type: 'number', default: 8 } }, ['root', 'from', 'to'])
  },
  {
    name: 'deepflow_entrypoints',
    description: 'List detected entrypoint files (main/app/server/manage/asgi/wsgi/route/worker, etc.).',
    inputSchema: withRoot()
  },
  {
    name: 'deepflow_orphans',
    description: 'List files/modules with no static execution references, useful for cleanup demos.',
    inputSchema: withRoot({ showInViewer: { type: 'boolean', description: 'Also highlight orphans in the viewer.', default: true } })
  },
  {
    name: 'deepflow_diagnostics',
    description: 'Return parse/import diagnostics (unresolved imports, syntax errors, TODO markers).',
    inputSchema: withRoot({ severity: { type: 'string', enum: ['error', 'warning', 'notice', 'all'], default: 'all' } })
  },
  {
    name: 'deepflow_after_edit',
    description: 'Immediately refresh the viewer after an agent write. Optional but removes FS-event latency. Pass changed relative paths when known.',
    inputSchema: withRoot({ paths: { type: 'array', items: { type: 'string' } } })
  },
  {
    name: 'deepflow_jump_to',
    description: 'Command the viewer to reveal and focus a folder, file, module, or source line (enters signal-path mode).',
    inputSchema: withRoot({
      path: { type: 'string' },
      module: { type: 'string' },
      line: { type: 'number' },
      pin: { type: 'boolean' },
      pulse: { type: 'boolean', description: 'Flash the focused card for demos.', default: true }
    }, ['root', 'path'])
  },
  {
    name: 'deepflow_highlight_paths',
    description: 'Highlight several workspace-relative files/folders in the viewer.',
    inputSchema: withRoot({ paths: { type: 'array', items: { type: 'string' } }, pin: { type: 'boolean' } }, ['root', 'paths'])
  },
  {
    name: 'deepflow_clear_highlights',
    description: 'Clear pins/highlights and return the viewer to architecture rails.',
    inputSchema: withRoot()
  },
  {
    name: 'deepflow_set_mode',
    description: 'Force viewer layout mode: rails (architecture overview) or signal (calls-in → focus → calls-out).',
    inputSchema: withRoot({ mode: { type: 'string', enum: ['rails', 'signal', 'outline'], description: 'outline is an alias of rails' } }, ['root', 'mode'])
  },
  {
    name: 'deepflow_set_edges',
    description: 'Toggle which relationship types are drawn (calls, imports, dataflow, events, inherits, references, reexports).',
    inputSchema: withRoot({
      edges: {
        type: 'object',
        description: 'Map of edge type → boolean visibility.',
        additionalProperties: { type: 'boolean' }
      }
    }, ['root', 'edges'])
  },
  {
    name: 'deepflow_tour',
    description: 'Run the short Atlas walkthrough in the viewer. Prefer deepflow_demo for the full capability showcase.',
    inputSchema: withRoot({
      step: { type: 'number', description: '0-based step index. Omit to run/list all steps metadata.' },
      autoPlay: { type: 'boolean', description: 'When true and step omitted, play the full tour in the viewer.', default: false }
    })
  },
  {
    name: 'deepflow_demo',
    description: 'Run the full capability showcase in the viewer: nested frames, edge filters, Live traces, folder focus, jump/pin, code-flow overlay, orphans, and agent-edit reveal. Best on fixtures/atlas-workspace. Use autoPlay: true for demos/judges.',
    inputSchema: withRoot({
      step: { type: 'number', description: '0-based step index. Omit with autoPlay to run the full demo, or omit both to list steps.' },
      autoPlay: { type: 'boolean', description: 'Play the entire capability demo in the viewer.', default: true },
      paceMs: { type: 'number', description: 'Optional global dwell override (ms) between steps. Default uses each step’s dwellMs.' }
    })
  },
  {
    name: 'deepflow_open_flow',
    description: 'Open the DeepFlow code-flow overlay for a file/module: scrollable upstream (inherits/callers) ← focus source → downstream (calls/emits). Best way for an agent to narrate how code works.',
    inputSchema: withRoot({
      path: { type: 'string', description: 'Workspace-relative file path, optionally file.ts::moduleName' },
      module: { type: 'string', description: 'Optional function/module name if not using :: in path' },
      narrative: { type: 'string', description: 'Optional agent-written explanation shown above the flow.' }
    }, ['root', 'path'])
  },
  {
    name: 'deepflow_explain_flow',
    description: 'Return a structured flow story (narrative + upstream/downstream snippets) and open the same overlay in the viewer so the human can follow along.',
    inputSchema: withRoot({
      path: { type: 'string' },
      module: { type: 'string' },
      openOverlay: { type: 'boolean', default: true }
    }, ['root', 'path'])
  },
  {
    name: 'deepflow_close_flow',
    description: 'Close the code-flow overlay in the viewer.',
    inputSchema: withRoot()
  },
  {
    name: 'deepflow_share_link',
    description: 'Return a shareable viewer deep-link hash for the current focus (path/module/mode).',
    inputSchema: withRoot({ path: { type: 'string' }, module: { type: 'string' }, mode: { type: 'string', enum: ['rails', 'signal'] } }, ['root', 'path'])
  },
  {
    name: 'deepflow_file_diff',
    description: 'Return the current local Git diff for a workspace file.',
    inputSchema: { type: 'object', properties: { root: rootProp, path: { type: 'string' } }, required: ['root', 'path'], additionalProperties: false }
  },
  {
    name: 'deepflow_pr_diff',
    description: 'Return a unified Git diff for a branch/PR range (base...head). Defaults base to main/master and head to HEAD. Optional paths filter.',
    inputSchema: {
      type: 'object',
      properties: {
        root: rootProp,
        base: { type: 'string', description: 'Base ref (default: main, then master).' },
        head: { type: 'string', description: 'Head ref (default: HEAD).' },
        paths: { type: 'array', items: { type: 'string' }, description: 'Optional path filters.' },
        maxChars: { type: 'number', description: 'Truncate diff after this many characters (default 24000).' }
      },
      required: ['root'],
      additionalProperties: false
    }
  },
  {
    name: 'deepflow_setup_help',
    description: 'Return copy-paste setup instructions for installing DeepFlow, starting the viewer, and wiring this MCP server into an agent IDE.',
    inputSchema: { type: 'object', properties: {}, additionalProperties: false }
  }
];

async function workspaceRoot(value) {
  const root = resolve(String(value || ''));
  if (!(await stat(root)).isDirectory()) throw new Error(`Not a readable local directory: ${root}`);
  return root;
}
function insideRoot(root, target) {
  return target === root || target.startsWith(root + sep);
}
function safePath(root, value) {
  const target = resolve(root, String(value || ''));
  if (!insideRoot(root, target)) throw new Error('Path must stay inside the requested workspace.');
  let realRoot = root;
  try { realRoot = realpathSync(root); } catch {}
  let realTarget = target;
  try {
    if (existsSync(target)) realTarget = realpathSync(target);
    else if (existsSync(dirname(target))) realTarget = join(realpathSync(dirname(target)), relative(dirname(target), target));
  } catch {
    realTarget = target;
  }
  if (!insideRoot(realRoot, resolve(realTarget))) throw new Error('Path must stay inside the requested workspace.');
  return relative(root, target).replaceAll('\\', '/');
}
/** Allow `path/to/file.ts::moduleName` while still sandboxing the file portion. */
function safePathRef(root, value) {
  const raw = String(value || '');
  const split = raw.search(/::|#/);
  if (split === -1) return safePath(root, raw);
  return `${safePath(root, raw.slice(0, split))}${raw.slice(split)}`;
}
function assertLoopbackViewer(url) {
  const base = String(url || DEFAULT_VIEWER);
  let parsed;
  try { parsed = new URL(base); } catch { throw new Error(`Invalid viewerUrl: ${base}`); }
  const host = parsed.hostname;
  if (!['127.0.0.1', 'localhost', '::1'].includes(host)) {
    throw new Error(`viewerUrl must target loopback (127.0.0.1/localhost); got ${host}`);
  }
  return base.replace(/\/$/, '');
}
async function viewerRequest(url, path, body, method = 'POST') {
  const base = assertLoopbackViewer(url);
  const response = await fetch(`${base}${path}`, {
    method,
    headers: method === 'GET' ? undefined : { 'content-type': 'application/json' },
    body: method === 'GET' ? undefined : JSON.stringify(body || {})
  });
  if (!response.ok) throw new Error(`DeepFlow viewer is not available at ${base} (${response.status}). Start it with: npm run dev`);
  return response.json();
}
async function graphFor(root) {
  return createRepositoryGraph({ roots: [root] });
}
async function viewerTry(viewer, path, body, method = 'POST') {
  try {
    return { ok: true, ...(await viewerRequest(viewer, path, body, method)) };
  } catch (error) {
    return { ok: false, error: error.message };
  }
}


async function call(name, args = {}) {
  if (name === 'deepflow_setup_help') {
    return {
      title: 'DeepFlow agent setup',
      steps: [
        '1. cd into the DeepFlow checkout',
        '2. npm install',
        '3. npm run dev   # leaves http://127.0.0.1:4317 running',
        '4. Add MCP config pointing at this mcp-server.js (absolute path)',
        '5. Call deepflow_open_workspace with the absolute path of the repo to map',
        '6. After edits: deepflow_after_edit; to narrate: deepflow_jump_to / deepflow_explain_flow / deepflow_demo',
        '7. For judges: deepflow_open_workspace on fixtures/atlas-workspace, then deepflow_demo with autoPlay: true'
      ],
      mcpConfig: {
        mcpServers: {
          deepflow: {
            command: 'node',
            args: [resolve(HERE, 'mcp-server.js')]
          }
        }
      },
      demoWorkspace: resolve(HERE, 'fixtures/atlas-workspace'),
      pythonDemo: resolve(HERE, 'fixtures/python-mini'),
      docs: ['README.md', 'AGENTS.md']
    };
  }

  if (name === 'deepflow_status') {
    try {
      const status = await viewerRequest(args.viewerUrl, '/api/status', null, 'GET');
      return { ok: true, viewer: String(args.viewerUrl || DEFAULT_VIEWER), ...status };
    } catch (error) {
      return {
        ok: false,
        viewer: String(args.viewerUrl || DEFAULT_VIEWER),
        error: error.message,
        fix: 'From the DeepFlow checkout run: npm install && npm run dev'
      };
    }
  }

  const root = await workspaceRoot(args.root);
  const viewer = args.viewerUrl || DEFAULT_VIEWER;

  if (name === 'deepflow_open_workspace') return viewerRequest(viewer, '/api/track', { root });

  if (name === 'deepflow_analyze_workspace') {
    await viewerRequest(viewer, '/api/track', { root });
    const graph = await graphFor(root);
    return {
      summary: summarizeGraph(graph),
      graph: args.includeSource ? graph : stripSources(graph)
    };
  }

  if (name === 'deepflow_summary') {
    const track = await viewerTry(viewer, '/api/track', { root });
    return { ...summarizeGraph(await graphFor(root)), viewer: track.ok ? { ok: true } : { ok: false, error: track.error } };
  }

  if (name === 'deepflow_find') return { query: args.query, matches: findInGraph(await graphFor(root), args.query, { limit: args.limit || 24 }) };
  if (name === 'deepflow_explain') return explainNode(await graphFor(root), safePathRef(root, args.path));
  if (name === 'deepflow_impact') return impactOf(await graphFor(root), safePathRef(root, args.path), { direction: args.direction || 'both', depth: args.depth || 3 });
  if (name === 'deepflow_path_between') {
    return pathBetween(await graphFor(root), safePathRef(root, args.from), safePathRef(root, args.to), { maxDepth: args.maxDepth || 8 });
  }
  if (name === 'deepflow_entrypoints') return { entrypoints: entrypoints(await graphFor(root)) };
  if (name === 'deepflow_orphans') {
    const list = orphans(await graphFor(root));
    let viewerStatus = { ok: true };
    if (args.showInViewer !== false) {
      const track = await viewerTry(viewer, '/api/track', { root });
      if (!track.ok) viewerStatus = { ok: false, error: track.error };
      else {
        const shown = await viewerTry(viewer, '/api/mcp-command', { type: 'show-orphans', pulse: true, paths: list.filter(i => i.kind === 'file').map(i => i.path).slice(0, 40) });
        if (!shown.ok) viewerStatus = { ok: false, error: shown.error };
      }
    }
    return { count: list.length, orphans: list, viewer: viewerStatus };
  }
  if (name === 'deepflow_diagnostics') {
    const graph = await graphFor(root);
    const severity = args.severity || 'all';
    const items = (graph.diagnostics || []).filter(d => severity === 'all' || d.severity === severity);
    return { count: items.length, diagnostics: items.slice(0, 80) };
  }
  if (name === 'deepflow_after_edit') return viewerRequest(viewer, '/api/mcp-change', { root, paths: (args.paths || []).map(p => safePath(root, p)) });
  if (name === 'deepflow_jump_to') {
    await viewerRequest(viewer, '/api/track', { root });
    const ref = safePathRef(root, args.path);
    const split = ref.search(/::|#/);
    const path = split === -1 ? ref : ref.slice(0, split);
    const moduleFromRef = split === -1 ? null : ref.slice(split + (ref[split] === '#' ? 1 : 2));
    return viewerRequest(viewer, '/api/mcp-command', {
      type: 'jump',
      path,
      module: args.module || moduleFromRef || undefined,
      line: args.line,
      pin: !!args.pin,
      pulse: args.pulse !== false
    });
  }
  if (name === 'deepflow_highlight_paths') {
    await viewerRequest(viewer, '/api/track', { root });
    return viewerRequest(viewer, '/api/mcp-command', {
      type: 'highlight-paths',
      paths: (args.paths || []).map(path => safePath(root, path)),
      pin: !!args.pin
    });
  }
  if (name === 'deepflow_clear_highlights') return viewerRequest(viewer, '/api/mcp-command', { type: 'clear-highlights' });
  if (name === 'deepflow_set_mode') return viewerRequest(viewer, '/api/mcp-command', { type: 'set-mode', mode: args.mode });
  if (name === 'deepflow_set_edges') return viewerRequest(viewer, '/api/mcp-command', { type: 'set-edges', edges: args.edges || {} });
  if (name === 'deepflow_tour') {
    await viewerRequest(viewer, '/api/track', { root });
    if (typeof args.step === 'number') {
      const step = DEMO_TOUR_STEPS[args.step];
      if (!step) throw new Error(`Tour step ${args.step} out of range (0-${DEMO_TOUR_STEPS.length - 1}).`);
      await viewerRequest(viewer, '/api/mcp-command', { type: 'tour-step', index: args.step, ...step });
      return { step: args.step, ...step, delivered: true };
    }
    if (args.autoPlay) {
      return viewerRequest(viewer, '/api/mcp-command', { type: 'tour-play', steps: DEMO_TOUR_STEPS });
    }
    return { steps: DEMO_TOUR_STEPS.map((step, index) => ({ index, title: step.title, narrative: step.narrative })), tip: 'Call again with step: N or autoPlay: true, or use deepflow_demo for the full showcase.' };
  }
  if (name === 'deepflow_demo') {
    await viewerRequest(viewer, '/api/track', { root });
    const steps = CAPABILITY_DEMO_STEPS;
    if (typeof args.step === 'number') {
      const step = steps[args.step];
      if (!step) throw new Error(`Demo step ${args.step} out of range (0-${steps.length - 1}).`);
      await viewerRequest(viewer, '/api/mcp-command', { type: 'tour-step', index: args.step, ...step });
      return { demo: 'capabilities', step: args.step, title: step.title, narrative: step.narrative, delivered: true };
    }
    if (args.autoPlay !== false) {
      const paced = typeof args.paceMs === 'number'
        ? steps.map(step => ({ ...step, dwellMs: args.paceMs }))
        : steps;
      await viewerRequest(viewer, '/api/mcp-command', { type: 'tour-play', steps: paced, demo: 'capabilities' });
      return {
        ok: true,
        demo: 'capabilities',
        playing: true,
        steps: paced.length,
        titles: paced.map(s => s.title),
        tip: 'Watch the viewer. The capability demo is narrating live.'
      };
    }
    return {
      demo: 'capabilities',
      steps: steps.map((step, index) => ({ index, title: step.title, narrative: step.narrative, dwellMs: step.dwellMs || 2800 })),
      tip: 'Call again with autoPlay: true (default) or step: N',
      recommendedRoot: 'fixtures/atlas-workspace'
    };
  }
  if (name === 'deepflow_open_flow') {
    await viewerRequest(viewer, '/api/track', { root });
    const ref = args.module ? `${safePath(root, args.path)}::${args.module}` : safePathRef(root, args.path);
    const story = explainFlow(await graphFor(root), ref);
    return viewerRequest(viewer, '/api/mcp-command', {
      type: 'open-flow',
      path: story.path || safePath(root, String(args.path).split(/::|#/)[0]),
      module: args.module || story.module,
      narrative: args.narrative || story.narrative,
      story
    });
  }
  if (name === 'deepflow_explain_flow') {
    const ref = args.module ? `${safePath(root, args.path)}::${args.module}` : safePathRef(root, args.path);
    const story = explainFlow(await graphFor(root), ref);
    let viewerStatus = { ok: true };
    if (args.openOverlay !== false) {
      const track = await viewerTry(viewer, '/api/track', { root });
      if (!track.ok) viewerStatus = { ok: false, error: track.error };
      else {
        const opened = await viewerTry(viewer, '/api/mcp-command', {
          type: 'open-flow',
          path: story.path,
          module: story.module,
          narrative: story.narrative,
          story
        });
        if (!opened.ok) viewerStatus = { ok: false, error: opened.error };
      }
    }
    return { ...story, viewer: viewerStatus };
  }
  if (name === 'deepflow_close_flow') return viewerRequest(viewer, '/api/mcp-command', { type: 'close-flow' });
  if (name === 'deepflow_share_link') {
    const path = safePath(root, args.path);
    const params = new URLSearchParams();
    params.set('path', path);
    if (args.module) params.set('module', args.module);
    if (args.mode) params.set('mode', args.mode);
    const hash = `#${params.toString()}`;
    return { url: `${String(viewer).replace(/\/$/, '')}${hash}`, hash, path, module: args.module || null, mode: args.mode || 'signal' };
  }
  if (name === 'deepflow_file_diff') {
    const path = safePath(root, args.path);
    try {
      const { stdout: statusOut } = await run('git', ['-C', root, 'status', '--porcelain', '--', path], { timeout: 5000 });
      const status = String(statusOut || '').trim();
      const untracked = status.startsWith('??') || status.startsWith('A ');
      let stdout = '';
      if (untracked) {
        const abs = join(root, path);
        const result = await run('git', ['-C', root, 'diff', '--no-ext-diff', '--unified=3', '--no-index', '--', '/dev/null', abs], { timeout: 5000 }).catch(error => error);
        stdout = result.stdout || '';
        if (!stdout && result.stderr) {
          return { root, path, error: result.stderr || result.message || 'Git diff failed', diff: null };
        }
      } else {
        const result = await run('git', ['-C', root, 'diff', '--no-ext-diff', '--unified=3', 'HEAD', '--', path], { timeout: 5000 });
        stdout = result.stdout || '';
      }
      return { root, path, untracked: !!untracked, diff: stdout || 'No uncommitted Git diff for this file.' };
    } catch (error) {
      return { root, path, error: error.stderr || error.message || 'Git diff failed', diff: null };
    }
  }
  if (name === 'deepflow_pr_diff') {
    const head = String(args.head || 'HEAD');
    let base = args.base ? String(args.base) : '';
    if (!base) {
      for (const candidate of ['main', 'master', 'origin/main', 'origin/master']) {
        try {
          await run('git', ['-C', root, 'rev-parse', '--verify', candidate], { timeout: 3000 });
          base = candidate;
          break;
        } catch {}
      }
      if (!base) {
        try {
          const { stdout } = await run('git', ['-C', root, 'symbolic-ref', 'refs/remotes/origin/HEAD'], { timeout: 3000 });
          const ref = String(stdout || '').trim().replace(/^refs\/remotes\//, '');
          if (ref) {
            await run('git', ['-C', root, 'rev-parse', '--verify', ref], { timeout: 3000 });
            base = ref;
          }
        } catch {}
      }
      if (!base) {
        return { root, head, error: 'No base ref found; pass base explicitly (e.g. main or origin/main).', diff: null };
      }
    }
    const pathArgs = [];
    if (Array.isArray(args.paths) && args.paths.length) {
      pathArgs.push('--');
      for (const p of args.paths) pathArgs.push(safePath(root, p));
    }
    const maxChars = Math.max(4000, Math.min(120000, Number(args.maxChars) || 24000));
    try {
      await run('git', ['-C', root, 'rev-parse', '--verify', base], { timeout: 3000 });
      await run('git', ['-C', root, 'rev-parse', '--verify', head], { timeout: 3000 });
      const { stdout } = await run(
        'git',
        ['-C', root, 'diff', '--no-ext-diff', '--unified=3', `${base}...${head}`, ...pathArgs],
        { timeout: 12000 }
      );
      const raw = stdout || '';
      const truncated = raw.length > maxChars;
      return {
        root, base, head, truncated,
        diff: truncated ? `${raw.slice(0, maxChars)}\n\n… truncated (${raw.length} chars total)` : (raw || 'No diff for this range.')
      };
    } catch (error) {
      return { root, base, head, truncated: false, error: error.stderr || error.message || 'Git PR/branch diff failed', diff: null };
    }
  }
  throw new Error(`Unknown tool: ${name}`);
}

const input = createInterface({ input: process.stdin, crlfDelay: Infinity });
let requestQueue = Promise.resolve();
input.on('line', line => {
  let peekedId;
  try { peekedId = JSON.parse(line)?.id; } catch { peekedId = undefined; }
  requestQueue = requestQueue.then(() => handleRequest(line)).catch(error => {
    if (peekedId !== undefined) send({ jsonrpc: '2.0', id: peekedId, error: { code: -32000, message: error.message } });
  });
});
async function handleRequest(line) {
  let request;
  try {
    request = JSON.parse(line);
    if (request.method === 'initialize') {
      return send({
        jsonrpc: '2.0',
        id: request.id,
        result: {
          protocolVersion: request.params?.protocolVersion || '2024-11-05',
          capabilities: { tools: {} },
          serverInfo: { name: 'deepflow-local', version: '0.3.0' }
        }
      });
    }
    if (request.method === 'notifications/initialized') return;
    if (request.method === 'tools/list') return send({ jsonrpc: '2.0', id: request.id, result: { tools } });
    if (request.method === 'tools/call') return send({ jsonrpc: '2.0', id: request.id, result: result(await call(request.params.name, request.params.arguments || {})) });
    if (request.method === 'ping') return send({ jsonrpc: '2.0', id: request.id, result: {} });
    if (request.id !== undefined) return send({ jsonrpc: '2.0', id: request.id, error: { code: -32601, message: `Unsupported method: ${request.method}` } });
  } catch (error) {
    let id = request?.id;
    if (id === undefined) {
      try { id = JSON.parse(line)?.id; } catch { id = undefined; }
    }
    if (id !== undefined) send({ jsonrpc: '2.0', id, error: { code: -32000, message: error.message } });
  }
}
