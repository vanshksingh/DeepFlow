#!/usr/bin/env node
/** Local-only MCP bridge for DeepFlow's live viewer. */
import { createInterface } from 'node:readline';
import { stat } from 'node:fs/promises';
import { resolve, relative, sep } from 'node:path';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { createRepositoryGraph } from './src/repository-graph.js';

const run = promisify(execFile);
const send = message => process.stdout.write(`${JSON.stringify(message)}\n`);
const result = value => ({ content: [{ type: 'text', text: typeof value === 'string' ? value : JSON.stringify(value, null, 2) }] });
const schema = { type: 'object', properties: { root: { type: 'string', description: 'Absolute path to the local workspace.' }, viewerUrl: { type: 'string', description: 'Local DeepFlow viewer URL.', default: 'http://127.0.0.1:4317' } }, required: ['root'], additionalProperties: false };
const tools = [
  { name: 'deepflow_open_workspace', description: 'Connect a local workspace to the running DeepFlow viewer. The viewer starts a filesystem watcher, so subsequent agent edits update the graph and local diff indicators automatically.', inputSchema: schema },
  { name: 'deepflow_analyze_workspace', description: 'Build and return the semantic local repository graph, and connect the workspace to the live DeepFlow viewer.', inputSchema: schema },
  { name: 'deepflow_after_edit', description: 'Immediately notify DeepFlow after an agent edit. This is optional because the workspace watcher also detects changes, but it removes filesystem-event latency.', inputSchema: { ...schema, properties: { ...schema.properties, paths: { type: 'array', items: { type: 'string' }, description: 'Changed workspace-relative paths.' } } } },
  { name: 'deepflow_jump_to', description: 'Command the DeepFlow viewer to reveal and focus a folder, file, module, or exact source line.', inputSchema: { ...schema, properties: { ...schema.properties, path: { type: 'string', description: 'Workspace-relative folder or file path.' }, module: { type: 'string', description: 'Optional function/module name to reveal.' }, line: { type: 'number', description: 'Optional source line to focus.' }, pin: { type: 'boolean', description: 'Pin the revealed trace.' } }, required: ['root', 'path'] } },
  { name: 'deepflow_highlight_paths', description: 'Highlight several workspace-relative files/folders in the DeepFlow viewer.', inputSchema: { ...schema, properties: { ...schema.properties, paths: { type: 'array', items: { type: 'string' } }, pin: { type: 'boolean' } }, required: ['root', 'paths'] } },
  { name: 'deepflow_clear_highlights', description: 'Clear viewer pins/highlights without changing the workspace watcher.', inputSchema: schema },
  { name: 'deepflow_file_diff', description: 'Return the current local Git diff for a workspace file.', inputSchema: { type: 'object', properties: { root: { type: 'string' }, path: { type: 'string' } }, required: ['root', 'path'], additionalProperties: false } }
];

async function workspaceRoot(value) { const root = resolve(String(value || '')); if (!(await stat(root)).isDirectory()) throw new Error(`Not a readable local directory: ${root}`); return root; }
function safePath(root, value) { const target = resolve(root, String(value || '')); if (target !== root && !target.startsWith(root + sep)) throw new Error('Path must stay inside the requested workspace.'); return relative(root, target).replaceAll('\\', '/'); }
async function viewerRequest(url, path, body) {
  const response = await fetch(`${String(url || 'http://127.0.0.1:4317').replace(/\/$/, '')}${path}`, { method: 'POST', headers: { 'content-type': 'application/json' }, body: JSON.stringify(body) });
  if (!response.ok) throw new Error(`DeepFlow viewer is not available at ${url || 'http://127.0.0.1:4317'} (${response.status}). Start it with npm run dev.`);
  return response.json();
}
async function call(name, args) {
  const root = await workspaceRoot(args.root);
  if (name === 'deepflow_open_workspace') return viewerRequest(args.viewerUrl, '/api/track', { root });
  if (name === 'deepflow_analyze_workspace') { await viewerRequest(args.viewerUrl, '/api/track', { root }); return createRepositoryGraph({ roots: [root] }); }
  if (name === 'deepflow_after_edit') return viewerRequest(args.viewerUrl, '/api/mcp-change', { root, paths: args.paths || [] });
  if (name === 'deepflow_jump_to') return viewerRequest(args.viewerUrl, '/api/mcp-command', { type: 'jump', path: safePath(root, args.path), module: args.module, line: args.line, pin: !!args.pin });
  if (name === 'deepflow_highlight_paths') return viewerRequest(args.viewerUrl, '/api/mcp-command', { type: 'highlight-paths', paths: (args.paths || []).map(path => safePath(root, path)), pin: !!args.pin });
  if (name === 'deepflow_clear_highlights') return viewerRequest(args.viewerUrl, '/api/mcp-command', { type: 'clear-highlights' });
  if (name === 'deepflow_file_diff') {
    const path = safePath(root, args.path);
    try { const { stdout } = await run('git', ['-C', root, 'diff', '--no-ext-diff', '--unified=3', 'HEAD', '--', path], { timeout: 5000 }); return { root, path, diff: stdout || 'No uncommitted Git diff for this file.' }; }
    catch (error) { return { root, path, diff: error.stdout || 'No Git diff is available for this file.' }; }
  }
  throw new Error(`Unknown tool: ${name}`);
}

const input = createInterface({ input: process.stdin, crlfDelay: Infinity });
let requestQueue = Promise.resolve();
input.on('line', line => {
  requestQueue = requestQueue.then(() => handleRequest(line)).catch(error => send({ jsonrpc: '2.0', error: { code: -32000, message: error.message } }));
});
async function handleRequest(line) {
  let request;
  try {
    request = JSON.parse(line);
    if (request.method === 'initialize') return send({ jsonrpc: '2.0', id: request.id, result: { protocolVersion: request.params?.protocolVersion || '2024-11-05', capabilities: { tools: {} }, serverInfo: { name: 'deepflow-local', version: '0.2.0' } } });
    if (request.method === 'tools/list') return send({ jsonrpc: '2.0', id: request.id, result: { tools } });
    if (request.method === 'tools/call') return send({ jsonrpc: '2.0', id: request.id, result: result(await call(request.params.name, request.params.arguments || {})) });
    if (request.id !== undefined) return send({ jsonrpc: '2.0', id: request.id, error: { code: -32601, message: `Unsupported method: ${request.method}` } });
  } catch (error) { if (request?.id !== undefined) send({ jsonrpc: '2.0', id: request.id, error: { code: -32000, message: error.message } }); }
}
