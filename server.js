import { createServer } from 'node:http';
import { readFile, readdir, stat, mkdtemp, mkdir, writeFile, rm } from 'node:fs/promises';
import { watch as watchFilesystem } from 'node:fs';
import { extname, join, dirname, resolve, relative } from 'node:path';
import { tmpdir } from 'node:os';
import { createRepositoryGraph } from './src/repository-graph.js';

const appRoot = new URL('.', import.meta.url).pathname;
const fixtureRoot = join(appRoot, 'fixtures', 'atlas-workspace');
const contentTypes = { '.html': 'text/html; charset=utf-8', '.css': 'text/css; charset=utf-8', '.js': 'application/javascript; charset=utf-8' };
const clients = new Set();
let trackedRoot = fixtureRoot;
let workspaceWatchers = [];
let changeTimer;
const pendingChangePaths = new Set();

function sendJson(res, value, status = 200) { res.writeHead(status, { 'content-type': 'application/json; charset=utf-8' }); res.end(JSON.stringify(value)); }
function readJson(req) { return new Promise((resolveJson, reject) => { let body = ''; req.on('data', chunk => body += chunk); req.on('end', () => { try { resolveJson(body ? JSON.parse(body) : {}); } catch (error) { reject(error); } }); }); }
function publishChange(paths = []) {
  for (const path of paths) if (path) pendingChangePaths.add(String(path).replaceAll('\\', '/'));
  clearTimeout(changeTimer);
  changeTimer = setTimeout(() => {
    const payload = JSON.stringify({ root: trackedRoot, paths: [...pendingChangePaths].slice(0, 50), at: Date.now() });
    pendingChangePaths.clear();
    for (const client of clients) client.write(`event: workspace-change\ndata: ${payload}\n\n`);
  }, 150);
}
function publishViewerCommand(command = {}) {
  const payload = JSON.stringify({ ...command, at: Date.now() });
  for (const client of clients) client.write(`event: viewer-command\ndata: ${payload}\n\n`);
}
async function localDirectory(value) {
  const directory = resolve(String(value || ''));
  if (!(await stat(directory)).isDirectory()) throw new Error(`Not a readable local directory: ${directory}`);
  return directory;
}
async function walkDirectories(directory) {
  const entries = await readdir(directory, { withFileTypes: true });
  const directories = [];
  for (const entry of entries) {
    if (!entry.isDirectory() || entry.name === '.git' || entry.name === 'node_modules') continue;
    const child = join(directory, entry.name);
    directories.push(child, ...await walkDirectories(child));
  }
  return directories;
}
async function startTracking(value) {
  const root = await localDirectory(value);
  if (trackedRoot === root && workspaceWatchers.length) return root;
  workspaceWatchers.forEach(watcher => watcher.close()); workspaceWatchers = []; trackedRoot = root;
  const directories = await walkDirectories(root);
  for (const directory of [root, ...directories]) {
    try {
      workspaceWatchers.push(watchFilesystem(directory, (_event, filename) => {
        const changed = filename ? relative(root, join(directory, filename.toString())) : '';
        if (!changed.includes('.git')) publishChange(changed ? [changed] : []);
      }));
    } catch {}
  }
  publishChange([]); return root;
}
async function graphFor(root) { return createRepositoryGraph({ roots: [root] }); }
function safeRelative(value) { const path = String(value || '').replaceAll('\\', '/').replace(/^\/+/, ''); return path && !path.split('/').includes('..') ? path : null; }

await startTracking(fixtureRoot);
createServer(async (req, res) => {
  try {
    if (req.url === '/api/changes' && req.method === 'GET') {
      res.writeHead(200, { 'content-type': 'text/event-stream', 'cache-control': 'no-cache', connection: 'keep-alive' });
      res.write(`event: ready\ndata: ${JSON.stringify({ root: trackedRoot })}\n\n`); clients.add(res); req.on('close', () => clients.delete(res)); return;
    }
    if (req.url === '/api/graph' && req.method === 'POST') {
      const payload = await readJson(req); const root = await localDirectory(payload.root || trackedRoot); return sendJson(res, await graphFor(root));
    }
    if (req.url === '/api/track' && req.method === 'POST') {
      const payload = await readJson(req); const root = await startTracking(payload.root); return sendJson(res, { root, graph: await graphFor(root) });
    }
    // The MCP server uses this endpoint after an agent edit. The server owns
    // the watcher; this message also makes the refresh immediate on platforms
    // where a recursive file event may be delayed.
    if (req.url === '/api/mcp-change' && req.method === 'POST') {
      const payload = await readJson(req); const root = await startTracking(payload.root); publishChange(payload.paths || []); return sendJson(res, { root, tracked: true });
    }
    if (req.url === '/api/mcp-command' && req.method === 'POST') {
      const payload = await readJson(req); publishViewerCommand(payload); return sendJson(res, { delivered: clients.size, command: payload });
    }
    if (req.url === '/api/graph-files' && req.method === 'POST') {
      const payload = await readJson(req); if (!Array.isArray(payload.files) || !payload.files.length) throw new Error('Choose a folder containing readable files.');
      const directory = await mkdtemp(join(tmpdir(), 'deepflow-'));
      try {
        await Promise.all(payload.files.slice(0, 4000).map(async entry => { const path = safeRelative(entry.path); if (!path || typeof entry.source !== 'string' || entry.source.length > 2_000_000) return; const target = join(directory, path); await mkdir(dirname(target), { recursive: true }); await writeFile(target, entry.source, 'utf8'); }));
        const graph = await graphFor(directory); graph.roots[0].label = payload.name || payload.files[0].path.split('/')[0] || 'workspace'; return sendJson(res, graph);
      } finally { await rm(directory, { recursive: true, force: true }); }
    }
    const pathname = req.url === '/' ? '/index.html' : req.url;
    const file = join(appRoot, 'public', pathname);
    const body = await readFile(file); res.writeHead(200, { 'content-type': contentTypes[extname(file)] || 'application/octet-stream' }); res.end(body);
  } catch (error) { sendJson(res, { error: error.message }, 400); }
}).listen(process.env.PORT || 4317, () => console.log('DeepFlow → http://localhost:4317'));
