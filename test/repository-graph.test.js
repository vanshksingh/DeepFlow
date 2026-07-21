import test from 'node:test';
import assert from 'node:assert/strict';
import { createRepositoryGraph, defaultAnalyzer, jsTsAnalyzer, pythonAnalyzer } from '../src/repository-graph.js';

const fixture = new URL('../fixtures/atlas-workspace', import.meta.url).pathname;
const pythonFixture = new URL('../fixtures/python-mini', import.meta.url).pathname;

test('indexes nested folders, modules, typed edges, and diagnostics', async () => {
  const graph = await createRepositoryGraph({ roots: [fixture] });
  assert.equal(graph.version, '1.0');
  assert.ok(graph.nodes.some((node) => node.kind === 'folder' && node.path === 'services/ingest/src/worker'));
  assert.ok(graph.nodes.some((node) => node.kind === 'module' && node.label === 'startIngest' && node.entrypoint));
  assert.ok(graph.edges.some((edge) => edge.type === 'imports'));
  assert.ok(graph.edges.some((edge) => edge.type === 'calls'));
  assert.ok(graph.edges.some((edge) => edge.type === 'exports'));
  assert.ok(graph.diagnostics.some((diagnostic) => diagnostic.message.includes('@atlas/does-not-exist')));
  assert.equal(graph.nodes.find((node) => node.path === 'README.md' && node.kind === 'file').orphan, undefined);
  assert.equal(graph.nodes.find((node) => node.path === 'config/eslint.config.js' && node.kind === 'file').orphan, undefined);
  assert.match(graph.nodes.find((node) => node.path.endsWith('documentRoutes.ts') && node.kind === 'file').meta.source, /startIngest/);
  assert.ok(graph.nodes.find((node) => node.path.endsWith('staleFeatureFlag.ts') && node.kind === 'file').orphan);
  assert.ok(!graph.edges.some((edge) => edge.type === 'calls' && edge.from === edge.to));
});

test('uses Tree-sitter for TypeScript and TSX semantic extraction', () => {
  const source = `
    import { run as start } from './runner';
    export const Screen = () => <button onClick={() => start()} />;
    export class Child extends Parent { execute() { return start(); } }
  `;
  const result = jsTsAnalyzer.analyze(source, { path: 'ui/Screen.tsx', analyzerName: jsTsAnalyzer.name });
  assert.equal(jsTsAnalyzer.name, 'tree-sitter-js-ts-v1');
  assert.deepEqual(result.imports[0].bindings, ['start']);
  assert.ok(result.modules.some(module => module.name === 'Screen' && module.exported));
  assert.ok(result.modules.some(module => module.name === 'Child' && module.kind === 'class'));
  assert.ok(result.calls.some(call => call.name === 'start'));
  assert.deepEqual(result.inherits, [{ name: 'Child', base: 'Parent', line: 4 }]);
});

test('extracts Python modules, imports, and calls', () => {
  const source = `
from services.worker import start

def create_app():
    start()
    return True

class App(Base):
    def run(self):
        create_app()
`;
  assert.equal(defaultAnalyzer.supports('app/api.py'), true);
  const result = pythonAnalyzer.analyze(source, { path: 'app/api.py', analyzerName: pythonAnalyzer.name });
  assert.ok(result.imports.some(item => item.specifier === 'services.worker' && item.bindings.includes('start')));
  assert.ok(result.modules.some(module => module.name === 'create_app'));
  assert.ok(result.modules.some(module => module.name === 'App'));
  assert.ok(result.modules.some(module => module.name === 'App.run'));
  assert.ok(result.calls.some(call => call.name === 'start'));
  assert.ok(result.inherits.some(item => item.name === 'App' && item.base === 'Base'));
});

test('indexes a Python workspace with import and call edges', async () => {
  const graph = await createRepositoryGraph({ roots: [pythonFixture] });
  assert.ok(graph.nodes.some(node => node.kind === 'file' && node.path === 'main.py' && node.language === 'python'));
  assert.ok(graph.nodes.some(node => node.kind === 'module' && node.label === 'create_app'));
  assert.ok(graph.edges.some(edge => edge.type === 'imports' && edge.evidence.includes('imports app.api')));
  assert.ok(graph.edges.some(edge => edge.type === 'calls'));
});

test('workspace package imports resolve to source files, not package.json', async () => {
  const graph = await createRepositoryGraph({ roots: [fixture] });
  const sharedImport = graph.edges.find(edge =>
    edge.type === 'imports'
    && edge.evidence.includes('imports @atlas/shared')
  );
  assert.ok(sharedImport, 'expected an imports edge for @atlas/shared');
  const target = graph.nodes.find(node => node.id === sharedImport.to);
  assert.ok(target);
  assert.equal(target.kind, 'file');
  assert.ok(target.path.endsWith('.ts') || target.path.endsWith('.js'), `expected source file, got ${target.path}`);
  assert.ok(!target.path.endsWith('package.json'));
  assert.ok(graph.edges.some(edge =>
    edge.type === 'references' && edge.evidence.includes('createId')
  ));
});
