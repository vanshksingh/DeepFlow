import test from 'node:test';
import assert from 'node:assert/strict';
import { createRepositoryGraph, defaultAnalyzer } from '../src/repository-graph.js';

const fixture = new URL('../fixtures/atlas-workspace', import.meta.url).pathname;

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
  const result = defaultAnalyzer.analyze(source, { path: 'ui/Screen.tsx', analyzerName: defaultAnalyzer.name });
  assert.equal(defaultAnalyzer.name, 'tree-sitter-js-ts-v1');
  assert.deepEqual(result.imports[0].bindings, ['start']);
  assert.ok(result.modules.some(module => module.name === 'Screen' && module.exported));
  assert.ok(result.modules.some(module => module.name === 'Child' && module.kind === 'class'));
  assert.ok(result.calls.some(call => call.name === 'start'));
  assert.deepEqual(result.inherits, [{ name: 'Child', base: 'Parent', line: 4 }]);
});
