import { test } from 'node:test';
import assert from 'node:assert/strict';
import { resolve, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { createRepositoryGraph } from '../src/repository-graph.js';
import {
  summarizeGraph, findInGraph, impactOf, pathBetween, explainNode, orphans, stripSources, explainFlow
} from '../src/graph-insights.js';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../fixtures/atlas-workspace');
const pythonRoot = resolve(dirname(fileURLToPath(import.meta.url)), '../fixtures/python-mini');

test('summarizeGraph returns rails, entrypoints, and hot files', async () => {
  const graph = await createRepositoryGraph({ roots: [root] });
  const summary = summarizeGraph(graph);
  assert.equal(summary.workspace, 'atlas-workspace');
  assert.ok(summary.stats.files > 10);
  assert.ok(summary.entrypoints.length >= 1);
  assert.ok(summary.hotFiles.length >= 1);
  assert.ok(summary.edgeTypes.imports || summary.edgeTypes.calls);
});

test('stripSources removes file bodies', async () => {
  const graph = await createRepositoryGraph({ roots: [pythonRoot] });
  const stripped = stripSources(graph);
  const withSource = graph.nodes.filter(n => n.meta?.source).length;
  const after = stripped.nodes.filter(n => n.meta?.source).length;
  assert.ok(withSource > 0);
  assert.equal(after, 0);
});

test('findInGraph locates python worker', async () => {
  const graph = await createRepositoryGraph({ roots: [pythonRoot] });
  const matches = findInGraph(graph, 'worker');
  assert.ok(matches.some(m => m.path.includes('worker')));
});

test('impact and explain work on python main', async () => {
  const graph = await createRepositoryGraph({ roots: [pythonRoot] });
  const impact = impactOf(graph, 'main.py');
  assert.equal(impact.target.path, 'main.py');
  assert.ok(impact.downstream.length >= 1);
  const explained = explainNode(graph, 'main.py');
  assert.equal(explained.kind, 'file');
  assert.ok(explained.relationships.length >= 1);
});

test('pathBetween finds a hop in python-mini', async () => {
  const graph = await createRepositoryGraph({ roots: [pythonRoot] });
  const path = pathBetween(graph, 'main.py', 'app/api.py', { maxDepth: 6 });
  assert.equal(path.found, true);
  assert.ok(path.hops >= 1);
});

test('orphans helper lists orphaned nodes when present', async () => {
  const graph = await createRepositoryGraph({ roots: [root] });
  const list = orphans(graph);
  assert.ok(Array.isArray(list));
  assert.ok(list.length >= 1);
});

test('explainFlow returns narrative with upstream/downstream snippets', async () => {
  const graph = await createRepositoryGraph({ roots: [pythonRoot] });
  const story = explainFlow(graph, 'main.py');
  assert.ok(!story.error);
  assert.ok(story.narrative);
  assert.ok(story.focus?.code || story.path);
  assert.ok(Array.isArray(story.upstream));
  assert.ok(Array.isArray(story.downstream));
  assert.ok(story.downstream.length >= 1);
});
