import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { readFile, readdir, realpath, stat } from 'node:fs/promises';
import { basename, dirname, extname, join, normalize, relative, resolve } from 'node:path';
import Parser from 'tree-sitter';
import JavaScript from 'tree-sitter-javascript';
import TypeScript from 'tree-sitter-typescript';
import Python from 'tree-sitter-python';

const run = promisify(execFile);
const JS_EXTENSIONS = new Set(['.js', '.mjs', '.cjs', '.ts', '.tsx', '.jsx', '.mts', '.cts']);
const PY_EXTENSIONS = new Set(['.py']);
const SOURCE_EXTENSIONS = new Set([...JS_EXTENSIONS, ...PY_EXTENSIONS]);
const IGNORED = new Set([
  '.git', 'node_modules', 'dist', 'build', '.next', 'coverage',
  'venv', '.venv', '__pycache__', '.mypy_cache', '.pytest_cache',
  'site-packages', '.tox', '.eggs', 'egg-info', '.ruff_cache'
]);
const id = (...parts) => parts.map((part) => String(part).replaceAll('\\', '/')).join(':');
const isEntrypointPath = (localPath) => (
  /(?:^|\/)(?:manage|asgi|wsgi|main|app|server|route|controller|consumer|worker)\.(?:py|[cm]?[jt]sx?)$/.test(localPath)
  || /(?:^|\/)(?:__main__)\.py$/.test(localPath)
);

function emptyResult(analyzerName) {
  return { modules: [], imports: [], exports: [], calls: [], inherits: [], diagnostics: [], analyzer: analyzerName };
}

/** Parser contract: (source, context) -> { modules, imports, exports, calls, inherits?, diagnostics } */
export const jsTsAnalyzer = {
  name: 'tree-sitter-js-ts-v1',
  supports(filePath) { return JS_EXTENSIONS.has(extname(filePath)); },
  analyze(source, context) {
    const parser = new Parser();
    const extension = extname(context.path);
    parser.setLanguage(extension === '.tsx' || extension === '.jsx' ? TypeScript.tsx : ['.ts', '.mts', '.cts'].includes(extension) ? TypeScript.typescript : JavaScript);
    const tree = parser.parse(source, undefined, { bufferSize: 1024 * 1024 * 4 });
    const modules = [], imports = [], exports = [], calls = [], inherits = [], diagnostics = [];
    const lineOf = item => item.startPosition.row + 1;
    const visit = (item, callback) => { callback(item); for (const child of item.namedChildren) visit(child, callback); };
    const bindingName = item => item?.text || null;
    const declarationFor = (item, exported = false) => {
      if (item.type === 'function_declaration' || item.type === 'class_declaration') {
        const name = bindingName(item.childForFieldName('name'));
        if (name) modules.push({ name, kind: item.type === 'class_declaration' ? 'class' : 'function', exported, line: lineOf(item), end: item.endPosition.row + 1 });
        if (item.type === 'class_declaration') {
          const heritage = item.namedChildren.find(child => child.type === 'class_heritage');
          const extendsClause = heritage?.namedChildren.find(child => child.type === 'extends_clause');
          const base = extendsClause?.childForFieldName('value')?.text || extendsClause?.namedChildren.at(-1)?.text;
          if (name && base) inherits.push({ name, base, line: lineOf(heritage) });
        }
        return;
      }
      if (item.type !== 'lexical_declaration' && item.type !== 'variable_declaration') return;
      for (const declarator of item.namedChildren.filter(child => child.type === 'variable_declarator')) {
        const value = declarator.childForFieldName('value');
        if (!value || !['arrow_function', 'function_expression'].includes(value.type)) continue;
        const name = bindingName(declarator.childForFieldName('name'));
        if (name) modules.push({ name, kind: 'function', exported, line: lineOf(declarator), end: declarator.endPosition.row + 1 });
      }
    };
    for (const statement of tree.rootNode.namedChildren) {
      if (statement.type === 'export_statement') {
        const declaration = statement.childForFieldName('declaration');
        if (declaration) declarationFor(declaration, true);
        const sourceNode = statement.childForFieldName('source');
        if (sourceNode) {
          const exportClause = statement.namedChildren.find(child => child.type === 'export_clause');
          const bindings = exportClause ? exportClause.namedChildren.map(specifier => bindingName(specifier.childForFieldName('alias') || specifier.childForFieldName('name') || specifier.namedChildren.at(-1)).trim()).filter(Boolean) : [];
          imports.push({ specifier: sourceNode.text.slice(1, -1), bindings, line: lineOf(statement), reexport: true });
        }
        continue;
      }
      declarationFor(statement);
    }
    for (const statement of tree.rootNode.namedChildren.filter(item => item.type === 'import_statement')) {
      const sourceNode = statement.childForFieldName('source');
      const clause = statement.namedChildren.find(item => item.type === 'import_clause');
      const bindings = [];
      if (clause) visit(clause, item => {
        if (item.type === 'import_specifier') bindings.push(bindingName(item.childForFieldName('alias') || item.childForFieldName('name')));
        if (item.type === 'namespace_import') bindings.push(bindingName(item.namedChildren.at(-1)));
        if (item.type === 'identifier' && item.parent?.type === 'import_clause') bindings.push(bindingName(item));
      });
      if (sourceNode) imports.push({ specifier: sourceNode.text.slice(1, -1), bindings: [...new Set(bindings.filter(Boolean))], line: lineOf(statement) });
    }
    for (const module of modules.filter(item => item.exported)) exports.push({ name: module.name, line: module.line });
    const ownerAt = row => modules.find(item => row >= item.line && row <= item.end)?.name;
    visit(tree.rootNode, item => {
      if (item.type === 'call_expression') {
        const callee = item.childForFieldName('function');
        const name = callee?.type === 'identifier' ? callee.text : callee?.childForFieldName('property')?.text;
        if (!name) return;
        const line = lineOf(item);
        const type = /^(emit|publish|dispatch|send|notify)$/i.test(name) ? 'events' : /^(save|store|write|persist|render)$/i.test(name) ? 'dataflow' : 'calls';
        calls.push({ name, line, owner: ownerAt(line), type });
      }
      if (item.type === 'comment' && (item.text.includes('TODO') || item.text.includes('FIXME'))) diagnostics.push({ severity: 'notice', message: 'Contains TODO/FIXME marker' });
      if (item.type === 'throw_statement') diagnostics.push({ severity: 'warning', message: 'Contains an explicit error path' });
      if (item.type === 'ERROR') diagnostics.push({ severity: 'error', message: 'Syntax could not be parsed', line: lineOf(item) });
    });
    return { modules, imports, exports, calls, inherits, diagnostics, analyzer: context.analyzerName || jsTsAnalyzer.name };
  }
};

export const pythonAnalyzer = {
  name: 'tree-sitter-python-v1',
  supports(filePath) { return PY_EXTENSIONS.has(extname(filePath)); },
  analyze(source, context) {
    const parser = new Parser();
    parser.setLanguage(Python);
    const tree = parser.parse(source, undefined, { bufferSize: 1024 * 1024 * 4 });
    const modules = [], imports = [], exports = [], calls = [], inherits = [], diagnostics = [];
    const lineOf = item => item.startPosition.row + 1;
    const visit = (item, callback) => { callback(item); for (const child of item.namedChildren) visit(child, callback); };
    const nameOf = item => item?.childForFieldName?.('name')?.text || item?.namedChildren?.find(child => child.type === 'identifier')?.text || null;

    visit(tree.rootNode, item => {
      if (item.type === 'function_definition') {
        // Skip nested methods' outer registration by allowing all; methods are useful for traces.
        const name = nameOf(item);
        if (!name || name.startsWith('_') && name !== '__init__' && name !== '__main__') return;
        const parentClass = (() => {
          for (let cursor = item.parent; cursor; cursor = cursor.parent) {
            if (cursor.type === 'class_definition') return nameOf(cursor);
            if (cursor.type === 'function_definition' && cursor !== item) return null;
          }
          return null;
        })();
        if (parentClass && name === '__init__') return;
        const label = parentClass && name !== parentClass ? `${parentClass}.${name}` : name;
        modules.push({ name: label, kind: parentClass ? 'method' : 'function', exported: !name.startsWith('_'), line: lineOf(item), end: item.endPosition.row + 1 });
        return;
      }
      if (item.type === 'class_definition') {
        const name = nameOf(item);
        if (!name) return;
        modules.push({ name, kind: 'class', exported: true, line: lineOf(item), end: item.endPosition.row + 1 });
        const args = item.namedChildren.find(child => child.type === 'argument_list');
        for (const base of args?.namedChildren || []) {
          const baseName = base.type === 'identifier' ? base.text : base.namedChildren?.find(child => child.type === 'identifier')?.text;
          if (baseName) inherits.push({ name, base: baseName, line: lineOf(item) });
        }
        return;
      }
      if (item.type === 'import_from_statement') {
        const match = item.text.match(/^from\s+(\.*[\w.]*)\s+import\s+(.+)$/s);
        if (!match) return;
        const specifier = match[1];
        const importedSide = match[2].split('#')[0].trim();
        const bindings = importedSide === '*'
          ? ['*']
          : importedSide
            .replace(/^\(|\)$/g, '')
            .split(',')
            .map(part => part.trim().split(/\s+as\s+/i)[0].trim())
            .filter(Boolean);
        if (specifier === '.' || /^\.+$/.test(specifier)) {
          for (const binding of bindings) imports.push({ specifier: `${specifier}${binding}`, bindings: [binding], line: lineOf(item), language: 'python' });
          return;
        }
        imports.push({ specifier, bindings, line: lineOf(item), language: 'python' });
        return;
      }
      if (item.type === 'import_statement') {
        for (const name of item.namedChildren.filter(child => child.type === 'dotted_name')) {
          imports.push({ specifier: name.text, bindings: [name.namedChildren.at(-1)?.text || name.text], line: lineOf(item), language: 'python' });
        }
        return;
      }
      if (item.type === 'call') {
        const fn = item.childForFieldName('function') || item.namedChildren[0];
        const name = fn?.type === 'identifier'
          ? fn.text
          : fn?.type === 'attribute'
            ? fn.namedChildren.find(child => child.type === 'identifier' && child === fn.namedChildren.at(-1))?.text || fn.text.split('.').pop()
            : null;
        if (!name || ['print', 'len', 'str', 'int', 'list', 'dict', 'set', 'range', 'type', 'isinstance', 'super'].includes(name)) return;
        const line = lineOf(item);
        const ownerAt = row => modules.find(entry => row >= entry.line && row <= entry.end)?.name;
        const type = /^(emit|publish|dispatch|send|notify)$/i.test(name) ? 'events' : /^(save|store|write|persist|render)$/i.test(name) ? 'dataflow' : 'calls';
        calls.push({ name, line, owner: ownerAt(line), type });
      }
      if (item.type === 'comment' && (item.text.includes('TODO') || item.text.includes('FIXME'))) diagnostics.push({ severity: 'notice', message: 'Contains TODO/FIXME marker' });
      if (item.type === 'ERROR') diagnostics.push({ severity: 'error', message: 'Syntax could not be parsed', line: lineOf(item) });
    });

    for (const module of modules.filter(item => item.exported)) exports.push({ name: module.name, line: module.line });
    return { modules, imports, exports, calls, inherits, diagnostics, analyzer: context.analyzerName || pythonAnalyzer.name };
  }
};

export const defaultAnalyzer = {
  name: 'tree-sitter-polyglot-v1',
  supports(filePath) { return jsTsAnalyzer.supports(filePath) || pythonAnalyzer.supports(filePath); },
  analyze(source, context) {
    if (pythonAnalyzer.supports(context.path)) return pythonAnalyzer.analyze(source, { ...context, analyzerName: pythonAnalyzer.name });
    if (jsTsAnalyzer.supports(context.path)) return jsTsAnalyzer.analyze(source, { ...context, analyzerName: jsTsAnalyzer.name });
    return emptyResult(defaultAnalyzer.name);
  }
};

async function walk(directory, root = directory) {
  const entries = await readdir(directory, { withFileTypes: true }); const results = [];
  for (const entry of entries) {
    if (IGNORED.has(entry.name) || entry.name.endsWith('.egg-info')) continue;
    const target = join(directory, entry.name);
    if (entry.isDirectory()) results.push(...await walk(target, root));
    else results.push(target);
  }
  return results;
}
async function gitMetadata(rootPath) {
  try {
    const realRoot = await realpath(rootPath);
    const [{ stdout: gitRootOut }, { stdout: head }] = await Promise.all([run('git', ['-C', rootPath, 'rev-parse', '--show-toplevel'], { timeout: 1800 }), run('git', ['-C', rootPath, 'rev-parse', '--short', 'HEAD'], { timeout: 1800 })]);
    const gitRoot = gitRootOut.trim();
    const { stdout: status } = await run('git', ['-C', gitRoot, 'status', '--porcelain=v1', '--untracked-files=all', '--', realRoot], { timeout: 1800 });
    const changes = new Map();
    for (const line of status.split('\n').filter(Boolean)) {
      const state = line.slice(0, 2).trim() || 'M';
      const repoPath = line.slice(3).split(' -> ').pop().replace(/^"|"$/g, '');
      const absolutePath = resolve(gitRoot, repoPath);
      const localPath = relative(realRoot, absolutePath).replaceAll('\\', '/');
      if (localPath && !localPath.startsWith('..')) changes.set(localPath, { state, repoPath, absolutePath });
    }
    const diffs = new Map();
    await Promise.all([...changes.entries()].slice(0, 160).map(async ([path, change]) => {
      try {
        const isNew = change.state === '??';
        const args = isNew ? ['-C', gitRoot, 'diff', '--no-index', '--unified=3', '--', '/dev/null', change.absolutePath] : ['-C', gitRoot, 'diff', '--no-ext-diff', '--unified=3', 'HEAD', '--', change.repoPath];
        const { stdout } = await run('git', args, { timeout: 2400 });
        if (stdout) diffs.set(path, stdout);
      } catch (error) { if (error.stdout) diffs.set(path, error.stdout); }
    }));
    return { head: head.trim(), changes: new Map([...changes].map(([path, change]) => [path, change.state])), diffs };
  } catch { return { head: null, changes: new Map(), diffs: new Map() }; }
}

function resolvePythonImport(specifier, fromPath, fileByAbsolute) {
  if (!specifier) return null;
  if (specifier.startsWith('.')) {
    let dots = 0;
    while (specifier[dots] === '.') dots += 1;
    const rest = specifier.slice(dots).replaceAll('.', '/');
    let dir = dirname(fromPath);
    for (let i = 1; i < dots; i += 1) dir = dirname(dir);
    const base = rest ? join(dir, rest) : dir;
    const candidates = [`${base}.py`, join(base, '__init__.py')];
    return candidates.map(normalize).find(candidate => fileByAbsolute.has(candidate)) || null;
  }
  const parts = specifier.replaceAll('.', '/');
  let dir = dirname(fromPath);
  for (let i = 0; i < 10; i += 1) {
    const base = join(dir, parts);
    for (const candidate of [`${base}.py`, join(base, '__init__.py')]) {
      if (fileByAbsolute.has(normalize(candidate))) return normalize(candidate);
    }
    const parent = dirname(dir);
    if (parent === dir) break;
    dir = parent;
  }
  for (const absolute of fileByAbsolute.keys()) {
    if (absolute.endsWith(`/${parts}.py`) || absolute.endsWith(`/${parts}/__init__.py`)) return absolute;
  }
  return null;
}

function jsCandidates(base) {
  return [
    base,
    ...[...JS_EXTENSIONS].map(extension => base + extension),
    ...[...JS_EXTENSIONS].map(extension => base.replace(/\.[cm]?[jt]sx?$/, extension)),
    ...[...JS_EXTENSIONS].map(extension => join(base, 'index' + extension))
  ];
}

function firstExisting(candidates, fileByAbsolute) {
  for (const candidate of candidates) {
    const normalized = normalize(candidate);
    if (fileByAbsolute.has(normalized)) return normalized;
  }
  return null;
}

function resolvePackageField(pkgDir, field, fileByAbsolute) {
  if (!field || typeof field !== 'string') return null;
  const cleaned = field.replace(/^\.\//, '');
  return firstExisting(jsCandidates(join(pkgDir, cleaned)), fileByAbsolute);
}

function resolvePackageImport(specifier, packageRoots, fileByAbsolute, packageMeta = new Map()) {
  const hit = [...packageRoots.entries()].find(([name]) => specifier === name || specifier.startsWith(name + '/'));
  if (!hit) return null;
  const [pkgName, pkgDir] = hit;
  const subpath = specifier === pkgName ? '' : specifier.slice(pkgName.length + 1);
  if (subpath) return firstExisting(jsCandidates(join(pkgDir, subpath)), fileByAbsolute);
  const meta = packageMeta.get(pkgName) || {};
  const fromExports = meta.exports;
  if (typeof fromExports === 'string') {
    const hitExport = resolvePackageField(pkgDir, fromExports, fileByAbsolute);
    if (hitExport) return hitExport;
  } else if (fromExports && typeof fromExports === 'object') {
    const dot = fromExports['.'] || fromExports['./'];
    const entry = typeof dot === 'string' ? dot : (dot && (dot.import || dot.default || dot.require));
    const hitExport = resolvePackageField(pkgDir, entry, fileByAbsolute);
    if (hitExport) return hitExport;
  }
  for (const field of [meta.module, meta.main]) {
    const hitField = resolvePackageField(pkgDir, field, fileByAbsolute);
    if (hitField) return hitField;
  }
  return firstExisting([
    ...jsCandidates(join(pkgDir, 'src/index')),
    ...jsCandidates(join(pkgDir, 'index'))
  ], fileByAbsolute);
}

function findBindingInPackage(pkgDir, binding, moduleByFileAndName, fileByAbsolute) {
  if (!binding || binding === '*') return null;
  const root = normalize(pkgDir);
  for (const [, mod] of moduleByFileAndName) {
    if (mod.label !== binding && !mod.label.endsWith(`.${binding}`)) continue;
    const file = [...fileByAbsolute.values()].find(f => f.id === mod.fileId || f.id === mod.parentId);
    if (!file) continue;
    if (normalize(file.absolutePath) === root || normalize(file.absolutePath).startsWith(root + '/')) {
      return { file, mod };
    }
  }
  return null;
}

function resolveImport(specifier, fromPath, fileByAbsolute, packageRoots, packageMeta = new Map()) {
  if (extname(fromPath) === '.py') return resolvePythonImport(specifier, fromPath, fileByAbsolute);
  if (specifier.startsWith('.')) {
    const base = resolve(dirname(fromPath), specifier);
    return firstExisting(jsCandidates(base), fileByAbsolute);
  }
  return resolvePackageImport(specifier, packageRoots, fileByAbsolute, packageMeta);
}

function languageFor(filePath) {
  if (PY_EXTENSIONS.has(extname(filePath))) return 'python';
  if (JS_EXTENSIONS.has(extname(filePath))) return 'javascript-typescript';
  return 'asset';
}

export async function createRepositoryGraph({ roots, analyzer = defaultAnalyzer }) {
  const normalizedRoots = roots.map((path, index) => ({ id: `root-${index + 1}`, path: resolve(path), label: basename(path) || path }));
  const nodes = [], edges = [], diagnostics = [], files = [], folders = new Map(), packageRoots = new Map(), packageMeta = new Map();
  for (const root of normalizedRoots) {
    const all = await walk(root.path); const git = await gitMetadata(root.path);
    folders.set(id(root.id, '/'), { id: id(root.id, '/'), kind: 'folder', rootId: root.id, parentId: root.id, label: root.label, path: '/', depth: 0 });
    for (const absolutePath of all) {
      const localPath = relative(root.path, absolutePath).replaceAll('\\', '/');
      const isSource = analyzer.supports(absolutePath);
      const fileId = id(root.id, 'file', localPath);
      const file = {
        id: fileId, kind: 'file', rootId: root.id, parentId: null, label: basename(localPath), path: localPath,
        extension: extname(localPath), language: languageFor(absolutePath), entrypoint: isEntrypointPath(localPath),
        git: { change: git.changes.get(localPath) || null, diff: git.diffs.get(localPath) || null, head: git.head }, meta: {}
      };
      const parts = localPath.split('/').slice(0, -1); let parentId = id(root.id, '/');
      for (let depth = 1; depth <= parts.length; depth++) {
        const folderPath = parts.slice(0, depth).join('/');
        const folderId = id(root.id, 'folder', folderPath);
        if (!folders.has(folderId)) folders.set(folderId, { id: folderId, kind: 'folder', rootId: root.id, parentId, label: parts[depth - 1], path: folderPath, depth });
        parentId = folderId;
      }
      file.parentId = parentId; files.push({ ...file, absolutePath }); nodes.push(file);
      edges.push({ id: id('contains', parentId, fileId), type: 'contains', from: parentId, to: fileId, evidence: 'folder contains file', confidence: 'high' });
      if (basename(absolutePath) === 'package.json') {
        try {
          const pkg = JSON.parse(await readFile(absolutePath, 'utf8'));
          if (pkg.name) {
            packageRoots.set(pkg.name, dirname(absolutePath));
            packageMeta.set(pkg.name, { main: pkg.main, module: pkg.module, exports: pkg.exports });
          }
        } catch {}
      }
    }
  }
  nodes.unshift(...folders.values());
  const fileByAbsolute = new Map(files.map((file) => [normalize(file.absolutePath), file]));
  const moduleByFileAndName = new Map();
  const importsByFile = new Map();
  for (const file of files.filter((item) => analyzer.supports(item.absolutePath))) {
    const source = await readFile(file.absolutePath, 'utf8'); let result;
    try { result = analyzer.analyze(source, { path: file.path, analyzerName: analyzer.name }); }
    catch (error) { result = { ...emptyResult(analyzer.name), diagnostics: [{ severity: 'error', message: `Analyzer failed: ${error.message}` }] }; }
    file.meta = { analyzer: result.analyzer, loc: source.split('\n').length, imports: result.imports.length, exports: result.exports.length, source };
    Object.assign(nodes.find((item) => item.id === file.id).meta, file.meta);
    for (const module of result.modules) {
      const moduleId = id(file.id, 'module', module.name);
      const node = {
        id: moduleId, kind: 'module', rootId: file.rootId, parentId: file.id, fileId: file.id, label: module.name, path: file.path,
        moduleKind: module.kind, exported: module.exported,
        entrypoint: /^(start|handle|main|run|serve|create_app|get_app)/i.test(module.name.split('.').pop()),
        loc: { start: module.line, end: module.end }, meta: {}
      };
      nodes.push(node);
      moduleByFileAndName.set(`${file.id}:${module.name}`, node);
      // Also index short method name for call resolution (App.run → run)
      const short = module.name.includes('.') ? module.name.split('.').pop() : null;
      if (short && !moduleByFileAndName.has(`${file.id}:${short}`)) moduleByFileAndName.set(`${file.id}:${short}`, node);
      edges.push({ id: id('contains', file.id, moduleId), type: 'contains', from: file.id, to: moduleId, evidence: `${file.label} defines ${module.name}()`, confidence: 'high' });
      if (module.exported) edges.push({ id: id('exports', moduleId, file.id), type: 'exports', from: moduleId, to: file.id, evidence: `${file.label} exports ${module.name}`, line: module.line, confidence: 'high' });
    }
    importsByFile.set(file.id, result);
    for (const item of result.diagnostics) diagnostics.push({ ...item, fileId: file.id, path: file.path });
  }
  for (const file of files.filter((item) => importsByFile.has(item.id))) {
    const result = importsByFile.get(file.id);
    for (const imported of result.imports) {
      let targetPath = resolveImport(imported.specifier, file.absolutePath, fileByAbsolute, packageRoots, packageMeta);
      let target = targetPath ? fileByAbsolute.get(normalize(targetPath)) : null;
      if (!target) {
        const pkgHit = [...packageRoots.entries()].find(([name]) => imported.specifier === name || imported.specifier.startsWith(name + '/'));
        if (pkgHit && (imported.specifier === pkgHit[0])) {
          const linked = [];
          for (const binding of imported.bindings || []) {
            const found = findBindingInPackage(pkgHit[1], binding, moduleByFileAndName, fileByAbsolute);
            if (!found) continue;
            linked.push(found);
            if (!target) target = found.file;
          }
          if (target) {
            edges.push({ id: id('imports', file.id, target.id, imported.line), type: imported.reexport ? 'reexports' : 'imports', from: file.id, to: target.id, evidence: `${file.label} imports ${imported.specifier}`, line: imported.line, confidence: 'high' });
            for (const { mod } of linked) {
              edges.push({ id: id('references', file.id, mod.id, imported.line), type: 'references', from: file.id, to: mod.id, evidence: `imports ${mod.label}`, line: imported.line, confidence: 'high' });
            }
            continue;
          }
        }
      }
      if (!target) {
        if (file.extension === '.py' && !imported.specifier.startsWith('.')) continue;
        diagnostics.push({ severity: 'error', path: file.path, fileId: file.id, line: imported.line, message: `Unresolved import: ${imported.specifier}` });
        continue;
      }
      edges.push({ id: id('imports', file.id, target.id, imported.line), type: imported.reexport ? 'reexports' : 'imports', from: file.id, to: target.id, evidence: `${file.label} imports ${imported.specifier}`, line: imported.line, confidence: 'high' });
      for (const binding of imported.bindings) {
        if (binding === '*') continue;
        let importedModule = moduleByFileAndName.get(`${target.id}:${binding}`);
        if (!importedModule) {
          const pkgHit = [...packageRoots.entries()].find(([name]) => imported.specifier === name || imported.specifier.startsWith(name + '/'));
          if (pkgHit) {
            const found = findBindingInPackage(pkgHit[1], binding, moduleByFileAndName, fileByAbsolute);
            importedModule = found?.mod || null;
            if (found && found.file.id !== target.id) {
              edges.push({ id: id('imports', file.id, found.file.id, imported.line, binding), type: 'imports', from: file.id, to: found.file.id, evidence: `${file.label} imports ${imported.specifier}`, line: imported.line, confidence: 'medium' });
            }
          }
        }
        if (importedModule) edges.push({ id: id('references', file.id, importedModule.id, imported.line), type: 'references', from: file.id, to: importedModule.id, evidence: `imports ${binding}`, line: imported.line, confidence: 'high' });
      }
    }
    for (const call of result.calls) {
      const sourceModule = call.owner ? moduleByFileAndName.get(`${file.id}:${call.owner}`) : null;
      const local = moduleByFileAndName.get(`${file.id}:${call.name}`);
      const imported = result.imports.find((entry) => entry.bindings.includes(call.name));
      let target = local;
      if (!target && imported) {
        const targetPath = resolveImport(imported.specifier, file.absolutePath, fileByAbsolute, packageRoots);
        const targetFile = targetPath && fileByAbsolute.get(normalize(targetPath));
        target = targetFile && moduleByFileAndName.get(`${targetFile.id}:${call.name}`);
      }
      if (sourceModule && target) edges.push({ id: id(call.type, sourceModule.id, target.id, call.line), type: call.type, from: sourceModule.id, to: target.id, evidence: `${sourceModule.label}() ${call.type === 'calls' ? 'calls' : call.type} ${target.label}()`, line: call.line, confidence: target === local ? 'high' : 'medium' });
    }
    for (const inheritance of result.inherits || []) {
      const sourceModule = moduleByFileAndName.get(`${file.id}:${inheritance.name}`);
      const local = moduleByFileAndName.get(`${file.id}:${inheritance.base}`);
      const imported = result.imports.find(entry => entry.bindings.includes(inheritance.base));
      let target = local;
      if (!target && imported) {
        const targetPath = resolveImport(imported.specifier, file.absolutePath, fileByAbsolute, packageRoots);
        const targetFile = targetPath && fileByAbsolute.get(normalize(targetPath));
        target = targetFile && moduleByFileAndName.get(`${targetFile.id}:${inheritance.base}`);
      }
      if (sourceModule && target) edges.push({ id: id('inherits', sourceModule.id, target.id, inheritance.line), type: 'inherits', from: sourceModule.id, to: target.id, evidence: `${sourceModule.label} extends ${target.label}`, line: inheritance.line, confidence: target === local ? 'high' : 'medium' });
    }
  }
  const structural = new Set(['contains']);
  const linked = new Set(edges.filter((edge) => !structural.has(edge.type)).flatMap((edge) => [edge.from, edge.to]));
  const isExecutableCandidate = (item) => item.kind === 'module' || (item.kind === 'file' && SOURCE_EXTENSIONS.has(item.extension) && !item.entrypoint && !/(?:^|\/)(?:config|scripts|docs|tests?|migrations)\//.test(item.path) && !/\.(?:config|setup)\.[cm]?[jt]sx?$/.test(item.path));
  for (const node of nodes) if (isExecutableCandidate(node) && !linked.has(node.id)) { node.orphan = true; node.orphanReason = 'No static execution references were found.'; }
  return {
    version: '1.0',
    analyzer: analyzer.name,
    roots: normalizedRoots,
    nodes,
    edges,
    diagnostics,
    stats: {
      folders: nodes.filter((node) => node.kind === 'folder').length,
      files: files.length,
      modules: nodes.filter((node) => node.kind === 'module').length,
      edges: edges.length,
      orphaned: nodes.filter((node) => node.orphan).length
    }
  };
}
