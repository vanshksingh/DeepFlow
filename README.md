<div align="center">
  <img src="./public/favicon.png" width="100" height="100" alt="DeepFlow Logo" />
  <h1>DeepFlow</h1>
  <p><strong>Live architecture signal map for agentic coding</strong></p>
</div>

<img width="1587" height="1049" alt="DeepFlow - interactive architecture signal map" src="https://github.com/user-attachments/assets/82dfc7fb-505d-4bf6-a7b9-329aa038f927" />

<br/>

Most code tools either show the human the architecture, or feed context to the agent. DeepFlow does both at the same time. Tree-sitter parses your JS/TS and Python files locally, and an MCP bridge lets any agent open a workspace, query the graph, and animate the viewer as it edits -- so you can actually watch your agent navigate the codebase in real time.

> The agent doesn't just edit files. It shows the architecture moving.

---

## Built with Codex and GPT-5.6

DeepFlow was built during OpenAI Build Week using the $100 promotional API credits.

The project started in Codex -- it was the main environment for ideating, prototyping fast, and trying out different ways to represent graph data visually. A lot of early decisions around the layout engine, animation system, and signal mode came from iterating quickly inside Codex sessions and seeing what actually looked and felt good. The Devpost plugin also helped keep the project scoped to what the hackathon was actually asking for.

GPT-5.6 Terra drove the core coding loop. Medium reasoning for architecture discussions and tradeoffs, high for precise edits and tricky bugs, and goal mode for the bigger refactors where I wanted it to run farther without stopping.

---

## Hosted Demo

Explore the live interactive fixture map: **[DeepFlow Live Demo](https://deepflow-42li.onrender.com/#path=services&mode=signal)**

*(Note: Hosted on Render's free tier. If the instance has been inactive, it may take ~50 seconds to spin back up on your first click.)*

---

## Quick Start

Paste this into any agent chat (Cursor, Claude, Codex, Antigravity, etc.) and it will install, start, and wire DeepFlow automatically.

```text
Setup DeepFlow (local codebase visualizer + MCP):
1. Clone and Bootstrap:
   git clone https://github.com/vanshksingh/DeepFlow.git && cd DeepFlow && bash scripts/agent-bootstrap.sh
   (Installs deps, starts viewer on http://127.0.0.1:4317, generates config in .deepflow.mcp.generated.json)
2. Connect: Merge generated config into your IDE's MCP settings. Verify via `deepflow_status`.
3. Usage in any repo:
   - Connect workspace: `deepflow_open_workspace {"root": "<ABS_PATH>"}`
   - Sync writes: `deepflow_after_edit {"paths": ["rel/path/to/edited"]}`
   - Trace/Explain: `deepflow_jump_to`, `deepflow_impact`, or `deepflow_summary`
   - Keep `npm run dev` running in the DeepFlow checkout.
```

**One-liner:**
```sh
bash scripts/agent-bootstrap.sh
```

**Manual:**
```sh
npm install
npm run dev          # viewer on http://localhost:4317
# in a second terminal or IDE MCP config:
# node /absolute/path/to/DeepFlow/mcp-server.js
```

---

## What it does

| | |
|--|--|
| **Live agent loop** | `deepflow_after_edit` refreshes the graph and triggers animations the moment an agent writes a file |
| **Nested frames** | Folder frames wrap file frames wrap function frames, like Figma for your codebase |
| **Trace focus** | Pin any node; unrelated rows dim and wires follow calls and imports |
| **Signal animations** | Particle bursts, fire embers, heart blooms, and typewriter effects on every edit |

**Keyboard:** `Cmd+K` / `Ctrl+K` to search, double-click a function to open source, `Esc` to collapse, drag to pan, scroll to zoom.

**Deep link:** `#path=apps/gateway/src/routes.ts&module=startIngest&mode=signal`

---

## MCP Tools

The viewer (`npm run dev`) needs to be running for tools that animate the UI. Analysis tools work headless too and return JSON.

| Tool | What it does |
|------|-------------|
| `deepflow_status` | Health check -- viewer, root, connected browsers |
| `deepflow_open_workspace` | Connect a repo and start the FS watcher (call this first) |
| `deepflow_summary` | Compact brief: languages, entrypoints, orphans, hot files |
| `deepflow_find` | Search files and modules by substring |
| `deepflow_explain` | One node: region, modules, typed edges with evidence |
| `deepflow_impact` | Upstream and downstream static impact for a path |
| `deepflow_path_between` | Directed path between two files |
| `deepflow_entrypoints` | Detected entry files |
| `deepflow_orphans` | Unreferenced code, highlighted in viewer |
| `deepflow_diagnostics` | Unresolved imports, parse issues, TODOs |
| `deepflow_after_edit` | Refresh map and trigger edit animation after a write |
| `deepflow_jump_to` | Focus a file or module, enter signal path, pulse |
| `deepflow_open_flow` | Code-flow overlay: upstream, focus, downstream + snippets |
| `deepflow_explain_flow` | Structured flow story for agents, optionally opens overlay |
| `deepflow_close_flow` | Close the code-flow overlay |
| `deepflow_highlight_paths` | Multi-select highlight and pin |
| `deepflow_clear_highlights` | Clear pins, return to rails |
| `deepflow_set_mode` | Force `rails` or `signal` mode |
| `deepflow_set_edges` | Toggle calls / imports / dataflow / events |
| `deepflow_tour` | Short Atlas walkthrough (`autoPlay: true`) |
| `deepflow_demo` | Full showcase: map, edges, live edits, overlay, orphans (`autoPlay: true`) |
| `deepflow_share_link` | Hash URL for the current focus |
| `deepflow_file_diff` | Local `git diff` for one path |
| `deepflow_analyze_workspace` | Full graph JSON |
| `deepflow_setup_help` | MCP config block + demo roots |

### Recommended agent loop

```
deepflow_status
deepflow_open_workspace { root }
deepflow_summary { root }
  ...edit files...
deepflow_after_edit { root, paths: ["..."] }
deepflow_jump_to { root, path, module?, pin: true }
deepflow_explain_flow { root, path, module? }
deepflow_impact { root, path }
```

---

## Fixtures

| Path | Use |
|------|-----|
| `fixtures/atlas-workspace` | Messy TS monorepo -- default boot target and full demo |
| `fixtures/python-mini` | Tiny Python import and call graph |

Any JS/TS/Python repo works via `deepflow_open_workspace`. Cross-language HTTP edges are not inferred; each language's own imports and calls are tracked separately.

---

## Scripts

| Command | Action |
|---------|--------|
| `npm run dev` | Viewer + API on `:4317` |
| `npm run mcp` | Stdio MCP server |
| `npm test` | Graph and insight tests |
| `npm run bootstrap` | Same as `bash scripts/agent-bootstrap.sh` |

---

## Requirements

- Node.js **18+** (20+ recommended)
- A native build toolchain only if `tree-sitter` needs to compile on your platform -- standard `npm install` is enough on macOS and Linux
- A browser open to the viewer for live animations
- Git (optional, enables diff badges on file nodes)

---

## Privacy

Everything runs locally. No source code or graph data is ever uploaded. The browser folder picker builds a static snapshot on your machine. Live watching, Git integration, and agent sync all go through MCP `deepflow_open_workspace` pointing at your disk.

```
server.js                 HTTP viewer + SSE + track API
mcp-server.js             MCP tools (stdio JSON-RPC)
src/repository-graph.js   Tree-sitter polyglot graph
src/graph-insights.js     Summary / find / impact / tour
public/                   Signal map UI
fixtures/                 Demo workspaces
AGENTS.md                 Agent contract
```
