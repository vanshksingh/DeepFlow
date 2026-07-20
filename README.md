# DeepFlow

**Local architecture signal map for agentic coding.**  
Tree-sitter parses JS/TS + Python on your machine. An MCP bridge lets any agent open a workspace, narrate the graph, jump to impact, and pulse the live viewer as it edits — no cloud upload.

> OpenAI Build Week style pitch: the agent doesn’t just edit files — it *shows* the architecture moving.

---

## Agent copy-paste setup (do this first)

Paste the block below into an agent chat (Cursor / Claude / Codex / etc.). It is enough to install, start, and wire DeepFlow.

```text
You are setting up DeepFlow, a local repo architecture map with MCP tools.

CHECKOUT: use the absolute path of this DeepFlow repo (the folder that contains package.json and mcp-server.js).

Do exactly this:

1. cd <CHECKOUT>
2. Run: bash scripts/agent-bootstrap.sh
   - This runs npm install, starts the viewer on http://127.0.0.1:4317 if needed,
     and writes .deepflow.mcp.generated.json with an absolute MCP path.
3. Add the generated MCP server to the IDE MCP config (merge mcpServers.deepflow).
4. Confirm with MCP tool deepflow_status → ok:true.
5. Demo (TypeScript monorepo fixture):
   - deepflow_open_workspace
     { "root": "<CHECKOUT>/fixtures/atlas-workspace" }
   - Open http://127.0.0.1:4317 in the browser if it is not already open.
   - deepflow_tour
     { "root": "<CHECKOUT>/fixtures/atlas-workspace", "autoPlay": true }
6. Python demo (optional):
   - deepflow_open_workspace
     { "root": "<CHECKOUT>/fixtures/python-mini" }
   - deepflow_summary { "root": "<CHECKOUT>/fixtures/python-mini" }
   - deepflow_jump_to { "root": "<CHECKOUT>/fixtures/python-mini", "path": "main.py", "module": "main" }
7. For the user’s real project:
   - deepflow_open_workspace { "root": "<ABSOLUTE_PATH_TO_THEIR_REPO>" }
   - After every edit batch: deepflow_after_edit with changed relative paths
   - Narrate with deepflow_jump_to / deepflow_impact / deepflow_explain

Rules while coding with DeepFlow:
- Always keep `npm run dev` (viewer) running before MCP viewer tools.
- Prefer deepflow_summary over full analyze for planning.
- After writes: deepflow_after_edit, then deepflow_jump_to on the changed file.
- Never upload repo contents; DeepFlow is local-only.
```

One-liner if you are already in the checkout:

```sh
bash scripts/agent-bootstrap.sh
```

Manual equivalent:

```sh
npm install
npm run dev          # terminal A — http://localhost:4317
# terminal B / IDE MCP:
# node /absolute/path/to/DeepFlow/mcp-server.js
```

---

## What judges see

| Mode | Meaning |
|------|---------|
| **Nested frames** | Figma-style encapsulation: folder frames wrap file frames wrap function frames → source |
| **Trace focus** | Select/pin a node; unrelated rows dim; wires follow calls/imports |
| **Live agent loop** | Watcher + `deepflow_after_edit` refreshes diffs/activity without reloading the story |

Keyboard: `⌘K` / `Ctrl+K` search · double-click function for source · `Esc` collapses · drag empty canvas to pan · wheel zoom.

Deep links: `#path=apps/gateway/src/documentRoutes.ts&module=startIngest&mode=signal`

---

## MCP tools

Viewer must be up (`npm run dev`) for tools that animate the UI. Analysis tools still work if the viewer is down (they print JSON).

| Tool | Purpose |
|------|---------|
| `deepflow_setup_help` | Absolute MCP config + demo roots |
| `deepflow_status` | Health of viewer / tracked root / connected browsers |
| `deepflow_open_workspace` | Connect workspace + start FS watcher (**call first**) |
| `deepflow_summary` | Compact briefing: rails, langs, entrypoints, orphans, hot files |
| `deepflow_analyze_workspace` | Full graph JSON (sources stripped by default) |
| `deepflow_find` | Search files/modules by substring |
| `deepflow_explain` | One node: region, modules, typed edges with evidence |
| `deepflow_impact` | Upstream / downstream static impact |
| `deepflow_path_between` | Directed path between two files |
| `deepflow_entrypoints` | Detected entry files |
| `deepflow_orphans` | Unreferenced code (+ highlight in viewer) |
| `deepflow_diagnostics` | Unresolved imports / parse issues / TODOs |
| `deepflow_after_edit` | Immediate refresh after agent writes |
| `deepflow_jump_to` | Focus file/module/line; enter signal path; pulse |
| `deepflow_open_flow` | Open code-flow overlay (upstream ← focus → downstream + snippets) |
| `deepflow_explain_flow` | Structured flow story for agents; optionally opens the overlay |
| `deepflow_close_flow` | Close the code-flow overlay |
| `deepflow_highlight_paths` | Multi-select highlight / pin |
| `deepflow_clear_highlights` | Clear pins; return to rails |
| `deepflow_set_mode` | Force `rails` or `signal` |
| `deepflow_set_edges` | Toggle calls/imports/dataflow/events/… |
| `deepflow_tour` | Built-in Atlas walkthrough (`autoPlay: true`) |
| `deepflow_share_link` | Hash URL for the current focus |
| `deepflow_file_diff` | Local `git diff` for one path |

### Recommended agent loop

```text
deepflow_status
→ deepflow_open_workspace { root }
→ deepflow_summary { root }
→ …edit files…
→ deepflow_after_edit { root, paths: ["…"] }
→ deepflow_jump_to { root, path, module?, pin: true }
→ deepflow_explain_flow { root, path, module? }   # narrate inherit/call/emit with overlay
→ deepflow_impact { root, path }   # when explaining a change
```

### MCP config shape

```json
{
  "mcpServers": {
    "deepflow": {
      "command": "node",
      "args": ["/ABSOLUTE/PATH/TO/DeepFlow/mcp-server.js"]
    }
  }
}
```

`deepflow_setup_help` and `scripts/agent-bootstrap.sh` both emit this with the correct absolute path.  
`deepflow.mcp.json` is a hand-maintained example — prefer the generated file.

---

## Fixtures

| Path | Use |
|------|-----|
| `fixtures/atlas-workspace` | Messy TS monorepo — default viewer boot + tour |
| `fixtures/python-mini` | Tiny Python import/call graph |

Any other local JS/TS/Python (or full-stack) repo works via `deepflow_open_workspace` with an absolute path. Cross-language HTTP edges are not inferred yet; each language’s imports/calls are.

---

## Scripts

| Command | What |
|---------|------|
| `npm run dev` | Viewer + API on `:4317` (`PORT` overrides) |
| `npm run mcp` | Stdio MCP server |
| `npm test` | Graph + insight tests |
| `npm run bootstrap` | Same as `bash scripts/agent-bootstrap.sh` |

---

## Requirements

- Node.js **18+** (20+ ideal)
- Native build toolchain only if `tree-sitter` needs to compile on your platform (usual `npm install` is enough on macOS/Linux with standard Node binaries)
- Browser open to the viewer for live MCP animation
- Git optional (enables local diff badges)

---

## Project layout

```text
server.js           HTTP viewer + SSE + track API
mcp-server.js       MCP tools (stdio JSON-RPC)
src/repository-graph.js   Tree-sitter polyglot graph
src/graph-insights.js     summary / find / impact / tour
public/             signal-map UI
fixtures/           demo workspaces
AGENTS.md           short agent contract
```

---

## Privacy

All parsing is local. The browser “Open” folder picker builds a **static snapshot**. Live watch + Git + agent sync require MCP `deepflow_open_workspace` (or the default fixture already tracked by `npm run dev`).
