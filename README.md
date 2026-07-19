# DeepFlow local

DeepFlow maps a repository as a draggable architectural whiteboard. Its parser is local Tree-sitter analysis—no repository content is uploaded.

From this checkout, run:

```sh
npm install && npm run dev
```

Open `http://localhost:4317`. Single click focuses a trace without moving the board; double click enters a folder or expands a file. Expanded files keep modules in source order, and source mode routes trace wires to the exact visible line badge.

## MCP (local-only)

Run the server:

```sh
npm run mcp
```

Add this to any MCP-capable local agent IDE configuration (replace the path once):

```json
{
  "mcpServers": {
    "deepflow": {
      "command": "node",
      "args": ["/absolute/path/to/DeepFlow/mcp-server.js"]
    }
  }
}
```

First call `deepflow_open_workspace` with the absolute workspace path. This connects that local workspace to the viewer and starts a filesystem watcher in the viewer process. New files, edits, and Git diff metadata then refresh in the browser automatically. `deepflow_after_edit` is available for an immediate refresh after an agent write; `deepflow_analyze_workspace` and `deepflow_file_diff` remain available for analysis.

For local development, [deepflow.mcp.json](./deepflow.mcp.json) is a ready-to-copy configuration. Replace its relative path with this checkout's absolute path if your IDE launches MCP servers from another working directory.
