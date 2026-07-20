#!/usr/bin/env bash
# Copy-paste friendly bootstrap for agents and judges.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
PORT="${PORT:-4317}"
VIEWER="http://127.0.0.1:${PORT}"

echo "==> DeepFlow bootstrap"
echo "    checkout: $ROOT"

if ! command -v node >/dev/null 2>&1; then
  echo "ERROR: Node.js is required (v18+ recommended)." >&2
  exit 1
fi

echo "==> npm install"
npm install

viewer_up() {
  curl -sf "$VIEWER/api/health" >/dev/null 2>&1 \
    || curl -sf "$VIEWER/api/status" >/dev/null 2>&1 \
    || curl -sf "$VIEWER/" >/dev/null 2>&1
}

if viewer_up; then
  echo "==> viewer already running at $VIEWER"
else
  echo "==> starting viewer on :$PORT"
  nohup npm run dev > /tmp/deepflow-viewer.log 2>&1 &
  echo $! > /tmp/deepflow-viewer.pid
  for _ in $(seq 1 40); do
    if viewer_up; then
      break
    fi
    sleep 0.25
  done
fi

if ! viewer_up; then
  echo "ERROR: viewer failed to start. See /tmp/deepflow-viewer.log" >&2
  echo "Tip: if port $PORT is busy, stop the old process or set PORT=4318" >&2
  exit 1
fi

MCP_CONFIG="$ROOT/.deepflow.mcp.generated.json"
cat > "$MCP_CONFIG" <<EOF
{
  "mcpServers": {
    "deepflow": {
      "command": "node",
      "args": ["$ROOT/mcp-server.js"]
    }
  }
}
EOF

cat <<EOF

DeepFlow is ready.

Viewer:  $VIEWER
MCP cfg: $MCP_CONFIG

Paste MCP config into your agent IDE, then run these tools in order:

1. deepflow_status
2. deepflow_open_workspace
   root = $ROOT/fixtures/atlas-workspace
3. deepflow_demo
   root = $ROOT/fixtures/atlas-workspace
   autoPlay = true

Python demo root:
  $ROOT/fixtures/python-mini

Live map of ANY local repo:
  deepflow_open_workspace { "root": "/absolute/path/to/repo" }

EOF
