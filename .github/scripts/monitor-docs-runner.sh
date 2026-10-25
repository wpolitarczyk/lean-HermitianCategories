#!/usr/bin/env bash
set -euo pipefail

snapshot() {
  date -u '+%Y-%m-%dT%H:%M:%SZ'
  free -m
  swapon --show
  df -h "$GITHUB_WORKSPACE" "$RUNNER_TEMP"
  echo 'Largest processes by resident memory (RSS and VSZ in KiB; NLWP = threads)'
  # Use process names rather than command lines to avoid logging arguments.
  ps -eo pid,ppid,comm,rss,vsz,nlwp,%mem,%cpu --sort=-rss | sed -n '1,16p'
  if [[ "${DOCS_DIAGNOSTICS_DETAILED:-false}" == 'true' ]]; then
    echo 'System memory commitments and pressure'
    grep -E '^(MemAvailable|SwapTotal|SwapFree|CommitLimit|Committed_AS|PageTables|Slab):' /proc/meminfo || true
    cat /proc/pressure/memory 2>/dev/null || true
    python3 "$(dirname "${BASH_SOURCE[0]}")/docs-process-resources.py" || echo 'Process snapshot failed; continuing monitoring.'
  fi
}

if [[ "${1:-}" == '--once' ]]; then
  snapshot
else
  while true; do
    snapshot
    sleep "${DOCS_MONITOR_INTERVAL_SECONDS:-30}"
  done
fi
