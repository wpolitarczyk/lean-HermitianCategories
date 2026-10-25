#!/usr/bin/env bash
set -euo pipefail

snapshot() {
  date -u '+%Y-%m-%dT%H:%M:%SZ'
  free -m
  swapon --show
  df -h "$GITHUB_WORKSPACE" "$RUNNER_TEMP"
  echo 'Largest processes by resident memory (RSS in KiB)'
  # Use process names rather than command lines to avoid logging arguments.
  ps -eo pid,ppid,comm,rss,%mem,%cpu --sort=-rss | sed -n '1,16p'
  for metric in memory.current memory.peak memory.max memory.events; do
    if [[ -r "/sys/fs/cgroup/$metric" ]]; then
      echo "cgroup $metric"
      cat "/sys/fs/cgroup/$metric"
    fi
  done
}

if [[ "${1:-}" == '--once' ]]; then
  snapshot
else
  while true; do
    snapshot
    sleep 30
  done
fi
