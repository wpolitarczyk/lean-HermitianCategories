#!/usr/bin/env bash
set -euo pipefail

mode=${1:?Expected enable or restore}
case "$mode" in
  enable|restore) ;;
  *) echo 'Expected enable or restore' >&2; exit 2 ;;
esac

diagnostics_dir="${RUNNER_TEMP:?}/docs-runner-diagnostics"
mkdir -p "$diagnostics_dir"
original_file="$diagnostics_dir/overcommit-original.txt"
log_file="$diagnostics_dir/overcommit.log"

log() {
  printf '%s %s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')" "$*" | tee -a "$log_file"
}

validate_policy() {
  case "$1" in
    0|1|2) ;;
    *) log "::error::Unexpected overcommit policy: $1"; return 1 ;;
  esac
}

if [[ "$mode" == enable ]]; then
  # Save before changing anything, and retain the first value if retried.
  if [[ ! -f "$original_file" ]]; then
    original=$(sysctl -n vm.overcommit_memory)
    validate_policy "$original"
    printf '%s\n' "$original" > "$original_file"
  fi
  original=$(cat "$original_file")
  validate_policy "$original"
  target=1
  log "Original vm.overcommit_memory=$original; enabling diagnostic policy $target"
else
  if [[ ! -f "$original_file" ]]; then
    log 'No saved overcommit policy; setup did not change it. Nothing to restore.'
    exit 0
  fi
  target=$(cat "$original_file")
  validate_policy "$target"
  log "Restoring vm.overcommit_memory=$target"
fi

sudo -n sysctl -w "vm.overcommit_memory=$target" 2>&1 | tee -a "$log_file"
actual=$(sysctl -n vm.overcommit_memory)
if [[ "$actual" != "$target" ]]; then
  log "::error::Expected vm.overcommit_memory=$target, got $actual"
  exit 1
fi
log "Verified vm.overcommit_memory=$actual"
