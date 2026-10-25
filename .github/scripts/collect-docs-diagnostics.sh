#!/usr/bin/env bash
set -euo pipefail

phase=${1:?Expected before or after}
case "$phase" in
  before|after) ;;
  *) echo 'Expected before or after' >&2; exit 2 ;;
esac
diagnostics_dir="$RUNNER_TEMP/docs-runner-diagnostics"
mkdir -p "$diagnostics_dir"

# Diagnostic commands can be unavailable on a particular runner. Keep their
# errors in the artifact without replacing the original build failure.
record() {
  printf '\n$ %s\n' "$*"
  "$@" || printf 'Unavailable (exit %s)\n' "$?"
}

{
  record date -u
  record uname -a
  record strace --version
  record bash -c 'ulimit -a'
  record cat /proc/self/limits /proc/self/cgroup /proc/self/mountinfo
  record cat /proc/meminfo /proc/pressure/memory /proc/pressure/cpu /proc/pressure/io
  for setting in vm.overcommit_memory vm.overcommit_ratio vm.overcommit_kbytes \
    vm.max_map_count kernel.threads-max kernel.pid_max; do
    record sysctl "$setting"
  done
  record python3 "$(dirname "${BASH_SOURCE[0]}")/docs-process-resources.py"
} > "$diagnostics_dir/system-$phase.log" 2>&1

# Keep the log owned by the runner; only reading the kernel buffer needs sudo.
# shellcheck disable=SC2024
if ! sudo -n dmesg --ctime > "$diagnostics_dir/kernel-$phase.log" 2>&1; then
  echo "::warning::Kernel log unavailable; see kernel-$phase.log for the error."
fi
