#!/usr/bin/env bash
set -euo pipefail

diagnostics_dir="$RUNNER_TEMP/docs-runner-diagnostics"
mkdir -p "$diagnostics_dir"
command -v strace > /dev/null

# Match docgen-action's isolated docbuild package and toolchain-matched doc-gen4
# dependency, but only build the API documentation: no Pages upload or deploy.
# Use a cold documentation cache to reproduce the failing run's workload.
toolchain=$(cat lean-toolchain)
mkdir -p docbuild
cat > docbuild/lakefile.toml <<EOF
name = "docbuild"
reservoir = false
version = "0.1.0"
packagesDir = "../.lake/packages"

[[require]]
name = "HermitianCategories"
path = "../"

[[require]]
scope = "leanprover"
name = "doc-gen4"
rev = "${toolchain##*:}"
EOF

cd docbuild
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update HermitianCategories

# Follow child processes and threads. Only log failed process/memory/pipe
# syscalls, with timestamps and process names, to keep the trace manageable.
# Tracing changes timing; this run diagnoses failures, not build performance.
set +e
strace -f -qq -tt -T -Y -e trace=%process,%memory,pipe,pipe2,dup,dup2,dup3 \
  -e status=failed -e signal=none -o "$diagnostics_dir/syscall-failures.log" \
  lake build HermitianCategories:docs 2>&1 | tee "$diagnostics_dir/build.log"
statuses=("${PIPESTATUS[@]}")
set -e
printf '%s\n' "${statuses[0]}" > "$diagnostics_dir/build-exit-code.txt"
if ((statuses[0] != 0)); then
  exit "${statuses[0]}"
fi
exit "${statuses[1]}"
