# Documentation runner diagnostics

After pushing the diagnosis branch, manually run **Lean Action CI** on that
branch. The **Diagnose documentation build (no deployment)** job builds the
documentation with a cold docs cache and does not publish to GitHub Pages.

Both the production and manual jobs set `vm.overcommit_memory=1` to avoid the
heuristic rejection of Lake's large virtual-memory commitment when forking Git
subprocesses. Each job saves the original setting, verifies the change, and
attempts to restore it after docgen finishes even if it fails. Swap remains
enabled in both jobs; syscall tracing is used only in the manual job.

The production job builds and deploys on pushes to `master`. Its
`docs-runner-diagnostics` artifact contains the lightweight 30-second resource
samples, `overcommit.log`, and `overcommit-original.txt`.

The manual job's `docs-runner-diagnostics` artifact contains:

- `build.log` and `build-exit-code.txt`: docgen/Lake output and its exit status.
- `syscall-failures.log`: failed process, memory, pipe, and descriptor-duplication
  system calls from Lake and its children, with timestamps, PIDs, and process
  names. Look for `ENOMEM` or `EAGAIN` near the build failure. Some failures,
  such as PATH lookups returning `ENOENT` or feature probes returning `ENOSYS`,
  are normal and are not by themselves evidence of the cause.
- `resource-usage.log`: five-second samples of RAM, swap, memory commitments,
  process RSS/virtual memory/thread counts, process limits and mapping counts,
  and cgroup memory/process limits and events. Both cgroup v1 and v2 are
  supported; visible ancestor limits are included. Unavailable data is reported.
- `system-before.log` and `system-after.log`: kernel version, overcommit and
  mapping settings, limits, cgroup membership/mounts, and memory pressure.
- `kernel-before.log` and `kernel-after.log`: kernel messages, or the reason
  they could not be read.
- `overcommit-original.txt` and `overcommit.log`: original policy, verified
  diagnostic setting, and restoration result. `system-before.log` is captured
  before enabling overcommit; `system-after.log` is captured before restoring it.

Tracing changes execution timing, so this is not a performance benchmark. The
wrapper preserves the build's exit status, and the workflow attempts to collect
and upload diagnostics even when the build fails. A terminated runner cannot
guarantee an artifact upload. The production job keeps its 30-second sampling
interval and does not use syscall tracing.
