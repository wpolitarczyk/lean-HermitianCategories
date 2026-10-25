# Documentation runner diagnostics

After pushing the diagnosis branch, manually run **Lean Action CI** on that
branch. The **Diagnose documentation build (no deployment)** job builds the
documentation with a cold docs cache and does not publish to GitHub Pages.

Download the `docs-runner-diagnostics` artifact after the run. It contains:

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

Tracing changes execution timing, so this is not a performance benchmark. The
wrapper preserves the build's exit status, and the workflow attempts to collect
and upload diagnostics even when the build fails. A terminated runner cannot
guarantee an artifact upload. The production job keeps its 30-second sampling
interval and does not use syscall tracing.
