#!/usr/bin/env python3
"""Read Linux process and cgroup limits without collecting command arguments."""

from pathlib import Path
import re


def read(path):
    try:
        return path.read_text()
    except OSError:
        # Processes and their cgroups can disappear during a sample.
        return None


def unescape_mount(value):
    return re.sub(r"\\([0-7]{3})", lambda m: chr(int(m[1], 8)), value)


def mounts():
    for line in (read(Path("/proc/self/mountinfo")) or "").splitlines():
        before, after = line.split(" - ", 1)
        fields, fs = before.split(), after.split()
        if fs[0] in {"cgroup", "cgroup2"}:
            yield (
                Path(unescape_mount(fields[3])),
                Path(unescape_mount(fields[4])),
                fs[0],
                set(fs[2].split(",")),
            )


CGROUP_METRICS = (
    "memory.current", "memory.peak", "memory.min", "memory.low", "memory.high",
    "memory.max", "memory.events", "memory.events.local", "memory.pressure",
    "memory.swap.current", "memory.swap.peak", "memory.swap.max",
    "pids.current", "pids.peak", "pids.max", "pids.events",
    # cgroup v1 runners use different filenames.
    "memory.usage_in_bytes", "memory.max_usage_in_bytes", "memory.limit_in_bytes",
    "memory.failcnt", "memory.oom_control", "memory.memsw.usage_in_bytes",
    "memory.memsw.limit_in_bytes", "memory.memsw.failcnt",
)


def cgroups(pid, seen):
    membership = read(Path(f"/proc/{pid}/cgroup"))
    print(f"PID {pid} cgroup membership:\n{membership or 'unavailable'}", end="\n")
    found = False
    for line in (membership or "").splitlines():
        _, controllers, name = line.split(":", 2)
        for root, mount, kind, options in mounts():
            if kind == "cgroup2":
                if controllers:
                    continue
            elif not (set(controllers.split(",")) & options & {"memory", "pids"}):
                continue
            try:
                relative = Path(name).relative_to(root)
            except ValueError:
                # A cgroup namespace can expose paths relative to its root.
                relative = Path(name.lstrip("/"))
            directory = (mount / relative).resolve()
            mount = mount.resolve()
            if not directory.is_relative_to(mount) or not directory.is_dir():
                print(f"Cannot resolve cgroup {name!r} under mount {mount}")
                continue
            # Parent limits also apply; the root alone may have no controller files.
            while True:
                if directory in seen:
                    found = True
                else:
                    seen.add(directory)
                    for metric in CGROUP_METRICS:
                        value = read(directory / metric)
                        if value is not None:
                            found = True
                            print(f"{directory / metric}: {value.strip()}")
                if directory == mount:
                    break
                directory = directory.parent
    if not found:
        print(f"No readable memory/pids cgroup metrics for PID {pid}")


def main():
    seen = set()
    cgroups("self", seen)
    for process in sorted(Path("/proc").iterdir()):
        if not process.name.isdecimal():
            continue
        name = read(process / "comm")
        if name is None or name.strip() not in {"lake", "lean", "doc-gen4"}:
            continue
        print(f"--- PID {process.name}: {name.strip()} ---")
        status = read(process / "status")
        for line in (status or "").splitlines():
            if line.startswith(("Name:", "Pid:", "PPid:", "Threads:", "FDSize:", "Vm", "Rss")):
                print(line)
        print(read(process / "limits") or "Process limits unavailable")
        try:
            with (process / "maps").open() as mappings:
                print(f"Memory mappings: {sum(1 for _ in mappings)}")
        except OSError as error:
            print(f"Memory mapping count unavailable: {error}")
        cgroups(process.name, seen)


if __name__ == "__main__":
    main()
