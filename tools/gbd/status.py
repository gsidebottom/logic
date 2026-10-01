#!/usr/bin/env python3
"""What each worker of a running `run_benchmark.py` is doing, from the
outside -- the TUI's worker lines, for a run whose stderr is a file.

Each worker is a `sat` process (found by its `--proof .../pbproof-<hash>.pbp`
argument); its container, if any, says whether it is in the solve phase or
the dsr-trim verify phase, and `docker top` says which of satsuma, kissat or
dsr-trim is running inside; the hydra stages and the circuit stage run inside
the sat process and show as "in-process".  Elapsed times come from `ps`.

    tools/gbd/status.py                       # the running benchmark
    tools/gbd/status.py --prev doc/competition-benchmark_<...>.json
                                              # with the previous run's result per instance

The index and the worker count are read from the running run_benchmark.py's
command line (--index, -j) unless given.
"""
import argparse
import json
import re
import subprocess
import time
from pathlib import Path


def sh(*cmd: str) -> str:
    return subprocess.run(cmd, capture_output=True, text=True).stdout


def etime_s(s: str) -> int:
    """`ps` etime ([[dd-]hh:]mm:ss) in seconds."""
    days = 0
    if "-" in s:
        d, s = s.split("-")
        days = int(d)
    parts = [int(x) for x in s.split(":")]
    while len(parts) < 3:
        parts.insert(0, 0)
    return days * 86400 + parts[0] * 3600 + parts[1] * 60 + parts[2]


def fmt(sec) -> str:
    if sec is None:
        return ""
    sec = int(sec)
    if sec >= 3600:
        return f"{sec // 3600}:{sec % 3600 // 60:02d}:{sec % 60:02d}"
    return f"{sec // 60}:{sec % 60:02d}"


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--index", type=Path, default=None,
                    help="the index the run uses (default: from the running run_benchmark.py)")
    ap.add_argument("--prev", type=Path, default=None,
                    help="a previous report's .json, for a column with that run's result per instance")
    ap.add_argument("-j", "--parallel", type=int, default=None,
                    help="the run's worker count (default: from the running run_benchmark.py, else 10)")
    args = ap.parse_args()

    ps = sh("ps", "-axo", "pid,ppid,etime,command")

    runner = re.search(r"run_benchmark\.py (.*)$", ps, re.M)
    runner_args = runner.group(1) if runner else ""
    if args.index is None:
        m = re.search(r"--index\s+(\S+)", runner_args)
        args.index = Path(m.group(1)) if m else Path("/Users/greg/projects/sat_benchmarks/main_track_2026_official.jsonl")
    if args.parallel is None:
        m = re.search(r"(?:-j|--parallel)\s+(\d+)", runner_args)
        args.parallel = int(m.group(1)) if m else 10

    by_hash = {}
    if args.index.exists():
        for line in open(args.index):
            if line.strip():
                r = json.loads(line)
                by_hash[r["hash"]] = r
    prev = {}
    if args.prev and args.prev.exists():
        prev = {r["hash"]: r for r in json.load(open(args.prev))["results"]}

    # the sat processes: pid, elapsed, backend, instance hash
    sats = {}
    for m in re.finditer(r"^\s*(\d+)\s+(\d+)\s+(\S+)\s+\S*release/sat -b (\S+).*?pbproof-([0-9a-f]+)\.pbp", ps, re.M):
        sats[int(m.group(1))] = dict(elapsed=etime_s(m.group(3)), backend=m.group(4), hash=m.group(5))
    # the docker client under each sat process, carrying its work dir
    clients = {}
    for m in re.finditer(r"^\s*(\d+)\s+(\d+)\s+(\S+)\s+docker run .*?pbsatsuma-(\d+):/work", ps, re.M):
        clients[int(m.group(4))] = dict(elapsed=etime_s(m.group(3)))
    # the containers, the main process inside each, and the sat pid each belongs to
    containers = {}
    for line in sh("docker", "ps", "--format", "{{.Names}}\t{{.Command}}").splitlines():
        name, cmd = line.split("\t", 1)
        procs = [l.split() for l in sh("docker", "top", name, "-o", "pid,etime,comm").splitlines()[1:]]
        inside = next((p[-1] for p in procs if p and p[-1] in ("satsuma", "kissat", "dsr-trim")), None)
        containers[name] = dict(cmd=cmd, inside=inside)
    container_of = {}
    if containers:
        for c in json.loads(sh("docker", "inspect", *containers)):
            for mnt in c.get("Mounts", []):
                m = re.search(r"pbsatsuma-(\d+)$", mnt.get("Source", ""))
                if m:
                    container_of[int(m.group(1))] = c["Name"].lstrip("/")
    decompressing = len(re.findall(r"xz -d -k -c", ps))

    rows = []
    for pid, s in sorted(sats.items(), key=lambda kv: -kv[1]["elapsed"]):
        rec = by_hash.get(s["hash"], {})
        name = rec.get("filename", s["hash"]).replace(".cnf.xz", "")
        phase, phase_elapsed = "in-process (hydra stages, circuit stage)", None
        cname = container_of.get(pid)
        if cname in containers:
            c = containers[cname]
            phase_elapsed = clients.get(pid, {}).get("elapsed")
            if "dsr-trim" in c["cmd"] or c["inside"] == "dsr-trim":
                phase = "verify: dsr-trim on the composed proof"
            elif c["inside"]:
                phase = f"solve: {c['inside']} in the container"
            else:
                phase = "solve: container starting"
        p = prev.get(s["hash"])
        prv = f"{p.get('result', '?')} {p.get('time_s', 0):.0f}s" if p else ""
        rows.append((name, rec.get("family", "?"), phase, s["elapsed"], phase_elapsed, prv))

    idle = max(0, args.parallel - len(rows) - decompressing)
    print(f"{time.strftime('%H:%M:%S')}  {len(rows)} solving, {decompressing} decompressing, "
          f"{idle} waiting for memory or between instances (of {args.parallel} workers)")
    # running = the worker's whole time on the instance; phase = the current
    # container's; solve = the verdict's time once the check has begun (the
    # verify container starts at the verdict), which is what a report records.
    print(f"{'instance':44s} {'family':22s} {'phase':40s} {'running':>8s} {'phase':>7s} {'solve':>7s}"
          + ("  previous solve" if prev else ""))
    for name, fam, phase, el, ph_el, prv in rows:
        solve = el - ph_el if (phase.startswith("verify") and ph_el is not None) else None
        print(f"{name[:44]:44s} {fam[:22]:22s} {phase[:40]:40s} {fmt(el):>8s} {fmt(ph_el):>7s} {fmt(solve):>7s}  {prv}")


if __name__ == "__main__":
    main()
