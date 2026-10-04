#!/usr/bin/env python3
"""Two (or more) solvers through one benchmark set, side by side, on a number
of cores you can change, with a pause that gives the machine back.

Every instance of the index is solved by every backend, in the index's order,
the backends of one instance launched one after the other so they mostly run
at the same time, under the same conditions.  At any moment `status` scores
the instances every backend has finished: solved, PAR-2, the instances only
one of them solved, the time ratio.

    tools/gbd/duo.py start --index I.jsonl --dir RUN [--cores 8] [--no-verify]
    tools/gbd/duo.py status [--dir RUN] [--running]
    tools/gbd/duo.py cores N [--now]       # --now: stop the newest jobs above N
    tools/gbd/duo.py pause [--drain]       # default: stop the running jobs now
    tools/gbd/duo.py resume
    tools/gbd/duo.py stop                  # end the scheduler; `start --dir RUN` resumes

Timing is the solver's own wall clock, so a job is never suspended: pausing
(or `cores N --now`, or `stop`) kills the running jobs, their containers and
their temporary files, and puts them back at the front of the queue, to be
run again from the start.  A job that finishes is appended to results.jsonl
and never run again; restarting the scheduler (after `stop`, a crash or a
reboot) carries on from there.  `pause --drain` instead lets the running jobs
finish and starts no new ones.

Memory: instances are admitted by the estimates of run_benchmark.py
(`mem_estimate`, `--mem-budget-vm`, `--mem-budget-host`), first in, first
out, one at a time when nothing else fits.  Disk: launches hold while the
volume holding /tmp has less than --disk-brake-gb free.  Instances not yet on
disk (a download still running) are skipped and picked up when they arrive.
While jobs run, `caffeinate -i` keeps the machine from idle-sleeping.

RUN holds config.json (fixed at start), control.json (what the commands
change), results.jsonl, running.json, events.log, logs/ (each job's stderr)
and work/ (decompressed instances, deleted when all backends are done).
The last RUN started is remembered in ~/.duo_current, so --dir can be left
out afterwards.
"""
import argparse
import datetime as dt
import json
import math
import os
import re
import shutil
import signal
import subprocess
import sys
import time
from pathlib import Path
from typing import Dict, List, Optional, Tuple

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
SAT_BIN = REPO / "target" / "release" / "sat"
CURRENT = Path.home() / ".duo_current"
sys.path.insert(0, str(HERE))
import run_benchmark as rb  # noqa: E402  (parse_sat_output, _parse_time_cell, mem_estimate)

DOCKER = ("satsuma", "hydra_satsuma", "hydra_circuit_satsuma")


# --------------------------------------------------------------------------
# small file helpers
# --------------------------------------------------------------------------
def now_iso() -> str:
    return dt.datetime.now().isoformat(timespec="seconds")


def read_json(p: Path, default):
    try:
        return json.loads(p.read_text())
    except (OSError, ValueError):
        return default


def write_json(p: Path, obj) -> None:
    tmp = p.with_suffix(p.suffix + ".tmp")
    tmp.write_text(json.dumps(obj, indent=1))
    os.replace(tmp, p)


def log_event(run: Path, msg: str) -> None:
    with open(run / "events.log", "a") as f:
        f.write(f"{now_iso()} {msg}\n")


def fmt_dur(sec: float) -> str:
    sec = int(sec)
    d, r = divmod(sec, 86400)
    h, r = divmod(r, 3600)
    m, s = divmod(r, 60)
    if d:
        return f"{d}d {h}h {m:02d}m"
    if h:
        return f"{h}:{m:02d}:{s:02d}"
    return f"{m}:{s:02d}"


def run_dir(arg: Optional[str]) -> Path:
    if arg:
        return Path(arg).resolve()
    if CURRENT.exists():
        return Path(CURRENT.read_text().strip())
    sys.exit("no run directory: give --dir (none remembered in ~/.duo_current)")


def disk_free_gb(path: str = "/tmp") -> float:
    st = os.statvfs(path)
    return st.f_bavail * st.f_frsize / 2**30


def find_xz(rec: dict) -> Optional[Path]:
    p = Path(rec.get("xz_path", ""))
    if p.exists():
        return p
    d = Path(rec.get("bench_dir") or (p.parent if str(p) else "."))
    hits = sorted(d.glob(f"{rec['hash']}-*.cnf.xz"))
    return hits[0] if hits else None


# --------------------------------------------------------------------------
# killing a job: its process group, its containers, its temporary files
# --------------------------------------------------------------------------
def containers_by_pid() -> Dict[int, List[str]]:
    """sat pid -> ids of the containers mounting its /tmp/pbsatsuma-<pid>."""
    out: Dict[int, List[str]] = {}
    ids = subprocess.run(["docker", "ps", "-q"], capture_output=True, text=True).stdout.split()
    if not ids:
        return out
    try:
        info = json.loads(subprocess.run(["docker", "inspect", *ids], capture_output=True, text=True).stdout)
    except ValueError:
        return out
    for c in info:
        for m in c.get("Mounts", []):
            mm = re.search(r"pbsatsuma-(\d+)$", m.get("Source", ""))
            if mm:
                out.setdefault(int(mm.group(1)), []).append(c["Id"][:12])
    return out


def cleanup_tmp(pid: int, proof: Optional[Path]) -> None:
    for d in (Path(f"/tmp/pbsatsuma-{pid}"), Path(f"/tmp/pbcircuit-{pid}")):
        shutil.rmtree(d, ignore_errors=True)
    if proof is not None:
        try:
            proof.unlink()
        except OSError:
            pass


def proc_command(pid: int) -> Optional[str]:
    """The command line of a live process, None if there is none."""
    out = subprocess.run(["ps", "-o", "command=", "-p", str(pid)], capture_output=True, text=True).stdout.strip()
    return out or None


def kill_job_procs(pid: int, proof: Optional[Path]) -> None:
    """Kill one of our jobs: only if the process is ours (its command line
    names our proof file; a PID can be reused after a reboot), with its
    process group and containers; then its temporary files, which no live
    process can own once the PID is free."""
    cmd = proc_command(pid)
    if cmd is not None and (proof is None or str(proof) not in cmd):
        return                                   # someone else's process now
    if cmd is not None:
        try:
            os.killpg(pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            pass
    # the container outlives its docker client; ours, or orphaned once the PID is free
    cids = containers_by_pid().get(pid, [])
    if cids:
        subprocess.run(["docker", "kill", *cids], capture_output=True)
    cleanup_tmp(pid, proof)


# --------------------------------------------------------------------------
# reading a finished job's output
# --------------------------------------------------------------------------
def read_outcome(stderr: str, stdout: str) -> dict:
    result, time_str, _ = rb.parse_sat_output(stderr)
    if result == "UNKNOWN":
        if re.search(r"^s SATISFIABLE\b", stdout, re.M):
            result = "SAT"
        elif re.search(r"^s UNSATISFIABLE\b", stdout, re.M):
            result = "UNSAT"
    m = re.search(r"prover=(\S+)", stderr)
    prover = m.group(1) if m else None
    check, check_s = None, None
    if result == "UNSAT":
        if re.search(r"(dsr|drat)-trim VERIFIED UNSAT", stderr):
            check = "verified"
        elif "verification skipped (--no-verify)" in stderr:
            check = "skipped"
        elif re.search(r"(dsr|drat)-trim verification TIMEOUT", stderr):
            check = "timeout"
        elif re.search(r"(dsr|drat)-trim did NOT verify", stderr):
            check = "rejected"
        elif "UNSAT of GE residual" in stderr:
            check = "residual only"
        elif prover in ("cook", "xor"):
            check = "veripb (not run here)"
        else:
            check = "no marker"
        m = re.search(r"(?:dsr|drat)-trim verify ([0-9.]+)s total", stderr)
        check_s = float(m.group(1)) if m else None
    return dict(result=result, time_s=rb._parse_time_cell(time_str), prover=prover,
                check=check, check_s=check_s)


# --------------------------------------------------------------------------
# the scheduler
# --------------------------------------------------------------------------
class Job:
    def __init__(self, h: str, backend: str, order: int):
        self.h, self.backend, self.order = h, backend, order
        self.proc: Optional[subprocess.Popen] = None
        self.state = "waiting"          # decompress | solve
        self.started = 0.0
        self.mem = (0.0, 0.0)
        self.proof: Optional[Path] = None
        self.err: Optional[Path] = None
        self.out: Optional[Path] = None

    def key(self) -> Tuple[str, str]:
        return (self.h, self.backend)


class Scheduler:
    def __init__(self, run: Path):
        self.run = run
        self.cfg = read_json(run / "config.json", None)
        if self.cfg is None:
            sys.exit(f"{run}: no config.json")
        self.recs: Dict[str, dict] = self.cfg["records"]
        self.backends: List[str] = self.cfg["backends"]
        (run / "logs").mkdir(exist_ok=True)
        (run / "work").mkdir(exist_ok=True)
        done = set()
        for line in open(run / "results.jsonl") if (run / "results.jsonl").exists() else []:
            try:
                r = json.loads(line)
                done.add((r["hash"], r["backend"]))
            except (ValueError, KeyError):
                pass
        self.queue: List[Job] = []
        for i, h in enumerate(self.cfg["order"]):
            for b in self.backends:
                if (h, b) not in done:
                    self.queue.append(Job(h, b, i))
        self.running: List[Job] = []
        self.unzip: Dict[str, subprocess.Popen] = {}   # hash -> xz process
        self.used_vm = self.used_host = 0.0
        self.caffeinate: Optional[subprocess.Popen] = None
        self.state = read_json(run / "state.json", {"active_s": 0.0})
        self.last_tick = time.time()
        # leftovers of a previous scheduler that died: kill them
        for r in read_json(run / "running.json", []):
            if r.get("pid"):
                kill_job_procs(int(r["pid"]), Path(r["proof"]) if r.get("proof") else None)
        write_json(run / "running.json", [])
        for f in (run / "work").glob("*.part"):
            f.unlink(missing_ok=True)

    # ---- control
    def control(self) -> dict:
        c = read_json(self.run / "control.json", {})
        c.setdefault("cores", self.cfg.get("cores", 8))
        c.setdefault("paused", False)
        c.setdefault("drain", False)
        c.setdefault("stop", False)
        c.setdefault("now", False)
        c.setdefault("mem_budget_vm", self.cfg.get("mem_budget_vm", 26.0))
        c.setdefault("mem_budget_host", self.cfg.get("mem_budget_host", 20.0))
        return c

    # ---- instances on disk
    def cnf_path(self, h: str) -> Path:
        return self.run / "work" / f"{h}.cnf"

    def instance_needed(self, h: str) -> bool:
        return any(j.h == h for j in self.queue) or any(j.h == h for j in self.running)

    def drop_instance_if_done(self, h: str) -> None:
        if not self.instance_needed(h):
            self.cnf_path(h).unlink(missing_ok=True)

    # ---- launching
    def start_unzip(self, h: str) -> bool:
        """True when the instance is decompressed; else start (or keep) its xz."""
        if self.cnf_path(h).exists():
            return True
        if h in self.unzip:
            p = self.unzip[h]
            if p.poll() is None:
                return False
            del self.unzip[h]
            part = self.cnf_path(h).with_suffix(".cnf.part")
            if p.returncode == 0 and part.exists():
                os.replace(part, self.cnf_path(h))
                return True
            part.unlink(missing_ok=True)
            log_event(self.run, f"xz failed on {h} (rc {p.returncode}); will retry")
            return False
        xz = find_xz(self.recs[h])
        if xz is None:
            return False
        part = self.cnf_path(h).with_suffix(".cnf.part")
        self.unzip[h] = subprocess.Popen(["xz", "-dc", str(xz)], stdout=open(part, "wb"),
                                         stderr=subprocess.DEVNULL)
        return False

    def launch_sat(self, j: Job) -> None:
        rec = self.recs[j.h]
        tag = f"{j.h}.{j.backend}"
        j.err = self.run / "logs" / f"{tag}.err"
        j.out = self.run / "logs" / f"{tag}.out"
        j.proof = Path(f"/tmp/pbproof-{j.h}-{j.backend}.pbp")
        cmd = [str(SAT_BIN), "-b", j.backend, "-t", str(self.cfg["timeout"]), "--proof", str(j.proof)]
        if not self.cfg.get("verify", True):
            cmd.append("--no-verify")
        cmd += self.cfg.get("sat_args", [])
        j.proc = subprocess.Popen(cmd, stdin=open(self.cnf_path(j.h), "rb"),
                                  stdout=open(j.out, "w"), stderr=open(j.err, "w"),
                                  start_new_session=True)
        j.state = "solve"
        j.started = time.time()
        log_event(self.run, f"start {rec['name']} {j.backend} pid {j.proc.pid}")

    def try_launch(self, c: dict) -> None:
        if c["paused"] or c["stop"]:
            return
        if disk_free_gb() < self.cfg.get("disk_brake_gb", 50):
            return
        while len(self.running) < c["cores"] and self.queue:
            # first queued job whose instance is on disk (or being unpacked)
            pick = None
            for j in self.queue:
                if j.h in self.unzip or self.cnf_path(j.h).exists() or find_xz(self.recs[j.h]) is not None:
                    pick = j
                    break
            if pick is None:
                return
            vm, host = rb.mem_estimate(self.recs[pick.h])
            if self.running and (self.used_vm + vm > c["mem_budget_vm"]
                                 or self.used_host + host > c["mem_budget_host"]):
                return                                   # first in, first out
            self.queue.remove(pick)
            pick.mem = (vm, host)
            self.used_vm += vm
            self.used_host += host
            pick.state = "decompress"
            pick.started = time.time()
            self.running.append(pick)
            if self.start_unzip(pick.h):
                self.launch_sat(pick)

    # ---- finishing
    def release(self, j: Job) -> None:
        self.running.remove(j)
        self.used_vm -= j.mem[0]
        self.used_host -= j.mem[1]

    def requeue(self, j: Job, why: str) -> None:
        if j.proc is not None and j.proc.poll() is None:
            kill_job_procs(j.proc.pid, j.proof)
            try:
                j.proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                pass
        elif j.proc is not None:
            cleanup_tmp(j.proc.pid, j.proof)
        self.release(j)
        j.proc, j.state = None, "waiting"
        self.queue.append(j)
        self.queue.sort(key=lambda x: (x.order, self.backends.index(x.backend)))
        log_event(self.run, f"requeue {self.recs[j.h]['name']} {j.backend} ({why})")

    def reap(self) -> None:
        for j in list(self.running):
            if j.state == "decompress":
                if self.start_unzip(j.h):
                    self.launch_sat(j)
                continue
            if j.proc.poll() is None:
                continue
            rc = j.proc.returncode
            stderr = j.err.read_text(errors="replace") if j.err.exists() else ""
            stdout = j.out.read_text(errors="replace") if j.out.exists() else ""
            o = read_outcome(stderr, stdout)
            cleanup_tmp(j.proc.pid, j.proof)
            j.out.unlink(missing_ok=True)       # the model; the verdict is in the record
            rec = self.recs[j.h]
            if o["result"] in ("UNKNOWN", "INTERRUPTED") and rc != 0:
                o["result"] = "ERROR"
            expected = (rec.get("status") or "").upper()
            row = dict(hash=j.h, name=rec["name"], family=rec.get("family"), backend=j.backend,
                       **o, rc=rc, expected=expected or None,
                       mismatch=bool(expected in ("SAT", "UNSAT") and o["result"] in ("SAT", "UNSAT")
                                     and o["result"] != expected),
                       started=dt.datetime.fromtimestamp(j.started).isoformat(timespec="seconds"),
                       finished=now_iso(), wall_s=round(time.time() - j.started, 1),
                       cores=self.control()["cores"])
            with open(self.run / "results.jsonl", "a") as f:
                f.write(json.dumps(row) + "\n")
            log_event(self.run, f"done {rec['name']} {j.backend} {o['result']} {o['time_s']}"
                                + (" MISMATCH" if row["mismatch"] else ""))
            self.release(j)
            self.drop_instance_if_done(j.h)

    # ---- bookkeeping for status
    def publish(self, c: dict) -> None:
        write_json(self.run / "running.json", [
            dict(hash=j.h, name=self.recs[j.h]["name"], backend=j.backend, state=j.state,
                 pid=(j.proc.pid if j.proc else None), started=j.started,
                 proof=(str(j.proof) if j.proof else None), mem=j.mem)
            for j in self.running])
        t = time.time()
        if self.running and not c["paused"]:
            self.state["active_s"] = self.state.get("active_s", 0.0) + (t - self.last_tick)
        self.last_tick = t
        self.state.update(pid=os.getpid(), heartbeat=t, queued=len(self.queue),
                          used_vm=round(self.used_vm, 1), used_host=round(self.used_host, 1))
        write_json(self.run / "state.json", self.state)

    def keep_awake(self, on: bool) -> None:
        if on and (self.caffeinate is None or self.caffeinate.poll() is not None):
            self.caffeinate = subprocess.Popen(["caffeinate", "-i", "-w", str(os.getpid())])
        elif not on and self.caffeinate is not None:
            self.caffeinate.terminate()
            self.caffeinate = None

    def loop(self) -> None:
        log_event(self.run, f"scheduler up, pid {os.getpid()}, {len(self.queue)} jobs queued")
        was_paused = None
        while True:
            c = self.control()
            if c["stop"]:
                for j in list(self.running):
                    self.requeue(j, "stop")
                for p in self.unzip.values():
                    p.kill()
                c["stop"] = False
                write_json(self.run / "control.json", c)
                self.publish(c)
                self.keep_awake(False)
                log_event(self.run, "scheduler stopped")
                return
            if c["paused"] != was_paused:
                log_event(self.run, "paused" + (" (drain)" if c["drain"] else "") if c["paused"] else "resumed")
                was_paused = c["paused"]
            if c["paused"] and not c["drain"]:
                for j in list(self.running):
                    self.requeue(j, "pause")
            if c["now"] and len(self.running) > c["cores"]:
                for j in sorted(self.running, key=lambda x: -x.started)[: len(self.running) - c["cores"]]:
                    self.requeue(j, f"cores {c['cores']} --now")
            if c["now"]:
                c["now"] = False
                write_json(self.run / "control.json", c)
            self.reap()
            self.try_launch(c)
            self.keep_awake(bool(self.running))
            self.publish(c)
            if not self.queue and not self.running:
                log_event(self.run, "all jobs done")
                self.keep_awake(False)
                return
            time.sleep(2)


# --------------------------------------------------------------------------
# status: scoring the instances every backend has finished
# --------------------------------------------------------------------------
def load_results(run: Path) -> Dict[Tuple[str, str], dict]:
    res = {}
    if (run / "results.jsonl").exists():
        for line in open(run / "results.jsonl"):
            try:
                r = json.loads(line)
                res[(r["hash"], r["backend"])] = r
            except (ValueError, KeyError):
                pass
    return res


def scored(r: dict, timeout: int, certified: bool) -> Tuple[bool, float]:
    ok = r["result"] in ("SAT", "UNSAT")
    if ok and certified and r["result"] == "UNSAT" and r.get("check") != "verified":
        ok = False
    return ok, (r["time_s"] if ok and r.get("time_s") is not None else 2.0 * timeout)


def phase_of_running(running: List[dict]) -> Dict[int, str]:
    """sat pid -> what it is doing, from its container (if any)."""
    by_pid = containers_by_pid()
    out = {}
    for r in running:
        pid = r.get("pid")
        if not pid:
            continue
        cids = by_pid.get(pid)
        if not cids:
            kids = subprocess.run(["pgrep", "-P", str(pid), "-l"], capture_output=True, text=True).stdout
            out[pid] = ("verify: drat-trim" if "drat-trim" in kids
                        else "in-process (hydra / circuit stages)")
            continue
        top = subprocess.run(["docker", "top", cids[0], "-o", "pid,comm"], capture_output=True, text=True).stdout
        names = [l.split()[-1] for l in top.splitlines()[1:] if l.split()]
        if "dsr-trim" in names:
            out[pid] = "verify: dsr-trim"
        elif "kissat" in names:
            out[pid] = "solve: kissat"
        elif "satsuma" in names:
            out[pid] = "solve: satsuma"
        else:
            out[pid] = "container starting"
    return out


def cmd_status(args) -> None:
    run = run_dir(args.dir)
    cfg = read_json(run / "config.json", None)
    if cfg is None:
        sys.exit(f"{run}: no config.json")
    c = read_json(run / "control.json", {})
    st = read_json(run / "state.json", {})
    backends, timeout = cfg["backends"], cfg["timeout"]
    res = load_results(run)
    order = cfg["order"]
    alive = bool(st.get("pid")) and _pid_alive(st["pid"]) and time.time() - st.get("heartbeat", 0) < 60
    running = read_json(run / "running.json", []) if alive else []
    all_done = len(res) >= len(cfg["order"]) * len(backends)
    state = ("finished" if all_done and not alive else "stopped" if not alive
             else "paused (draining)" if c.get("paused") and c.get("drain")
             else "paused" if c.get("paused") else "running")
    both = [h for h in order if all((h, b) in res for b in backends)]
    print(f"{cfg.get('name', run.name)}: {' vs '.join(backends)}, {len(order)} instances, "
          f"{timeout} s, checks {'on' if cfg.get('verify', True) else 'off'}")
    print(f"scheduler {state}; cores {c.get('cores', cfg.get('cores'))}; {len(running)} jobs running; "
          f"active {fmt_dur(st.get('active_s', 0))} since {cfg['created'][:16].replace('T', ' ')}; "
          f"memory in use {max(0.0, st.get('used_vm', 0)):.1f}/{c.get('mem_budget_vm', cfg.get('mem_budget_vm'))} GB VM, "
          f"{max(0.0, st.get('used_host', 0)):.1f}/{c.get('mem_budget_host', cfg.get('mem_budget_host'))} GB host")
    per = {b: sum(1 for (h, bb) in res if bb == b) for b in backends}
    missing = sum(1 for h in order if find_xz(cfg["records"][h]) is None)
    print(f"done by both: {len(both)} of {len(order)} ({100 * len(both) / max(1, len(order)):.1f}%); "
          + ", ".join(f"{b} {n}" for b, n in per.items())
          + (f"; {missing} instances not on disk yet" if missing else ""))
    if both:
        n = len(both)
        print(f"\non the {n} done by both" + (" (PAR-2 certified: unchecked UNSATs count as unsolved)" if cfg.get("verify", True) else "") + ":")
        print(f"  {'backend':24s} {'solved':>6s} {'SAT':>5s} {'UNSAT':>5s} {'timeout':>7s} {'other':>5s} "
              f"{'PAR-2':>8s} {'only it':>7s}" + (f" {'cert PAR-2':>10s} {'unchecked':>9s}" if cfg.get('verify', True) else ""))
        solved = {b: {h for h in both if res[(h, b)]["result"] in ("SAT", "UNSAT")} for b in backends}
        for b in backends:
            rows = [res[(h, b)] for h in both]
            sat = sum(r["result"] == "SAT" for r in rows)
            uns = sum(r["result"] == "UNSAT" for r in rows)
            to = sum(r["result"] == "TIMEOUT" for r in rows)
            other = n - sat - uns - to
            par2 = sum(scored(r, timeout, False)[1] for r in rows) / n
            only = len(solved[b] - set.union(*(solved[x] for x in backends if x != b))) if len(backends) > 1 else 0
            line = f"  {b:24s} {sat + uns:6d} {sat:5d} {uns:5d} {to:7d} {other:5d} {par2:8.1f} {only:7d}"
            if cfg.get("verify", True):
                cpar2 = sum(scored(r, timeout, True)[1] for r in rows) / n
                unch = sum(r["result"] == "UNSAT" and r.get("check") != "verified" for r in rows)
                line += f" {cpar2:10.1f} {unch:9d}"
            print(line)
        if len(backends) == 2:
            a, b = backends
            pairs = [(res[(h, a)]["time_s"], res[(h, b)]["time_s"]) for h in both
                     if res[(h, a)]["result"] in ("SAT", "UNSAT") and res[(h, b)]["result"] in ("SAT", "UNSAT")
                     and min(res[(h, a)]["time_s"] or 0, res[(h, b)]["time_s"] or 0) >= 5]
            if pairs:
                g = math.exp(sum(math.log(y / x) for x, y in pairs) / len(pairs))
                print(f"  time {b} / {a} on the {len(pairs)} both solved in >= 5 s: geometric mean {g:.3f}")
        mism = [r for r in res.values() if r.get("mismatch")]
        errs = [r for r in res.values() if r["result"] == "ERROR"]
        if mism:
            print(f"\n  MISMATCH with the recorded status: " + ", ".join(f"{r['name']} {r['backend']} {r['result']}" for r in mism))
        if errs:
            print(f"  errors (no verdict, nonzero exit): " + ", ".join(f"{r['name']} {r['backend']} rc {r['rc']}" for r in errs[:10]))
        act = st.get("active_s", 0)
        if act > 3600 and len(both) < len(order):
            rate = len(both) / act
            print(f"\n  pace: {3600 * rate:.1f} instances per active hour at the cores used so far; "
                  f"the remaining {len(order) - len(both)} at that pace: {fmt_dur((len(order) - len(both)) / rate)}")
    if running:
        ph = phase_of_running(running)
        t = time.time()
        print(f"\nrunning:")
        for r in sorted(running, key=lambda r: r["started"]):
            what = "decompressing" if r["state"] == "decompress" else ph.get(r["pid"], "?")
            print(f"  {r['name'][:44]:44s} {r['backend'][:22]:22s} {what:34s} {fmt_dur(t - r['started']):>9s}")


def _pid_alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
        return True
    except (ProcessLookupError, PermissionError):
        return False


# --------------------------------------------------------------------------
# commands
# --------------------------------------------------------------------------
def set_control(run: Path, **kv) -> dict:
    c = read_json(run / "control.json", {})
    c.update(kv)
    write_json(run / "control.json", c)
    return c


def scheduler_pid(run: Path) -> Optional[int]:
    st = read_json(run / "state.json", {})
    pid = st.get("pid")
    if pid and _pid_alive(pid) and time.time() - st.get("heartbeat", 0) < 60:
        return pid
    return None


def cmd_start(args) -> None:
    run = Path(args.dir).resolve()
    run.mkdir(parents=True, exist_ok=True)
    if scheduler_pid(run):
        sys.exit(f"a scheduler is already running for {run}")
    if not (run / "config.json").exists():
        if not args.index:
            sys.exit("a new run needs --index")
        recs, order = {}, []
        for line in open(args.index):
            if not line.strip():
                continue
            r = json.loads(line)
            h = r["hash"]
            if h in recs:
                continue
            r["name"] = rb.strip_guid(r.get("filename", h)).replace(".cnf.xz", "").replace(".cnf", "")
            r.setdefault("bench_dir", str(Path(r.get("xz_path", args.index)).parent))
            recs[h] = r
            order.append(h)
        rb.size_records([r for r in recs.values() if not r.get("bytes")],
                        Path(args.index).with_suffix(".sizes.json"))
        if args.order == "shuffle":
            import random
            random.Random(args.seed).shuffle(order)
        cfg = dict(name=args.name or run.name, index=str(Path(args.index).resolve()),
                   backends=args.backends.split(","), timeout=args.timeout, verify=not args.no_verify,
                   sat_args=args.sat_arg, cores=args.cores, mem_budget_vm=args.mem_budget_vm,
                   mem_budget_host=args.mem_budget_host, disk_brake_gb=args.disk_brake_gb,
                   order_kind=args.order, seed=args.seed, created=now_iso(), order=order, records=recs,
                   sat_version=subprocess.run(["git", "-C", str(REPO), "rev-parse", "--short", "HEAD"],
                                              capture_output=True, text=True).stdout.strip())
        write_json(run / "config.json", cfg)
        write_json(run / "control.json", dict(cores=args.cores, paused=False, drain=False, stop=False,
                                              now=False, mem_budget_vm=args.mem_budget_vm,
                                              mem_budget_host=args.mem_budget_host))
        log_event(run, f"created: {len(order)} instances, backends {cfg['backends']}, "
                       f"timeout {args.timeout}, checks {'on' if cfg['verify'] else 'off'}, sat at {cfg['sat_version']}")
    else:
        set_control(run, stop=False)
        if args.cores_given:
            set_control(run, cores=args.cores)
    CURRENT.write_text(str(run))
    log = open(run / "scheduler.log", "a")
    p = subprocess.Popen([sys.executable, str(Path(__file__).resolve()), "_loop", "--dir", str(run)],
                         stdout=log, stderr=log, stdin=subprocess.DEVNULL, start_new_session=True)
    for _ in range(30):
        time.sleep(0.5)
        if scheduler_pid(run) == p.pid:
            break
    print(f"scheduler started (pid {p.pid}) for {run}")
    print(f"  status: {Path(__file__).name} status    cores: {Path(__file__).name} cores N    "
          f"pause: {Path(__file__).name} pause    resume: {Path(__file__).name} resume")


def cmd_loop(args) -> None:
    run = Path(args.dir).resolve()
    s = Scheduler(run)
    signal.signal(signal.SIGTERM, lambda *_: set_control(run, stop=True))
    s.loop()


def cmd_cores(args) -> None:
    run = run_dir(args.dir)
    if args.n < 1:
        sys.exit("cores must be at least 1 (use pause to stop)")
    set_control(run, cores=args.n, now=bool(args.now))
    log_event(run, f"cores -> {args.n}" + (" (now)" if args.now else ""))
    print(f"cores {args.n}" + ("; the newest jobs above it are stopped and requeued" if args.now
                               else "; running jobs above it finish first"))


def cmd_pause(args) -> None:
    run = run_dir(args.dir)
    set_control(run, paused=True, drain=bool(args.drain))
    if args.drain:
        print("pausing: no new jobs; the running ones finish")
    else:
        print("paused: running jobs stopped and requeued (they rerun from the start on resume)")


def cmd_resume(args) -> None:
    run = run_dir(args.dir)
    set_control(run, paused=False, drain=False)
    if not scheduler_pid(run):
        print("the scheduler is not running; starting it")
        args.index, args.cores_given = None, False
        args.dir = str(run)
        cmd_start(args)
    else:
        print("resumed")


def cmd_stop(args) -> None:
    run = run_dir(args.dir)
    pid = scheduler_pid(run)
    if not pid:
        print("not running")
        return
    set_control(run, stop=True)
    for _ in range(120):
        time.sleep(0.5)
        if not _pid_alive(pid):
            break
    print("stopped; running jobs requeued. `duo.py start --dir %s` resumes." % run)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("start", help="create a run (with --index) or restart one")
    s.add_argument("--dir", required=True)
    s.add_argument("--index")
    s.add_argument("--name")
    s.add_argument("--backends", default="satsuma,hydra_circuit_satsuma")
    s.add_argument("--timeout", type=int, default=5000)
    s.add_argument("--cores", type=int, default=None)
    s.add_argument("--no-verify", action="store_true",
                   help="skip the certificate checks after UNSAT verdicts (solving unchanged)")
    s.add_argument("--order", choices=("index", "shuffle"), default="index")
    s.add_argument("--seed", type=int, default=2022)
    s.add_argument("--mem-budget-vm", type=float, default=26.0)
    s.add_argument("--mem-budget-host", type=float, default=20.0)
    s.add_argument("--disk-brake-gb", type=float, default=50.0)
    s.add_argument("--sat-arg", action="append", default=[])
    for name, h in (("status", "score what both have finished, and what runs now"),
                    ("pause", "stop the running jobs (or --drain) and start none"),
                    ("resume", "carry on"), ("stop", "end the scheduler; start --dir resumes")):
        p = sub.add_parser(name, help=h)
        p.add_argument("--dir")
        if name == "status":
            p.add_argument("--running", action="store_true")
        if name == "pause":
            p.add_argument("--drain", action="store_true", help="let the running jobs finish")
    c = sub.add_parser("cores", help="change the number of cores")
    c.add_argument("n", type=int)
    c.add_argument("--now", action="store_true", help="stop the newest jobs above N at once")
    c.add_argument("--dir")
    lp = sub.add_parser("_loop")
    lp.add_argument("--dir", required=True)
    args = ap.parse_args()
    if args.cmd == "start":
        args.cores_given = args.cores is not None
        if args.cores is None:
            args.cores = 8
    {"start": cmd_start, "_loop": cmd_loop, "status": cmd_status, "cores": cmd_cores,
     "pause": cmd_pause, "resume": cmd_resume, "stop": cmd_stop}[args.cmd](args)


if __name__ == "__main__":
    main()
