#!/usr/bin/env python3
"""Exact free-basis leg screen of the new Hell's Bells classes.

In the alternative-basis model a class costs legA + legB + legC + 14 per
step, where each leg minimum is a de Groote class invariant computed
exactly by ../../target/release/fbmin on one representative (a 9-column
0/1 mask per product, mod 2).  A leg with d distinct nonzero rows costs
at least d - 9; fbmin decides d-9 (tier 1), d-8 (tier 2) and d-7 (tier 3)
exactly and otherwise proves min >= d-6.  So the per-step total is
floor2 + extras, floor2 = dA + dB + dC - 13, and a class can reach a
total T only if its extras sum to at most T - floor2.

Staged per class: tier 1 on every leg; then tiers 1-2, then tier 3 on
the legs still open, stopping as soon as the proved extras exceed the
slack for 51 (the record).  Verdicts: ALERT-<T> (T <= 50, all legs exact),
TIE-51, ruled-out-51 (total proved >= 52), undecided (a leg beyond tier
3 with the slack not yet exhausted), total-<T> (exact total >= 52).

Usage: hblegs.py HB_BITS_TXT VERDICTS_CSV OUTDIR [--max-floor 51]
         [--jobs 3] [--threads 2] [--leg-timeout 1800]
Resumable: classes already in OUTDIR/hblegs.csv are skipped.
"""
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor

H = os.path.dirname(os.path.abspath(__file__))
FBMIN = f"{H}/../../target/release/fbmin"
LEG_RE = re.compile(r"min_adds(>?=)(\d+) \[(.*?)\]")


def flag(name, default):
    return int(sys.argv[sys.argv.index(name) + 1]) if name in sys.argv else default


def legs_of(bits):
    """three sorted lists of distinct nonzero 9-char masks (A, B, C legs)."""
    out = []
    for blk in range(3):
        rows = {"".join(bits[blk * 207 + m * 9 + k] for k in range(9)) for m in range(23)}
        rows.discard("0" * 9)
        out.append(sorted(rows))
    return out


def run_fbmin(path, mode, threads, timeout):
    """-> (exact: bool, value, how)."""
    cmd = [FBMIN, "--threads", str(threads)]
    if mode == "tier1":
        cmd.append("--tier1-only")
    elif mode == "tier3":
        cmd.append("--tier3")
    cmd.append(path)
    try:
        out = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout).stdout
    except subprocess.TimeoutExpired as e:
        out = e.stdout.decode() if isinstance(e.stdout, bytes) else (e.stdout or "")
        m = LEG_RE.search(out)
        return (False, int(m.group(2)) if m else None, "timeout")
    m = LEG_RE.search(out)
    if not m:
        raise RuntimeError(f"fbmin: unparsable output for {path}: {out[:200]}")
    op, val, how = m.groups()
    if op == "=":
        assert "CERT-OK" in out, f"positive result without certificate: {path}"
    return (op == "=", int(val), how)


def screen(item):
    cls, name, bits, floor2, outdir, threads, timeout = item
    t0 = time.time()
    legs = legs_of(bits)
    d = [len(L) for L in legs]
    assert sum(d) - 13 == floor2, (cls, d, floor2)
    paths = []
    for s, L in zip("ABC", legs):
        p = f"{outdir}/legs/{cls}_{s}.legs"
        with open(p, "w") as f:
            f.write("\n".join(L) + "\n")
        paths.append(p)
    slack = 51 - floor2  # extras allowed for a 51
    extra = [None] * 3  # exact extras per leg
    lb = [0] * 3  # proved lower bound on extras
    how = [""] * 3
    for mode, reach in (("tier1", 0), ("tier2", 1), ("tier3", 2)):
        for i in range(3):
            if extra[i] is not None or lb[i] > reach:
                continue
            ok, val, h = run_fbmin(paths[i], mode, threads, timeout)
            how[i] = h
            if val is None:
                continue
            e = val - (d[i] - 9)
            if ok:
                extra[i] = e
                lb[i] = e
            else:
                lb[i] = max(lb[i], e)
        if sum(lb) > slack:
            break
    tot_lb = floor2 + sum(lb)
    exact = all(x is not None for x in extra)
    if exact and tot_lb <= 50:
        verdict = f"ALERT-{tot_lb}"
    elif exact and tot_lb == 51:
        verdict = "TIE-51"
    elif tot_lb >= 52:
        verdict = "ruled-out-51" if not exact else f"total-{tot_lb}"
    else:
        verdict = "undecided"
    cells = [f"{'=' if extra[i] is not None else '>='}{(d[i] - 9) + lb[i]}" for i in range(3)]
    return (cls, name, floor2, d, cells, tot_lb, exact, verdict, how, time.time() - t0)


def main():
    bits_txt, verdicts, outdir = sys.argv[1:4]
    max_floor, jobs, threads, timeout = flag("--max-floor", 51), flag("--jobs", 3), flag("--threads", 2), flag("--leg-timeout", 1800)
    os.makedirs(f"{outdir}/legs", exist_ok=True)
    res = f"{outdir}/hblegs.csv"
    done = set()
    if os.path.exists(res):
        done = {ln.split(",")[0] for ln in open(res) if not ln.startswith("class,")}
    else:
        open(res, "w").write("class,rep,floor2,dA,dB,dC,legA,legB,legC,total_lb,exact,verdict,secs\n")
    bits = {}
    for ln in open(bits_txt):
        name, bs = ln.split()
        bits[name] = bs
    reps = {}
    for ln in open(verdicts):
        f = ln.rstrip("\n").split(",")
        if f[1] == "NEW" and int(f[3]) <= max_floor and f[2] not in reps:
            reps[f[2]] = (f[0], int(f[3]))
    items = [(cls, name, bits[name], fl, outdir, threads, timeout) for cls, (name, fl) in sorted(reps.items(), key=lambda t: (t[1][1], t[0])) if cls not in done]
    print(f"{len(reps)} new classes with floor2 <= {max_floor}; {len(items)} to screen ({len(done)} done)", flush=True)
    with ProcessPoolExecutor(max_workers=jobs) as ex:
        for cls, name, floor2, d, cells, tot_lb, exact, verdict, how, secs in ex.map(screen, items):
            with open(res, "a") as f:
                f.write(f"{cls},{name},{floor2},{d[0]},{d[1]},{d[2]},{cells[0]},{cells[1]},{cells[2]},{tot_lb},{int(exact)},{verdict},{secs:.0f}\n")
            tag = "*** " if verdict.startswith(("ALERT", "TIE")) else ""
            print(f"{tag}{cls} ({name}) floor2={floor2} d={d} legs={cells} total{'=' if exact else '>='}{tot_lb} -> {verdict} ({secs:.0f} s)", flush=True)
    print("screen complete.", flush=True)


if __name__ == "__main__":
    main()
