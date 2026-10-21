#!/usr/bin/env python3
"""Collect the best programs from Patel-tool runs on sparse68, re-verify each
with PLinOpt's SLPchecker against OUR matrices (after translating his syntax),
transpose the P^T results with PLinOpt's transpozer, assemble the cheapest
triple and check it with slp48check.py (exact Brent over Q, both cost models).

Usage: collect.py [--pt-glob 'pt/run_s*/best.slp'] [--out cand_dir]
"""
import argparse
import glob
import os
import re
import subprocess
import sys

SP = os.environ.get("R48_SCRATCH", "/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad")  # run directories (scratch)
BIN = os.environ.get("PLINOPT_BIN", f"{SP}/plinopt-run/bin")  # SLPchecker, transpozer, optimizer, matrix-transpose
CAND = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "cand48")
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import slp48check as C  # noqa: E402


def slpcheck(sms, text):
    r = subprocess.run([f"{BIN}/SLPchecker", "-M", sms], input=text, capture_output=True, text=True)
    o = re.sub(r"\x1b\[[0-9;]*m", "", r.stdout + r.stderr)
    m = re.search(r"SUCCESS.*?<(\d+), (\d+)>", o)
    return (int(m.group(1)), int(m.group(2))) if m else None


def translate(path):
    prog = C.parse(open(path).read())
    n_in = 1 + max(int(m) for _, rhs in prog for m in re.findall(r"\bi(\d+)\b", rhs))
    lines = C.emit_plinopt(prog, n_in)
    return "\n".join(lines) + "\n"


def transpose(text):
    r = subprocess.run([f"{BIN}/transpozer"], input=text, capture_output=True, text=True)
    return "\n".join(ln for ln in r.stdout.splitlines() if ln.strip() and not ln.startswith("#")) + "\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", default=f"{SP}/patel202/out")
    ap.add_argument("--pt-glob", default=f"{SP}/patel202/pt/run_s*/best.slp")
    ap.add_argument("--out", default=f"{SP}/patel202/cand")
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    best = {}
    for ph in "LRP":
        sms = f"{CAND}/sparse68_{ph}.sms"
        base = slpcheck(sms, open(f"{CAND}/sparse68_{ph}.slp").read())
        print(f"{ph}: ours {base} = {sum(base)}")
        for p in sorted(glob.glob(f"{a.runs}/sparse68_{ph}/worker_*/best.slp")):
            t = translate(p)
            c = slpcheck(sms, t)
            print(f"   {p.split('/')[-2]}: {c} = {sum(c) if c else None}")
            if c and (ph not in best or sum(c) < best[ph][0]):
                best[ph] = (sum(c), t, p)
        if ph not in best or best[ph][0] > sum(base):
            best[ph] = (sum(base), open(f"{CAND}/sparse68_{ph}.slp").read(), "ours")
    # P through its transpose
    smsP = f"{CAND}/sparse68_P.sms"
    for p in sorted(glob.glob(a.pt_glob)):
        t = transpose(translate(p))
        c = slpcheck(smsP, t)
        print(f"   P^T {p.split('/')[-2]}: transposed {c} = {sum(c) if c else None}")
        if c and sum(c) < best["P"][0]:
            best["P"] = (sum(c), t, p + " (transposed)")
    for ph in "LRP":
        open(f"{a.out}/{ph}.slp", "w").write(best[ph][1])
        print(f"best {ph}: {best[ph][0]} from {best[ph][2]}")
    total = sum(best[ph][0] for ph in "LRP")
    print(f"TOTAL (PLinOpt count): {total}")
    r = subprocess.run([sys.executable, os.path.join(os.path.dirname(HERE), "slp48check.py"), "--dir", a.out], capture_output=True, text=True)
    print(r.stdout.strip())
    if r.returncode:
        print("INDEPENDENT CHECK FAILED", r.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
