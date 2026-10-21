#!/usr/bin/env python3
"""Drive PLinOpt's sub-program refinement (prune.sh -> mirabelle.sh) to a
fixed point, splicing every verified improvement back into the program.

mirabelle.sh re-optimizes the sub-program around a set of temporaries and,
when it finds a shorter one, writes a file mirabelle_<vars><mode>-<pid>.log
holding the old sub-body, a checker report, and the new lines (fresh
temporaries named with a letter unused in the sub-body).  Splicing is left
to the user; this driver does it: remove the old lines, add the new ones
(renamed to globally fresh temporaries), re-emit in a valid topological
order, verify with SLPchecker -M against the matrix, and keep it if the
operation count (additions + multiplications) dropped.  Improvements of
one sweep are applied greedily, largest gain first, each re-verified.

Usage: prune_loop.py --slp PROG.slp --sms MATRIX.sms --bin PLINOPT_BIN
         [--out DIR] [--rounds 20] [--loops 100] [--mode p|t] [--path GNU_PATH]
"""
import argparse
import glob
import os
import re
import shutil
import subprocess
import sys
import time

LINE = re.compile(r"^\s*([A-Za-z]\w*)\s*:=\s*(.*?);\s*$")
IDENT = re.compile(r"[A-Za-z]\w*")


def parse(text):
    out = []
    for ln in text.splitlines():
        ln = ln.split("#")[0].strip()
        if not ln:
            continue
        m = LINE.match(ln)
        if not m:
            raise ValueError(f"unparsable line: {ln}")
        lhs, rhs = m.group(1), m.group(2)
        ops = {t for t in IDENT.findall(rhs)}
        out.append((lhs, rhs, ops))
    return out


def emit(lines):
    return "".join(f"{l}:={r};\n" for l, r, _ in lines)


def toposort(lines, inputs_are=lambda n: n.startswith("i")):
    """valid straight-line order; original order is the tie-break."""
    defined = set()
    pending = list(lines)
    out = []
    while pending:
        progress = False
        rest = []
        for item in pending:
            lhs, rhs, ops = item
            if all(inputs_are(o) or o in defined for o in ops):
                out.append(item)
                defined.add(lhs)
                progress = True
            else:
                rest.append(item)
        pending = rest
        if not progress:
            raise ValueError("cycle or undefined operand: " + ", ".join(l for l, _, _ in pending[:5]))
    return out


def check(bin_dir, sms, text, env):
    r = subprocess.run([f"{bin_dir}/SLPchecker", "-M", sms], input=text, capture_output=True, text=True, env=env)
    o = re.sub(r"\x1b\[[0-9;]*m", "", r.stdout + r.stderr)
    m = re.search(r"SUCCESS.*?<(\d+), (\d+)>", o)
    return (int(m.group(1)), int(m.group(2))) if m else None


def splice(program, impr_text, used_names):
    """program: parsed lines; impr_text: a mirabelle log.  Returns new parsed
    program or None when the old body is not present verbatim."""
    parts = impr_text.split("########################################")
    old_body = parse(parts[0])
    new_body = parse(parts[-1])
    old_keys = {(l, r) for l, r, _ in old_body}
    keep = [x for x in program if (x[0], x[1]) not in old_keys]
    if len(program) - len(keep) != len(old_body):
        return None  # some old line already changed: this improvement no longer applies
    old_lhs = {l for l, _, _ in old_body}
    # rename new temporaries that are neither outputs nor re-definitions of old names
    rename = {}
    taken = used_names | {l for l, _, _ in keep}
    k = 0
    for l, _, _ in new_body:
        if l.startswith("o") or l in old_lhs or l in rename:
            continue
        while True:
            cand = f"w{k}"
            k += 1
            if cand not in taken:
                break
        rename[l] = cand
        taken.add(cand)
    renamed = []
    for l, r, ops in new_body:
        l2 = rename.get(l, l)
        r2 = IDENT.sub(lambda m: rename.get(m.group(0), m.group(0)), r)
        renamed.append((l2, r2, {rename.get(o, o) for o in ops}))
    return toposort(keep + renamed)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--slp", required=True)
    ap.add_argument("--sms", required=True)
    ap.add_argument("--bin", required=True)
    ap.add_argument("--out", default="prune_loop_out")
    ap.add_argument("--rounds", type=int, default=20)
    ap.add_argument("--loops", type=int, default=100)
    ap.add_argument("--mode", default="p")
    ap.add_argument("--path", default="")
    a = ap.parse_args()
    env = dict(os.environ)
    if a.path:
        env["PATH"] = a.path + ":" + env["PATH"]
    os.makedirs(a.out, exist_ok=True)
    sms = os.path.abspath(a.sms)
    program = parse(open(a.slp).read())
    cur = check(a.bin, sms, emit(program), env)
    assert cur, "initial program does not verify"
    print(f"start: {cur[0]}+{cur[1]} = {sum(cur)} ops, {len(program)} lines", flush=True)
    for rnd in range(1, a.rounds + 1):
        wd = os.path.join(a.out, f"round{rnd:02d}")
        os.makedirs(wd, exist_ok=True)
        open(os.path.join(wd, "cur.slp"), "w").write(emit(program))
        t0 = time.time()
        subprocess.run([f"{a.bin}/prune.sh", f"-{a.mode}", "-O", str(a.loops), "cur.slp"], cwd=wd, capture_output=True, text=True, env=env, timeout=14400)
        files = sorted(glob.glob(os.path.join(wd, "mirabelle_*.log")))
        cands = []
        for f in files:
            txt = open(f).read()
            m = re.findall(r"(\d+)\s+additions\s+instead of (\d+)", txt)
            mm = re.findall(r"(\d+)\s+multiplications\s+instead of (\d+)", txt)
            gain = (int(m[-1][1]) - int(m[-1][0]) if m else 0) + (int(mm[-1][1]) - int(mm[-1][0]) if mm else 0)
            cands.append((gain, f, txt))
        cands.sort(key=lambda t: -t[0])
        applied = 0
        used = {l for l, _, _ in program}
        for gain, f, txt in cands:
            try:
                new = splice(program, txt, used)
            except ValueError as e:
                continue
            if new is None:
                continue
            res = check(a.bin, sms, emit(new), env)
            if res and sum(res) < sum(cur):
                program, cur = new, res
                used = {l for l, _, _ in program}
                applied += 1
        open(os.path.join(a.out, f"best_round{rnd:02d}.slp"), "w").write(emit(program))
        print(f"round {rnd}: {len(files)} improvement files, {applied} applied -> {cur[0]}+{cur[1]} = {sum(cur)} ops ({time.time() - t0:.0f}s)", flush=True)
        if applied == 0:
            break
    open(os.path.join(a.out, "best.slp"), "w").write(emit(program))
    print(f"final: {cur[0]}+{cur[1]} = {sum(cur)} ops -> {a.out}/best.slp", flush=True)


if __name__ == "__main__":
    main()
