#!/usr/bin/env python3
"""Model-sweep conversion minimization: for EVERY gauge-distinct sign
model of a mask scheme that clears the given leg targets (fbsloop
stopped at the first), run the exact in-scope conversion sweep
(fbsmin --min-basis-at) on each leg and report the cheapest package.

For database classes the one-shot floor is 55+1 => conversions >= 5
(no DB class attains flat <= 55 except the record class), so this can
only polish a known package toward 51+5 = 56, never beat S-P's 56.

Usage: modelconv.py bits fbsmin workdir tA tB tC [--nmodels N]
         [--threads T] [--best-known B]
Stop: touch <workdir>/STOP.
"""
import pathlib
import re
import subprocess
import sys
import time

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from gaugecanon import dedup_models  # noqa: E402
from lift import lift_models, z_verify  # noqa: E402

args = sys.argv[1:]
flags = {"--nmodels": 128, "--threads": 4, "--best-known": 10 ** 9}
pos = []
i = 0
while i < len(args):
    if args[i] in flags:
        flags[args[i]] = int(args[i + 1])
        i += 2
    else:
        pos.append(args[i])
        i += 1
BITSF, FBSMIN, WORKD = pos[0], pos[1], pathlib.Path(pos[2])
TARGETS = [int(x) for x in pos[3:6]]
WORKD.mkdir(parents=True, exist_ok=True)
RES = WORKD / "modelconv_results.csv"
if not RES.exists():
    RES.write_text("model,cleared,convA,convB,convC,total,secs\n")

bits = [int(c) for c in open(BITSF).read().split()[-1].strip()]
assert len(bits) == 621
DIMS = (3, 3, 3, 23)


def rows_of(signs):
    coef = [signs.get(v, 0) if bits[v] else 0 for v in range(621)]
    return [[tuple(coef[off + m * 9 + k] for k in range(9)) for m in range(23)]
            for off in (0, 207, 414)]


def write_slegs(path, rows):
    with open(path, "w") as f:
        for r in rows:
            f.write(" ".join(str(x) for x in r) + "\n")


CLEAR_RE = re.compile(r"min_adds(>?=)(\d+)")
CONV_RE = re.compile(r"conversion cost (\d+)")


def leg_min(path, target):
    try:
        out = subprocess.run(
            [FBSMIN, "--threads", str(flags["--threads"]),
             "--max-helpers", "3", str(path)],
            capture_output=True, text=True, timeout=3600).stdout
    except subprocess.TimeoutExpired:
        return False   # undecided at budget -> treat as not cleared
    m = CLEAR_RE.search(out)
    return (m.group(1) == "=" and int(m.group(2)) == target) if m else False


def leg_conv(path, target):
    try:
        out = subprocess.run(
            [FBSMIN, "--threads", str(flags["--threads"]),
             "--min-basis-at", str(target), str(path)],
            capture_output=True, text=True, timeout=6 * 3600).stdout
    except subprocess.TimeoutExpired:
        return None
    m = CONV_RE.search(out)
    return int(m.group(1)) if m and "CERT-OK" in out else None


models = lift_models(bits, flags["--nmodels"], DIMS)
models = dedup_models(models, bits)
print(f"{len(models)} gauge-distinct models; targets {TARGETS}, "
      f"best known {flags['--best-known']}", flush=True)
best = flags["--best-known"]
for mi, (signs, _) in enumerate(models):
    if (WORKD / "STOP").exists():
        print("STOP present -- halting.", flush=True)
        break
    assert z_verify(bits, signs, DIMS) == 0
    rows = rows_of(signs)
    paths = []
    for nm, r in zip("ABC", rows):
        pp = WORKD / f"m{mi}_{nm}.slegs"
        write_slegs(pp, r)
        paths.append(pp)
    t0 = time.time()
    cleared = all(leg_min(p, t) for p, t in zip(paths, TARGETS))
    convs = ["", "", ""]
    tot = ""
    if cleared:
        print(f"model {mi}: CLEARS {TARGETS}; sweeping conversions...",
              flush=True)
        convs = [leg_conv(p, t) for p, t in zip(paths, TARGETS)]
        if all(c is not None for c in convs):
            tot = sum(convs)
            if tot < best:
                best = tot
                print(f"*** model {mi}: NEW BEST conversions "
                      f"{convs[0]}+{convs[1]}+{convs[2]} = {tot} "
                      f"(one-shot {sum(TARGETS) + 14 + tot}) ***",
                      flush=True)
    secs = time.time() - t0
    with open(RES, "a") as f:
        f.write(f"{mi},{int(cleared)},{convs[0]},{convs[1]},{convs[2]},"
                f"{tot},{secs:.0f}\n")
    if not cleared:
        for p in paths:
            p.unlink()
print(f"modelconv done; best conversions {best}", flush=True)
