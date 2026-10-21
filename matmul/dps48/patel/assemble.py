#!/usr/bin/env python3
"""Assemble the cheapest verified triple of a sweep/climb candidate: for each
side, the best program among the stage directories (SLPchecker count against
the point's matrices; P^T programs transposed with PLinOpt's transpozer),
written with the point's sms files to OUTDIR and checked exactly.

Usage: assemble.py SWEEP_DIR TAG POINT_PREFIX OUTDIR
   e.g. assemble.py .../sweep_rust1 pool_l0.3_cand005 .../r48/pool_l0.3/cand005 OUT
"""
import glob
import os
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sweep as S  # noqa: E402


def main():
    sweep_dir, tag, prefix, out = sys.argv[1:5]
    os.makedirs(out, exist_ok=True)
    sms = {s: f"{prefix}_{s}.sms" for s in "LRP"}
    best = {}
    for side in ("L", "R", "Pt"):
        for path in sorted(glob.glob(f"{sweep_dir}/{tag}/*_{side}_s*/best.slp")):
            t = S.translate(path)
            c = S.slpcheck(sms["P"], S.transpose(t)) if side == "Pt" else S.slpcheck(sms[side], t)
            if c is None:
                print(f"  {side} {path.split('/')[-2]}: does not verify")
                continue
            cost = sum(c) + (0 if side != "Pt" else 0)
            print(f"  {side} {path.split('/')[-2]}: {c} = {cost}")
            if side not in best or cost < best[side][0]:
                best[side] = (cost, t, path)
    for side in ("L", "R", "Pt"):
        cost, t, path = best[side]
        if side == "Pt":
            open(os.path.join(out, "Pt.slp"), "w").write(t)
            open(os.path.join(out, "P.slp"), "w").write(S.transpose(t))
        else:
            open(os.path.join(out, f"{side}.slp"), "w").write(t)
    for s in "LRP":
        shutil.copy(sms[s], os.path.join(out, f"{s}.sms"))
    total = best["L"][0] + best["R"][0] + best["Pt"][0]
    print(f"best: L {best['L'][0]} R {best['R'][0]} P {best['Pt'][0]} = {total} -> {out}")
    r = subprocess.run([sys.executable, os.path.join(os.path.dirname(HERE), "slp48check.py"), "--dir", out], capture_output=True, text=True)
    print(r.stdout.strip().splitlines()[-2:] if r.stdout.strip() else r.stderr[-500:])
    sys.exit(r.returncode)


if __name__ == "__main__":
    main()
