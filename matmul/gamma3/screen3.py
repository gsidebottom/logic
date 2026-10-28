#!/usr/bin/env python3
"""Growth factors of every rank-23 3x3 scheme in the HKS database (dbcache/schemes.tgz) and of
our 55-addition scheme, at their stored representatives, in all three role assignments.

Per scheme and role (P = the factor set that computes the outputs; L, R the other two):
  g_infinf = max_j sum_i |p_ji| ||L_i||_1 ||R_i||_1
  g_inf2   = max_j sum_i |p_ji| ||L_i||_2 ||R_i||_2
  g_22     = || (sum_i |p_ji| ||L_i||_2 ||R_i||_2)_j ||_2
  Q0       = max_j ( nnz(P_j) + max_{i: p_ji != 0} (nnz(L_i) + nnz(R_i)) )     (DPS / Ballard et al.)
  amp      = max_j (1/2) sqrt( sum_i p_ji^2 ||L_i||_2^2 ||R_i||_2^2 )
and g_2 = sum_i ||L_i||_2 ||R_i||_2 ||P_{*,i}||_2 (the same in every role).
Exponents are log_3 of the factor; accurate_262's are 3.522 (g_infinf), 2.250 (g_inf2),
3.250 (g_22), 3.636 (g_2); its amp 2 sqrt2 against the classical 1 is exponent 0.75.

  python3 screen3.py OUT.csv          (about a minute; the stored run is db3_gamma.csv)
"""
import csv
import math
import os
import sys
import tarfile

import numpy as np

M = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))  # matmul/
sys.path.insert(0, M)
import f3scan  # noqa: E402

R = 23


def factors(a, b, c):
    """a, b, c: (23, 9) float arrays, rows = the three factor vectors of each product.
    Returns dict of the quantities for the three roles (P = c, P = a, P = b) and g_2."""
    out = {}
    n2 = [np.linalg.norm(x, axis=1) for x in (a, b, c)]
    out["g_2"] = float(np.sum(n2[0] * n2[1] * n2[2]))
    for role, (L, Rm, P) in enumerate(((a, b, c), (b, c, a), (c, a, b))):
        l1, r1 = np.abs(L).sum(1), np.abs(Rm).sum(1)
        l2, r2 = np.linalg.norm(L, axis=1), np.linalg.norm(Rm, axis=1)
        Pt = P.T  # (9, 23): rows = outputs
        absP = np.abs(Pt)
        s_inf = absP @ (l1 * r1)
        s_2 = absP @ (l2 * r2)
        amp = 0.5 * np.sqrt((Pt ** 2) @ (l2 ** 2 * r2 ** 2))
        nz = Pt != 0
        nnzL, nnzR = (L != 0).sum(1), (Rm != 0).sum(1)
        q0 = max(int(nz[j].sum()) + int(max((nnzL[i] + nnzR[i]) for i in np.nonzero(nz[j])[0])) for j in range(9))
        out[role] = dict(g_infinf=float(s_inf.max()), g_inf2=float(s_2.max()), g_22=float(np.linalg.norm(s_2)),
                         Q0=q0, amp=float(amp.max()))
    return out


def load_db():
    tf = tarfile.open(f"{M}/dbcache/schemes.tgz", "r:gz")
    for mem in tf:
        if not mem.name.endswith(".tab"):
            continue
        sm = f3scan.parse_tab(tf.extractfile(mem).read().decode())
        if sm is None:
            continue
        name = mem.name.rsplit("/", 1)[-1][:-4]
        a = np.array([s[0] for s in sm], float)
        b = np.array([s[1] for s in sm], float)
        c = np.array([s[2] for s in sm], float)
        yield name, a, b, c


def load_slp(path):
    cap = {}
    orig = f3scan.legs_from_signed
    f3scan.legs_from_signed = lambda A, B, G: cap.update(A=A, B=B, G=G) or orig(A, B, G)
    try:
        f3scan.legs_from_slp(path)
    finally:
        f3scan.legs_from_signed = orig
    return (np.array(cap["A"], float), np.array(cap["B"], float), np.array(cap["G"], float))


def main():
    out = sys.argv[1]
    rows = []
    items = list(load_db())
    print(f"{len(items)} database schemes parsed", flush=True)
    items.append(("i19_55adds (ours)",) + load_slp(f"{M}/external/i19-55adds-slp.txt"))
    items.append(("i12_56adds (ours)",) + load_slp(f"{M}/external/i12-56adds-slp.txt"))
    keys = ["g_infinf", "g_inf2", "g_22", "Q0", "amp"]
    with open(out, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["name", "g_2"] + [f"{k}_r{r}" for r in range(3) for k in keys] + [f"best_{k}" for k in keys])
        for name, a, b, c in items:
            d = factors(a, b, c)
            best = {k: min(d[r][k] for r in range(3)) for k in keys}
            w.writerow([name, f"{d['g_2']:.4f}"] + [f"{d[r][k]:.4f}" if k != "Q0" else d[r][k] for r in range(3) for k in keys]
                       + [f"{best[k]:.4f}" if k != "Q0" else best[k] for k in keys])
            rows.append((name, d, best))
    # summary
    L3 = math.log(3)
    thr = {"g_infinf": 3 ** 3.522197, "g_inf2": 3 ** 2.25, "g_22": 3 ** 3.25, "amp": 0.5 * math.sqrt(3) * 3 ** 0.75}
    print("\nclassical 3x3: g_infinf 3, g_inf2 3, g_22 9, g_2 27, Q0 5, amp 0.866")
    print("thresholds for accurate_262's exponents: " + ", ".join(f"{k} < {v:.2f}" for k, v in thr.items()) + ", g_2 < 54.29")
    for k in ["g_infinf", "g_inf2", "g_22", "amp"]:
        v = np.array([r[2][k] for r in rows[:-2]])
        print(f"\n{k}: DB best-role min {v.min():.4f} (exponent {math.log(v.min()) / L3:.3f}), median {np.median(v):.3f}, "
              f"max {v.max():.3f}; schemes under the threshold: {(v < thr[k]).sum()}")
        top = sorted(rows[:-2], key=lambda r: r[2][k])[:5]
        for name, d, best in top:
            print(f"   {name:28s} {k}={best[k]:.4f}  g_2={d['g_2']:.2f}  Q0={best['Q0']}  amp={best['amp']:.3f}  g_inf2={best['g_inf2']:.3f}  g_infinf={best['g_infinf']:.2f}")
    v = np.array([r[1]["g_2"] for r in rows[:-2]])
    print(f"\ng_2: DB min {v.min():.4f} (exponent {math.log(v.min()) / L3:.3f}), median {np.median(v):.2f}, max {v.max():.2f}; under 54.29: {(v < 54.29).sum()}")
    q = np.array([r[2]["Q0"] for r in rows[:-2]])
    print(f"Q0 (best role): min {q.min()}, median {np.median(q)}, max {q.max()}; accurate_262 has 34 (4x4), classical 3x3 has 5")
    for name, d, best in rows[-2:]:
        print(f"\n{name}: g_2={d['g_2']:.3f}; per role " + " | ".join(
            f"r{r}: g_infinf {d[r]['g_infinf']:.2f} g_inf2 {d[r]['g_inf2']:.3f} g_22 {d[r]['g_22']:.3f} Q0 {d[r]['Q0']} amp {d[r]['amp']:.3f}" for r in range(3)))
        print("   exponents (best role): " + ", ".join(f"{k} {math.log(best[k]) / L3:.3f}" for k in ["g_infinf", "g_inf2", "g_22"]) + f", amp/0.866 {math.log(best['amp'] / (0.5 * math.sqrt(3))) / L3:.3f}")


if __name__ == "__main__":
    main()
