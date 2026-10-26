"""Inspect a float scheme saved by ampvariety.py (or any (L, R, P) stacked as one vector):
amplification per output, growth factors, the coefficient values seen, and whether snapping the
coefficients to dyadics with denominators up to 2^k keeps the Brent equations (a rational scheme).

  python3 inspect_point.py FILE.npy
"""
import sys
from fractions import Fraction
import numpy as np
np.seterr(all="ignore")
import orbit

x = np.load(sys.argv[1])
RK = 48
L, R, P = x[:RK * 16].reshape(RK, 16), x[RK * 16:2 * RK * 16].reshape(RK, 16), x[2 * RK * 16:].reshape(16, RK)
g = (L * L).sum(1) * (R * R).sum(1)
a = np.sqrt((P * P) @ g) / 2
print(f"amp per output: max {a.max():.4f} mean {a.mean():.4f}  values {np.round(np.sort(a), 3)}")
print(f"gamma_inf2 {orbit.g_inf2(L, R, P):.4f} gamma_infinf {orbit.g_inf_inf(L, R, P):.4f} gamma2 {orbit.g2(L, R, P):.4f} brent {orbit.brent_error(L, R, P):.1e}")
# per-product rescaling makes the comparison of coefficients meaningful: scale each product so
# that max|L_i| = max|R_i| = 1
Ls, Rs, Ps = L.copy(), R.copy(), P.copy()
for i in range(RK):
    al, be = np.abs(Ls[i]).max(), np.abs(Rs[i]).max()
    Ls[i] /= al; Rs[i] /= be; Ps[:, i] *= al * be
vals = np.concatenate([Ls.ravel(), Rs.ravel(), Ps.ravel()])
vals = vals[np.abs(vals) > 1e-9]
print(f"nonzeros {len(vals)} (L {np.count_nonzero(np.abs(Ls) > 1e-9)}, R {np.count_nonzero(np.abs(Rs) > 1e-9)}, P {np.count_nonzero(np.abs(Ps) > 1e-9)})")
u, c = np.unique(np.round(np.abs(vals), 3), return_counts=True)
print("distinct |coefficients| (rounded to 1e-3), with counts:", ", ".join(f"{v}x{n}" for v, n in zip(u, c))[:400])
for k in (1, 2, 3, 4, 6, 8):
    d = 2 ** k
    Ld, Rd, Pd = (np.round(M * d) / d for M in (Ls, Rs, Ps))
    err = orbit.brent_error(Ld, Rd, Pd)
    print(f"snapped to denominators 2^{k}: brent error {err:.2e}{'  <-- exact dyadic scheme' if err < 1e-12 else ''}")
