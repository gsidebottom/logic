"""The 648 points of the dyadic orthogonal sub-orbit of 4x4x4_48_accurate (dyadic_orth.py's
enumeration: 6 classes of G under signed permutations, (U, V, W) in classes^3, 3 role
assignments) written as exact dyadic schemes, points/r{role}_u{iu}v{iv}w{iw}_{L,R,P}.sms, for
scoring by the realized rounding model (slpopt realized).  The transform already folds the sqrt2
factors into P as powers of two, so every entry is dyadic; each point is checked on all Brent
equations (floating point, to 1e-12) before it is written.

  python3 dyadic_points.py OUTDIR
"""
import itertools, os, sys
from fractions import Fraction
import numpy as np
np.seterr(all="ignore")
import orbit
import dyadic_orth as d

out = sys.argv[1] if len(sys.argv) > 1 else "points"
os.makedirs(out, exist_ok=True)
cl = d.classes()
base = orbit.load(orbit.SCHEMES["table1"])
n = 0
for role, (L, R, P) in enumerate(orbit.roles(*base)):
    for iu, iv, iw in itertools.product(range(len(cl)), repeat=3):
        L2, R2, P2 = d.transformed(L, R, P, cl[iu], cl[iv], cl[iw])
        assert orbit.brent_error(L2, R2, P2) < 1e-12
        prefix = os.path.join(out, f"r{role}_u{iu}v{iv}w{iw}")
        for name, M in (("L", L2), ("R", R2), ("P", P2)):
            with open(f"{prefix}_{name}.sms", "w") as f:
                f.write(f"# dyadic orthogonal point role {role} classes U{iu} V{iv} W{iw} of 4x4x4_48_accurate's orbit\n")
                f.write(f"{M.shape[0]} {M.shape[1]} R\n")
                for i in range(M.shape[0]):
                    for j in range(M.shape[1]):
                        if M[i, j] != 0:
                            q = Fraction(float(M[i, j])).limit_denominator(1 << 20)
                            assert float(q) == M[i, j], (prefix, name, i, j, M[i, j])
                            f.write(f"{i + 1} {j + 1} {q}\n")
                f.write("0 0 0\n")
        n += 1
print(f"wrote {n} points to {out}/")
