#!/usr/bin/env python3
"""The checks on rank-23 3x3 decompositions harvested by flip23 --descend --known-families.

Per decomposition: (1) the 729 Brent equations, exactly; (2) its mod-2 image -- none if a
product needs a 1/2 (its scale 2^(ea+eb+ec) below 1), else the F2 family string (ranks over
F2, the database's directory naming) and whether the database or Hell's Bells has that F2
family; (3) f3scan's whole-orbit lower bound on the additions over F3 (1/2 -> 2), which holds
for every Z[1/2] representative a basis change invertible mod 3 reaches, scalings not even
counted -- the bound that leaves only our 55 below 56 among the known classes.  A bound of 54
or less is a candidate for beating the 55 record.

  check_new23.py [--hb DIR] [--jobs N] [--target 54] DUMP ... (or @FILE listing them)
"""
import itertools
import os
import sys
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, ".."))
import classify23 as C  # noqa: E402
import f3scan as F  # noqa: E402

TR = lambda v: [v[3 * c + r] for r in range(3) for c in range(3)]


def brent_bad(sch):
    return sum(1 for x, y, z in itertools.product(range(9), repeat=3)
               if sum(a[x] * b[y] * c[z] for a, b, c in sch)
               != (1 if (x % 3 == y // 3 and x // 3 == z // 3 and y % 3 == z % 3) else 0))


def rank2(m):
    rows = [sum((int(m[3 * r + c]) % 2) << c for c in range(3)) for r in range(3)]
    rank = 0
    for bit in (1, 2, 4):
        p = next((k for k in range(len(rows)) if rows[k] & bit), None)
        if p is None:
            continue
        piv = rows.pop(p)
        rows = [x ^ piv if x & bit else x for x in rows]
        rank += 1
    return rank


def family2(sch):
    """the family string with ranks over F2 (the database's directory names)"""
    ranks = [tuple(rank2(f) for f in prod) for prod in sch]
    term = lambda count, var, exp: (str(count) if count > 1 else "") + var + exp
    xs = Counter(r for t in ranks for r in t)
    ys = Counter(sum(t) for t in ranks)
    zs = Counter(sum(t[s] for t in ranks) for s in range(3))
    parts = [term(xs[k], "x", str(k) if k > 1 else "") for k in sorted(xs, reverse=True)]
    parts += [term(ys[k], "y", str(k)) for k in sorted(ys, reverse=True)]
    parts += [term(zs[k], "z", str(k)) for k in sorted(zs, reverse=True)]
    return "+".join(parts)


def mod2_image(sch):
    """the integral scheme with every factor primitive and the scale on c, or the reason
    there is no mod-2 image"""
    out = []
    for prod in sch:
        prim = []
        scale = Fraction(1)
        for f in prod:
            den = 1
            for x in f:
                den = den * x.denominator // __import__("math").gcd(den, x.denominator)
            ints = [int(x * den) for x in f]
            g = 0
            for x in ints:
                g = __import__("math").gcd(g, x)
            prim.append([x // g for x in ints])
            scale *= Fraction(g, den)
        if scale.denominator % 2 == 0:
            return None, "needs 1/2"
        if scale.numerator % 2 == 0:
            return None, "a product vanishes mod 2"
        a, b, c = prim
        out.append((a, b, [int(x * scale) for x in c]))
    return out, ""


def mod3(v):
    return [(x.numerator * pow(x.denominator, -1, 3)) % 3 for x in v]


def check(item):
    path, target = item
    sch = C.parse_dump(path)
    bad = brent_bad(sch)
    img, why = mod2_image(sch)
    fam2 = family2(img) if img is not None else ""
    legs = F.legs_from_signed([mod3(a) for a, _, _ in sch], [mod3(b) for _, b, _ in sch],
                              [mod3(TR(c)) for _, _, c in sch])
    b_t, b_c, ntrip, ncl = F.scan(legs, target)
    return path, bad, C.family(sch), why, fam2, b_t, b_c


def main():
    args = sys.argv[1:]
    opt = {"--hb": None, "--jobs": "12", "--target": "54"}
    for k in list(opt):
        if k in args:
            i = args.index(k)
            opt[k] = args[i + 1]
            del args[i:i + 2]
    known2 = set()
    import tarfile
    with tarfile.open(C.DB, "r:gz") as tf:
        for mem in tf:
            if mem.name.endswith(".tab"):
                known2.add(mem.name.split("/")[-2])
    if opt["--hb"]:
        for name in os.listdir(opt["--hb"]):
            if name.endswith(".txt"):
                known2.add(family2(C.parse_hb(os.path.join(opt["--hb"], name))))
    target = int(opt["--target"])
    paths = [q.strip() for a in args for q in (open(a[1:]) if a.startswith("@") else [a]) if q.strip()]
    with ProcessPoolExecutor(int(opt["--jobs"])) as ex:
        rows = list(ex.map(check, [(p, target) for p in paths], chunksize=4))
    nbad = sum(1 for r in rows if r[1])
    print(f"{len(rows)} decompositions; {nbad} fail Brent")
    by_fam = {}
    for path, bad, fam, why, fam2, b_t, b_c in rows:
        by_fam.setdefault(fam, []).append((b_c, b_t, why, fam2, path))
    print(f"{len(by_fam)} Q-families; mod-3 whole-orbit bound (min over the family's decompositions):")
    for fam, v in sorted(by_fam.items(), key=lambda kv: min(x[0] for x in kv[1])):
        best = min(x[0] for x in v)
        n2 = Counter("needs 1/2" if x[2] else ("F2 family known" if x[3] in known2 else "F2 family NEW")
                     for x in v)
        flag = "  <-- CANDIDATE" if best <= target else ""
        print(f"  {fam:46s} {len(v):5d} decs  bound {best}{flag}  mod 2: {dict(n2)}")
    cands = [r for r in rows if r[6] <= target]
    print(f"{len(cands)} decompositions with a bound <= {target}")


if __name__ == "__main__":
    main()
