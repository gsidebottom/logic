#!/usr/bin/env python3
"""The stabilizer of the Li-Wang-Hu family over Q(t), and the elements behind the doubling at s(1/4).

Input: iso_between.py outputs in ISODIR, stab_<t>.json (SRC = TGT = s(t)) for t in TS_STAB and
curve_<t>.json (SRC = s(t), TGT = s(1/(16t))) for t in TS_CURVE.  Elements are matched across t by
slot map and layer permutation; X, Y, Z (scaled so that one fixed entry is 1) are fitted entrywise as
Laurent polynomials sum_{e=-2..2} c_e t^e on five values of t and checked on every other value; the
fitted elements are then checked on s(t) itself at 40 values of t (the conditions are polynomial
identities in t of bounded degree, so enough values prove them).  Writes ISODIR/stab_lwh_Qt.json and
ISODIR/curve_lwh_Qt.json (entries as {exponent: coefficient}) and prints the group structure.

  fit_family.py CLASSDIR ISODIR [AGARWAL_ISO.json]
"""
import json, os, sys
from collections import Counter
from fractions import Fraction as Fr
D = '/Users/greg/projects/logic/matmul/dps48'
sys.path.insert(0, D); sys.path.insert(0, os.path.join(D, 'rfc2610'))
import stab_family as SF, lwh_transport as LT  # noqa: E402

def tag(t):
    return str(t).replace('/', 'o').replace('-', 'm')

TS_STAB = [Fr(1, 2), Fr(1), Fr(2), Fr(4), Fr(8), Fr(1, 3), Fr(3), Fr(3, 2), Fr(2, 3), Fr(5), Fr(1, 5)]
TS_CURVE = [Fr(1, 2), Fr(1), Fr(2), Fr(4), Fr(8), Fr(1, 3), Fr(3)]
TS_NEG = [Fr(1, 2), Fr(1), Fr(2), Fr(4), Fr(8), Fr(1, 3), Fr(3), Fr(3, 2), Fr(2, 3)]
EXPS = (-2, -1, 0, 1, 2)


def mats(e, names='XYZ'):
    return [[[Fr(x) for x in r] for r in e[n]] for n in names]


def solve(A, b):
    n = len(A)
    M = [A[i][:] + [b[i]] for i in range(n)]
    for c in range(n):
        p = next(i for i in range(c, n) if M[i][c] != 0)
        M[c], M[p] = M[p], M[c]
        M[c] = [x / M[c][c] for x in M[c]]
        for i in range(n):
            if i != c and M[i][c] != 0:
                f = M[i][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[c])]
    return [M[i][n] for i in range(n)]


def fit(series, fit_ts, check_ts, exps=EXPS):
    """series: {t: list of three 4x4 matrices}.  Returns three 4x4 matrices of Laurent dicts, or None."""
    allt = fit_ts + check_ts
    A = [[t ** e for e in exps] for t in fit_ts]
    out = []
    for m in range(3):
        M = None
        for pos in [(i, j) for i in range(4) for j in range(4) if all(series[t][m][i][j] != 0 for t in allt)]:
            nrm = {t: [[x / series[t][m][pos[0]][pos[1]] for x in r] for r in series[t][m]] for t in allt}
            M = []
            for i in range(4):
                row = []
                for j in range(4):
                    c = solve(A, [nrm[t][i][j] for t in fit_ts])
                    if any(sum(ci * t ** e for ci, e in zip(c, exps)) != nrm[t][i][j] for t in check_ts):
                        row = None
                        break
                    row.append({e: ci for ci, e in zip(c, exps) if ci != 0})
                if row is None:
                    M = None
                    break
                M.append(row)
            if M is not None:
                break
        if M is None:
            return None
        out.append(M)
    return out


def ev(M, t):
    return [[sum(c * t ** e for e, c in p.items()) for p in r] for r in M]


def show(p):
    if not p:
        return "0"
    s = ""
    for e in sorted(p, reverse=True):
        c = p[e]
        mon = "" if e == 0 else ("t" if e == 1 else f"t^{e}" if e > 0 else f"t^({e})")
        cs = str(abs(c))
        term = cs if not mon else (mon if abs(c) == 1 else f"{cs}*{mon}")
        s += (" - " if c < 0 else " + ") + term if s else ("-" if c < 0 else "") + term
    return s


def main():
    classdir, isodir = sys.argv[1], sys.argv[2]
    at = SF.rebuild(classdir)
    tests = sorted({Fr(s * n, d) for s in (1, -1) for n in range(1, 11) for d in (1, 3)})
    res = {}
    for kind, ts, tgt in (("stab", TS_STAB, lambda t: t), ("curve", TS_CURVE, lambda t: 1 / (16 * t)), ("neg", TS_NEG, lambda t: -t)):
        data = {t: {(e['slot'], tuple(e['pi'])): e for e in json.load(open(os.path.join(isodir, f"{kind}_{tag(t)}.json")))} for t in ts}
        keys = set.intersection(*[set(d) for d in data.values()])
        print(f"{kind}: sizes {[len(data[t]) for t in ts]} at t = {[str(t) for t in ts]}; "
              f"slot map + layer permutation common to all: {len(keys)}", flush=True)
        els = []
        for k in sorted(keys):
            f = fit({t: mats(data[t][k]) for t in ts}, ts[:5], ts[5:])
            assert f is not None, f"{kind} {k[0]}: not Laurent of degree <= 2 after scaling"
            fu = fit({t: mats(data[t][k], 'UVW') for t in ts}, ts[:5], ts[5:])
            els.append(dict(slot=k[0], act=data[ts[0]][k]['act'], pi=list(k[1]), X=f[0], Y=f[1], Z=f[2],
                            U=fu[0] if fu else None, V=fu[1] if fu else None, W=fu[2] if fu else None))
        bad = []
        for e in els:
            for t in tests:
                g = dict(slot=e['slot'], pi=e['pi'], X=ev(e['X'], t), Y=ev(e['Y'], t), Z=ev(e['Z'], t))
                try:
                    ok = SF.carries(g, at(t), at(tgt(t)))
                except StopIteration:
                    ok = False
                if not ok:
                    bad.append((e['slot'], str(t)))
        degs = Counter(max((abs(x) for r in M for p in r for x in p), default=0) for e in els for M in (e['X'], e['Y'], e['Z']))
        print(f"  fitted {len(els)} elements, Laurent degrees used {dict(sorted(degs.items()))}; "
              f"checked on s(t) at {len(tests)} values of t: {len(els) * len(tests) - len(bad)} pass, failures {bad[:6]}", flush=True)
        const = sum(all(set(p) <= {0} for M in (e['X'], e['Y'], e['Z']) for r in M for p in r) for e in els)
        print(f"  elements with X, Y, Z all constant in t: {const}; X constant: {sum(all(set(p) <= {0} for r in e['X'] for p in r) for e in els)}, "
              f"Y constant: {sum(all(set(p) <= {0} for r in e['Y'] for p in r) for e in els)}, "
              f"Z constant: {sum(all(set(p) <= {0} for r in e['Z'] for p in r) for e in els)}", flush=True)
        nu = sum(e['U'] is not None for e in els)
        badu = []
        for e in els:
            if e['U'] is None:
                continue
            for t in tests:
                g = dict(slot=e['slot'], pi=e['pi'], X=LT.inv(LT.T(ev(e['U'], t))), Y=LT.inv(LT.T(ev(e['V'], t))), Z=LT.inv(LT.T(ev(e['W'], t))))
                try:
                    ok = SF.carries(g, at(t), at(tgt(t)))
                except StopIteration:
                    ok = False
                if not ok:
                    badu.append((e['slot'], str(t)))
        print(f"  Lemma 2.1 form (U, V, W) = (X^-T, Y^-T, Z^-T) up to scale: Laurent of degree <= 2 for {nu} of {len(els)}; "
              f"checked on s(t) at {len(tests)} values: failures {badu[:6]}", flush=True)
        res[kind] = els
        json.dump([dict(slot=e['slot'], act=e['act'], pi=e['pi'], **{n: [[{str(k): str(v) for k, v in p.items()} for p in r] for r in e[n]] for n in 'XYZUVW' if e[n] is not None},
                        text={n: [[show(p) for p in r] for r in e[n]] for n in 'XYZUVW' if e[n] is not None}) for e in els],
                  open(os.path.join(isodir, f"{kind}_lwh_Qt.json"), 'w'), indent=0)
    q = {(e['slot'], tuple(e['pi'])): e for e in json.load(open(os.path.join(isodir, "stab_1o4.json")))}
    for kind in ("stab", "curve"):
        hit = 0
        for e in res[kind]:
            k = (e['slot'], tuple(e['pi']))
            if k in q:
                m = mats(q[k])
                f = [ev(M, Fr(1, 4)) for M in (e['X'], e['Y'], e['Z'])]
                hit += all(LT.ratio(a, b) for a, b in zip(m, f))
        print(f"at t = 1/4 the fitted {kind} elements are elements of Stab(s(1/4)): {hit} of {len(res[kind])}")
    G = [dict(slot=e['slot'], pi=tuple(e['pi']), mono=[False] * 3, orth=[False] * 3) for e in res['stab']]
    Gam = G + [dict(slot=e['slot'], pi=tuple(e['pi']), mono=[False] * 3, orth=[False] * 3) for e in res['curve']]
    print(f"stab and curve layer permutations together = those of Stab(s(1/4)): {set(e['pi'] for e in Gam) == set(k[1] for k in q)}")
    SF.structure("generic stabilizer G of s(t) over Q(t)", G, print)
    SF.structure("trivial-slot subgroup of G", [e for e in G if e['slot'] == 'id'], print)
    SF.structure("G with the curve map t -> 1/(16t): order-64 group, = Stab(s(1/4)) at t = 1/4", Gam, print)
    gap = lambda p: "(" + ")(".join(",".join(str(i + 1) for i in c) for c in cycles(p) if len(c) > 1) + ")"
    Neg = [dict(slot=e['slot'], pi=tuple(e['pi']), mono=[False] * 3, orth=[False] * 3) for e in res['neg']]
    full = SF.closure([e['pi'] for e in Gam + Neg], tuple(range(48)))
    slot_of = {e['pi']: e['slot'] for e in Gam + Neg}
    print(f"group generated by the stabilizer, the t -> 1/(16t) maps and the t -> -t maps: order {len(full)}; "
          f"its elements realize t -> t, 1/(16t), -t, -1/(16t) on the curve")
    Full = [dict(slot=slot_of.get(p, '?'), pi=p, mono=[False] * 3, orth=[False] * 3) for p in sorted(full)]
    SF.structure("the whole symmetry group of the curve (order 128 expected)", Full, print)
    for nm, els in (("G", G), ("Gamma", Gam), ("Full", Full)):
        _, gens = SF.structure(nm + " (generators)", els, lambda s: None)
        print(f"GAP: {nm} := Group({', '.join(gap(p) for p in gens)});")
    if len(sys.argv) > 3:
        ag = [dict(slot=e['slot'], pi=tuple(e['pi']), mono=e['mono'], orth=[False] * 3) for e in json.load(open(sys.argv[3]))]
        _, gens = SF.structure("Agarwal", ag, print)
        print(f"GAP: Agarwal := Group({', '.join(gap(p) for p in gens)});")


def cycles(p):
    seen, out = set(), []
    for k in range(48):
        if k in seen:
            continue
        c, j = [], k
        while j not in seen:
            seen.add(j); c.append(j); j = p[j]
        out.append(c)
    return out


if __name__ == "__main__":
    main()
