#!/usr/bin/env python3
"""First pass at the stabilizer of the Li-Wang-Hu family s(t) (A. Sedoglavic, 2026-11-11: 'the stabilizer of the
family and of Agarwal's decompositions'): which isotropies with CONSTANT matrices fix every s(t).  Result: only 2 (the
identity and one involution); the other 30 elements of each Stab(s(t)) have the same layer permutations at every t but a
t-dependent third matrix, so the stabilizer of the family lives over Q(t) -- fit_family.py builds it.  This module also
holds the helpers fit_family.py uses (rebuild, carries, structure, closure).

Reads the members classes/s_{1o4,1o2,1,2,4,8} (lwh_family.py sms output; cyclic reading
sum U_k (x) V_k (x) W_k = sum e_ij (x) e_jl (x) e_li) and their stabilizers as written by
stab_matrices.py (every element: slot map, layer permutation pi, X, Y, Z exactly), and
 1. rebuilds s(t) exactly: every entry is a/t + b + c t, fitted on t = 1/2, 1, 2 and checked
    on t = 1/4, 4, 8, with phi(s(t)) = 64 + 4/t^2 + 1024 t^2 as a control;
 2. intersects the five generic stabilizers (t = 1/2 .. 8): the elements (slot map, pi, and
    X, Y, Z up to scale) common to all of them;
 3. checks every common element on s(t) at many t (each condition is a Laurent polynomial
    identity with exponents in [-3, 3], so 7 nonzero values of t already prove it);
 4. checks every element of Stab(s(1/4)) outside the common group against the curve map
    t -> 1/(16 t), the symmetry behind phi(t) = phi(1/(16 t)), and t -> -t;
 5. reports the group structure (element orders, centre, derived and Frattini subgroups,
    number of generators, conjugacy classes) and the orbits on the 48 components, for each
    JSON given on the command line (Agarwal's included).

  stab_family.py CLASSDIR STABDIR [EXTRA.json ...]
STABDIR holds stab_s_<t>.json for the six members; writes STABDIR/stab_lwh_family.json (the
common group) and STABDIR/stab_lwh_curve_map.json (the elements realizing t -> 1/(16 t)).
"""
import functools, json, math, os, sys
from collections import Counter
from fractions import Fraction as Fr
D = '/Users/greg/projects/logic/matmul/dps48'; sys.path.insert(0, D)
import lwh_family as F, lwh_transport as LT  # noqa: E402

TS = [('s_1o4', Fr(1, 4)), ('s_1o2', Fr(1, 2)), ('s_1', Fr(1)), ('s_2', Fr(2)), ('s_4', Fr(4)), ('s_8', Fr(8))]


def cyc(prefix):
    U, V, W = F.read_lrp(prefix)
    return (U, V, [LT.T(M) for M in W])


def solve3(rows, rhs):
    A = [r[:] + [v] for r, v in zip(rows, rhs)]
    for c in range(3):
        p = next(i for i in range(c, 3) if A[i][c] != 0)
        A[c], A[p] = A[p], A[c]
        A[c] = [x / A[c][c] for x in A[c]]
        for i in range(3):
            if i != c and A[i][c] != 0:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[c])]
    return [A[i][3] for i in range(3)]


def rebuild(classdir):
    mem = {t: cyc(os.path.join(classdir, n)) for n, t in TS}
    fit_t = [Fr(1, 2), Fr(1), Fr(2)]
    rows = [[1 / t, Fr(1), t] for t in fit_t]
    coef = [[[[solve3(rows, [mem[t][f][k][i][j] for t in fit_t]) for j in range(4)] for i in range(4)]
             for k in range(48)] for f in range(3)]

    def at(t):
        return tuple([[[a / t + b + c * t for (a, b, c) in row] for row in coef[f][k]] for k in range(48)]
                     for f in range(3))
    for n, t in TS:
        assert at(t) == tuple(mem[t]), f"{n}: not a/t + b + c t entrywise"
    return at


def norm(M):
    s = next(x for row in M for x in row if x != 0)
    return tuple(tuple(x / s for x in row) for row in M)


def load(path):
    out = []
    for e in json.load(open(path)):
        M = [[[Fr(x) for x in r] for r in e[n]] for n in 'XYZ']
        out.append(dict(slot=e['slot'], pi=tuple(e['pi']), X=M[0], Y=M[1], Z=M[2], mono=e['mono'], orth=e['orth'],
                        key=(e['slot'], tuple(e['pi'])) + tuple(norm(m) for m in M)))
    return out


def carries(e, S_from, S_to):
    """does e carry S_from onto S_to (layer k of the slot image onto layer pi[k], per-layer scalings)?"""
    U, V, W = dict(LT.s3_variants(S_from))[e['slot']]
    U2, V2, W2 = S_to
    X, Y, Z = e['X'], e['Y'], e['Z']
    Xi, Yi, Zi = LT.inv(X), LT.inv(Y), LT.inv(Z)
    for k in range(48):
        j = e['pi'][k]
        a = LT.ratio(U2[j], LT.mm(LT.mm(X, U[k]), Yi))
        b = LT.ratio(V2[j], LT.mm(LT.mm(Y, V[k]), Zi))
        if not a or not b or LT.ratio(W2[j], LT.mm(LT.mm(Z, W[k]), Xi)) != 1 / (a * b):
            return False
    return True


# ------------------------------------------------------------------ group structure from layer permutations
def comp(p, q):          # p after q
    return tuple(p[q[k]] for k in range(48))


def inverse(p):
    r = [0] * 48
    for k, j in enumerate(p):
        r[j] = k
    return tuple(r)


def order(p):
    seen, o = set(), 1
    for k in range(48):
        if k in seen:
            continue
        n, j = 0, k
        while j not in seen:
            seen.add(j); j = p[j]; n += 1
        o = math.lcm(o, n)
    return o


def closure(gens, ident):
    H, frontier = {ident}, [ident]
    while frontier:
        new = []
        for h in frontier:
            for g in gens:
                x = comp(g, h)
                if x not in H:
                    H.add(x); new.append(x)
        frontier = new
    return H


def structure(name, els, out):
    G = [e['pi'] for e in els]
    ident = tuple(range(48))
    Gs = set(G)
    out(f"--- {name}: order {len(G)}, distinct layer permutations {len(Gs)} (faithful on the 48 components: {len(Gs) == len(G)})")
    assert all(comp(p, q) in Gs for p in G for q in G), "not closed under composition"
    out(f"  closed under composition: yes;  slot maps {dict(Counter(e['slot'] for e in els))}")
    oc = Counter(order(p) for p in G)
    out(f"  element orders: {dict(sorted(oc.items()))}")
    for s in sorted({e['slot'] for e in els}):
        out(f"    slot map {s}: orders {dict(sorted(Counter(order(e['pi']) for e in els if e['slot'] == s).items()))}")
    Zc = [p for p in G if all(comp(p, q) == comp(q, p) for q in G)]
    comm = {comp(comp(inverse(p), inverse(q)), comp(p, q)) for p in G for q in G}
    Gd = closure(comm, ident)
    Phi = closure(comm | {comp(p, p) for p in G}, ident)
    d = round(math.log2(len(G) // len(Phi)))
    classes = len({frozenset(comp(comp(q, p), inverse(q)) for q in G) for p in G})
    ab = Counter()
    for p in G:          # orders in G / G'
        n, x = 1, p
        while x not in Gd:
            x = comp(p, x); n += 1
        ab[n] += 1
    out(f"  centre order {len(Zc)} (orders {dict(sorted(Counter(order(p) for p in Zc).items()))}); derived subgroup order {len(Gd)}; "
        f"abelian: {len(Gd) == 1}")
    out(f"  abelianization order {len(G) // len(Gd)}, element orders there {dict(sorted(Counter({k: v // len(Gd) for k, v in ab.items()}).items()))}; "
        f"Frattini order {len(Phi)}, minimal number of generators {d}; conjugacy classes {classes}")
    seen, orbs = set(), []
    for k in range(48):
        if k in seen:
            continue
        o = {p[k] for p in G}
        seen |= o
        orbs.append(sorted(o))
    out(f"  orbits on the 48 components: sizes {sorted(len(o) for o in orbs)}")
    gens = []
    H = {ident}
    for p in sorted(G, key=lambda p: (-order(p), p)):
        if p not in H:
            gens.append(p); H = closure(gens, ident)
        if len(H) == len(G):
            break
    out(f"  {len(gens)} generators suffice (greedy): orders {[order(p) for p in gens]}")
    return orbs, gens


def main():
    classdir, stabdir = sys.argv[1], sys.argv[2]
    lines = []

    def out(s):
        print(s, flush=True); lines.append(s)
    at = functools.lru_cache(maxsize=None)(rebuild(classdir))
    out("s(t) rebuilt: every entry a/t + b + c t, fitted on t = 1/2, 1, 2 and exact at 1/4, 4, 8")
    for t in (Fr(1, 3), Fr(3), Fr(-1, 2)):
        ph = F.phi(*at(t))[0]
        assert ph == 64 + 4 / t ** 2 + 1024 * t ** 2, (t, ph)
    out("  control: phi(s(t)) = 64 + 4/t^2 + 1024 t^2 at t = 1/3, 3, -1/2")
    st = {n: load(os.path.join(stabdir, f"stab_{n}.json")) for n, _ in TS}
    for n, t in TS:
        assert all(carries(e, at(t), at(t)) for e in st[n]), n
        out(f"  {n}: stabilizer order {len(st[n])}, slot maps {dict(Counter(e['slot'] for e in st[n]))}")
    gen_names = [n for n, _ in TS if n != 's_1o4']
    common = set.intersection(*[{e['key'] for e in st[n]} for n in gen_names])
    out(f"common to the five generic members t = 1/2, 1, 2, 4, 8 (same slot map, layer permutation, X, Y, Z up to scale): {len(common)}")
    for n in gen_names:
        out(f"  {n}: {sum(e['key'] in common for e in st[n])} of {len(st[n])} common")
    G = [e for e in st['s_1'] if e['key'] in common]
    q = st['s_1o4']
    out(f"  inside Stab(s(1/4)): {sum(e['key'] in common for e in q)} of {len(q)}")
    tests = sorted({Fr(s * n, d) for s in (1, -1) for n, d in ((1, 7), (1, 3), (2, 3), (1, 1), (5, 2), (7, 1))} | {Fr(1, 4), Fr(1, 16)})
    okG = [all(carries(e, at(t), at(t)) for t in tests) for e in G]
    out(f"  each common element fixes s(t) at all {len(tests)} test values of t (7 nonzero values prove it): {sum(okG)} of {len(G)}")
    rest = [e for e in q if e['key'] not in common]
    inv16 = [all(carries(e, at(t), at(1 / (16 * t))) for t in tests) for e in rest]
    neg = [all(carries(e, at(t), at(-t)) for t in tests) for e in rest]
    out(f"the {len(rest)} elements of Stab(s(1/4)) outside the common group: carry s(t) onto s(1/(16t)) for every test t: "
        f"{sum(inv16)};  onto s(-t): {sum(neg)}")
    negG = [all(carries(e, at(t), at(-t)) for t in tests) for e in G]
    out(f"  common elements carrying s(t) onto s(-t): {sum(negG)}")
    for nm, els in (("pointwise stabilizer of the family (common group)", G), ("Stab(s(1/4)) = curve-map extension", q)):
        structure(nm, els, out)
        out(f"  signed permutations in all three modes: {sum(all(e['mono']) for e in els)}; orthogonal up to scale in all three: "
            f"{sum(all(e['orth']) for e in els)}; per mode X/Y/Z signed permutations "
            f"{[sum(e['mono'][i] for e in els) for i in range(3)]}, orthogonal {[sum(e['orth'][i] for e in els) for i in range(3)]}")
    for path in sys.argv[3:]:
        els = load(path)
        structure(os.path.basename(path), els, out)
        out(f"  signed permutations in all three modes: {sum(all(e['mono']) for e in els)}; per mode X/Y/Z signed permutations "
            f"{[sum(e['mono'][i] for e in els) for i in range(3)]}, orthogonal {[sum(e['orth'][i] for e in els) for i in range(3)]}")
    s1 = json.load(open(os.path.join(stabdir, 'stab_s_1.json')))
    json.dump([r for r, e in zip(s1, st['s_1']) if e['key'] in common], open(os.path.join(stabdir, 'stab_lwh_family.json'), 'w'))
    s14 = json.load(open(os.path.join(stabdir, 'stab_s_1o4.json')))
    json.dump([r for r, e in zip(s14, q) if e['key'] not in common], open(os.path.join(stabdir, 'stab_lwh_curve_map.json'), 'w'))
    out("wrote stab_lwh_family.json (the common group, matrices as at t = 1) and stab_lwh_curve_map.json (Stab(s(1/4)) minus it)")


if __name__ == "__main__":
    main()
