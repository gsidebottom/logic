#!/usr/bin/env python3
"""Lift a mod-2 scheme to integer coefficients in {-1,0,+1} via sign-SAT.

Hypothesis (HKS's, which fails only rarely): a valid Z-scheme exists with
the same support and coefficients +-1. Encode: sign bit s_v per support
variable (sigma = (-1)^s); a covering term's sign is the XOR of its three
sign bits (t=1 <=> term = -1); the integer Brent equation
Sum_m sigma_a sigma_b sigma_g = delta over its k_e covering terms becomes
EXACTLY (k_e - rhs)/2 of the k_e term-bits equal 1. Per-product scaling
freedom (lambda, mu, (lambda mu)^-1) is broken by fixing the first alpha
and first beta support sign of every product to +.

SAT -> decode signs, verify the integer Brent equations EXACTLY over Z
(python ints), write the signed scheme. UNSAT -> not +-1-liftable
(reported; rare per HKS).

Usage: python3 lift.py scheme.bits [more.bits ...] [--outdir lifted]
"""
import functools
import itertools
import os
import subprocess
import sys
import tempfile

from brent import brent_equations, var_counts, verify_bits

DIMS3 = (3, 3, 3, 23)


@functools.lru_cache(maxsize=8)
def _geom(dims):
    """(EQS, NA, NB, NV, sizes (sa,sb,sg)) for a dims tuple."""
    n1, n2, n3, r = dims
    na, nb, ng = var_counts(n1, n2, n3, r)
    return (brent_equations(n1, n2, n3, r), na, nb, na + nb + ng,
            (n1 * n2, n2 * n3, n1 * n3))


def lift(bits, dims=DIMS3):
    """returns (signed_entries dict var->+-1, stats) or None if UNSAT."""
    models = lift_models(bits, 1, dims)
    return models[0] if models else None


def lift_models(bits, nmodels, dims=DIMS3):
    """up to `nmodels` distinct sign models, each (signs dict, stats).
    Distinct models are enforced by blocking clauses over the sign vars."""
    eqs, na, nb, nv, (sa, sb, sg) = _geom(tuple(dims))
    r_prod = dims[3]
    support = [v for v in range(nv) if bits[v]]
    svar = {v: i + 1 for i, v in enumerate(support)}  # DIMACS sign vars
    nxt = len(support) + 1
    clauses = []

    # normalization: first alpha + first beta support bit of each product +
    for m in range(r_prod):
        for base, size in ((m * sa, sa), (na + m * sb, sb)):
            for k in range(size):
                if bits[base + k]:
                    clauses.append([-svar[base + k]])
                    break

    # terms per equation
    nterms = 0
    for mons, rhs in eqs:
        terms = [(va, vb, vg) for va, vb, vg in mons
                 if bits[va] & bits[vb] & bits[vg]]
        k = len(terms)
        assert k % 2 == rhs, "scheme must satisfy mod-2 Brent"
        if k == 0:
            continue
        # aux var per term: t = sa ^ sb ^ sg
        tvars = []
        for (va, vb, vg) in terms:
            t = nxt
            nxt += 1
            tvars.append(t)
            trip = (svar[va], svar[vb], svar[vg])
            for pat in itertools.product((1, -1), repeat=3):
                # t must equal the XOR of the three sign bits: for each
                # of the 8 patterns, forbid t != parity(#true)
                par = sum(1 for x in pat if x > 0) & 1
                clauses.append(
                    [-x * s for x, s in zip(pat, trip)]
                    + [t if par else -t])
        nterms += k
        n1 = (k - rhs) // 2  # exactly n1 term-bits = 1 (negative terms)
        for sub in itertools.combinations(tvars, n1 + 1):
            clauses.append([-t for t in sub])
        for sub in itertools.combinations(tvars, k - n1 + 1):
            clauses.append(list(sub))

    out = []
    blocking: list = []
    for _ in range(nmodels):
        with tempfile.NamedTemporaryFile(
                "w", suffix=".cnf", delete=False) as f:
            f.write(f"p cnf {nxt - 1} {len(clauses) + len(blocking)}\n")
            for c in clauses + blocking:
                f.write(" ".join(map(str, c)) + " 0\n")
            path = f.name
        r = subprocess.run(["kissat", "-q", path], capture_output=True,
                           text=True)
        os.unlink(path)
        if "s UNSATISFIABLE" in r.stdout:
            break
        assert "s SATISFIABLE" in r.stdout, r.stdout[-500:]
        model = set()
        for line in r.stdout.splitlines():
            if line.startswith("v"):
                for tok in line.split()[1:]:
                    x = int(tok)
                    if x > 0:
                        model.add(x)
        signs = {}
        for v in support:
            signs[v] = -1 if svar[v] in model else 1
        out.append((signs, (len(support), nterms, len(clauses))))
        # block this sign assignment (over sign vars only)
        blocking.append([-s if s in model else s
                         for s in (svar[v] for v in support)])
    return out


def z_verify(bits, signs, dims=DIMS3):
    """exact integer Brent check with coefficients in {-1,0,1}."""
    eqs, _, _, nv, _ = _geom(tuple(dims))
    coef = [signs.get(v, 0) if bits[v] else 0 for v in range(nv)]
    bad = 0
    for mons, rhs in eqs:
        tot = 0
        for va, vb, vg in mons:
            tot += coef[va] * coef[vb] * coef[vg]
        if tot != rhs:
            bad += 1
    return bad


def pretty(bits, signs, name, dims=DIMS3):
    n1, n2, n3, r = dims
    _, na, nb, _, (sa, sb, sg) = _geom(tuple(dims))
    out = [f"# {name}: {n1}x{n2}x{n3} r={r} integer scheme, coefficients "
           "in {-1,0,+1}, lifted from mod-2 by sign-SAT"]

    def ent(base, i, j, ncols, sym):
        v = base + i * ncols + j
        if not bits[v]:
            return None
        s = "-" if signs[v] == -1 else "+"
        return f"{s}{sym}{i + 1}{j + 1}"

    for m in range(r):
        al = [x for i in range(n1) for j in range(n2)
              if (x := ent(m * sa, i, j, n2, "a"))]
        be = [x for i in range(n2) for j in range(n3)
              if (x := ent(na + m * sb, i, j, n3, "b"))]
        out.append(f"M{m + 1} = ({' '.join(al)}) * ({' '.join(be)})")
    for i in range(n1):
        for j in range(n3):
            cs = []
            for m in range(r):
                v = na + nb + m * sg + i * n3 + j
                if bits[v]:
                    cs.append(f"{'-' if signs[v] == -1 else '+'}M{m + 1}")
            out.append(f"C{i + 1}{j + 1} = {' '.join(cs)}")
    return "\n".join(out) + "\n"


def main():
    argv = sys.argv[1:]
    outdir = "lifted"
    dims = DIMS3
    if "--outdir" in argv:
        i = argv.index("--outdir")
        outdir = argv[i + 1]
        argv = argv[:i] + argv[i + 2:]
    if "--dims" in argv:
        i = argv.index("--dims")
        dims = tuple(int(x) for x in argv[i + 1].split(","))
        argv = argv[:i] + argv[i + 2:]
    args = [a for a in argv if not a.startswith("--")]
    os.makedirs(outdir, exist_ok=True)
    nlift = nfail = 0
    for path in args:
        s = open(path).read().split()[-1].strip()
        bits = [int(c) for c in s]
        assert verify_bits(bits, *dims) == 0, f"{path}: invalid mod-2"
        name = os.path.basename(path).replace(".bits", "")
        res = lift(bits, dims)
        if res is None:
            nfail += 1
            print(f"{name}: NOT +-1-liftable (sign-SAT UNSAT)", flush=True)
            continue
        signs, (ns, nt, nc) = res
        bad = z_verify(bits, signs, dims)
        assert bad == 0, f"{name}: LIFT BUG — {bad} integer equations fail"
        nlift += 1
        out = f"{outdir}/{name}.txt"
        open(out, "w").write(pretty(bits, signs, name, dims))
        print(f"{name}: LIFTED + Z-VERIFIED (support {ns}, {nt} terms, "
              f"{nc} clauses) -> {out}", flush=True)
    print(f"\n{nlift} lifted, {nfail} not +-1-liftable", flush=True)


if __name__ == "__main__":
    main()
