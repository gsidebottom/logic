#!/usr/bin/env python3
"""Convert Perminov FastMatrixMultiplication 3x3x3 m=23 JSON schemes to our
621-bit mod-2 format, verifying everything along the way:

  1. expand reduced (CSE) forms back to full U/V/W over Z
  2. check ternary-ness of full coefficients (for _ZT files)
  3. verify Brent equations exactly over Z (both gamma orientations tried)
  4. for reduced files: independently recount the additive cost
     (cost = n_fresh + sum(len(expr)-1) per component; fresh vars must be
     2-term; negation free) and compare against the filename/complexity claim
  5. emit 621-bit vector (our brent.py order), cross-check brent.verify_bits==0

Writes bits to perminov_cache/bits/<tag>.bits and prints a report line each.
"""
import json
import sys
import itertools
import os

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))  # matmul/
from brent import verify_bits, brent_equations

REPO = os.path.join(HERE, "repo")
OUT = os.path.join(HERE, "bits")
os.makedirs(OUT, exist_ok=True)

EQS = brent_equations(3, 3, 3, 23)


def expand_expr(terms, nbase, fresh, cache):
    """terms: list of {'index','value'} -> dict base_idx -> int coeff."""
    vec = {}
    for t in terms:
        idx, val = t["index"], t["value"]
        if idx < nbase:
            vec[idx] = vec.get(idx, 0) + val
        else:
            sub = cache_get(idx, nbase, fresh, cache)
            for k, v in sub.items():
                vec[k] = vec.get(k, 0) + val * v
    return {k: v for k, v in vec.items() if v}


def cache_get(idx, nbase, fresh, cache):
    if idx not in cache:
        cache[idx] = expand_expr(fresh[idx - nbase], nbase, fresh, cache)
    return cache[idx]


def load_full(d):
    """full format: u,v,w each 23 rows x 9 ints (w product-major)."""
    U = [list(row) for row in d["u"]]
    V = [list(row) for row in d["v"]]
    Wp = [list(row) for row in d["w"]]  # per-product output coeffs
    assert len(U) == len(V) == len(Wp) == 23
    return U, V, Wp, None


def load_reduced(d):
    """reduced format: expand fresh vars.
    u,v: 23 exprs over 9+nf base/fresh vars; w: 9 output exprs over 23+nf."""
    nf_u, nf_v, nf_w = len(d["u_fresh"]), len(d["v_fresh"]), len(d["w_fresh"])
    U, V = [], []
    for key, base, out in (("u", 9, U), ("v", 9, V)):
        fresh = d[key + "_fresh"]
        cache = {}
        for expr in d[key]:
            vec = expand_expr(expr, base, fresh, cache)
            row = [0] * base
            for k, v in vec.items():
                row[k] = v
            out.append(row)
    # w: output-major (9 exprs over products 0..22 + fresh)
    cache = {}
    Wout = []
    for expr in d["w"]:
        vec = expand_expr(expr, 23, d["w_fresh"], cache)
        row = [0] * 23
        for k, v in vec.items():
            row[k] = v
        Wout.append(row)
    assert len(Wout) == 9
    # convert to product-major 23 x 9
    Wp = [[Wout[o][m] for o in range(9)] for m in range(23)]

    # --- independent additive-cost recount ---
    cost = 0
    for key in ("u", "v", "w"):
        fresh = d[key + "_fresh"]
        for f in fresh:
            assert len(f) == 2 and all(t["value"] in (-1, 1) for t in f), \
                f"fresh var in {key} not a 2-term +-1 pair: {f}"
        nterms = 0
        for expr in d[key]:
            assert len(expr) >= 1
            assert all(t["value"] in (-1, 1) for t in expr), expr
            nterms += len(expr) - 1
        cost += len(fresh) + nterms
    return U, V, Wp, cost


def z_brent_ok(U, V, G):
    """exact integer Brent check. G: product-major 23 x 9, entry k=p*3+q."""
    for (mons, rhs) in EQS_Z:
        pass  # unused; direct loop below


def brent_over_z(U, V, G):
    bad = 0
    for a, b in itertools.product(range(3), range(3)):
        for c, dd in itertools.product(range(3), range(3)):
            for p, q in itertools.product(range(3), range(3)):
                s = sum(U[m][a * 3 + b] * V[m][c * 3 + dd] * G[m][p * 3 + q]
                        for m in range(23))
                want = 1 if (b == c and a == p and dd == q) else 0
                bad += (s != want)
    return bad


def to_bits(U, V, G):
    bits = [0] * 621
    for m in range(23):
        for k in range(9):
            bits[m * 9 + k] = abs(U[m][k]) % 2
            bits[207 + m * 9 + k] = abs(V[m][k]) % 2
            bits[414 + m * 9 + k] = abs(G[m][k]) % 2
    return bits


def transpose9(row):
    return [row[(k % 3) * 3 + (k // 3)] for k in range(9)]


def process(path, tag):
    d = json.load(open(path))
    assert d.get("n") == [3, 3, 3] and d.get("m") == 23, path
    claimed = d.get("complexity")
    if "u_fresh" in d:
        U, V, Wp, recount = load_reduced(d)
    else:
        U, V, Wp, recount = load_full(d)

    maxc = max(abs(x) for row in (U + V + Wp) for x in row)
    ternary = maxc <= 1

    # gamma orientation: direct (w row entry k -> C[p,q], k=p*3+q) or transposed
    res = {}
    for name, G in (("direct", Wp), ("transposed", [transpose9(r) for r in Wp])):
        res[name] = brent_over_z(U, V, G)
    orient = min(res, key=res.get)
    zbad = res[orient]
    G = Wp if orient == "direct" else [transpose9(r) for r in Wp]

    bits = to_bits(U, V, G)
    m2bad = verify_bits(bits, 3, 3, 3, 23, EQS)
    support = sum(bits)

    ok = zbad == 0 and m2bad == 0
    line = (f"{tag:28s} Zbrent={zbad}({orient}) mod2={m2bad} "
            f"ternary={'Y' if ternary else 'N(max=%d)' % maxc} support={support}")
    if recount is not None:
        cl = claimed["reduced"] if isinstance(claimed, dict) else claimed
        line += f" recounted_adds={recount} claimed={cl} {'MATCH' if recount == cl else 'MISMATCH'}"
    elif claimed is not None:
        # full file: complexity = naive count; recount naive = sum over rows (nnz-1), incl. w product-major?
        # naive counts per component use expressions as computed: U rows, V rows, W output-major columns
        naive = 0
        for rows in (U, V):
            for r in rows:
                nz = sum(1 for x in r if x)
                naive += max(0, nz - 1)
        for o in range(9):
            nz = sum(1 for m in range(23) if Wp[m][o])
            naive += max(0, nz - 1)
        line += f" naive_recount={naive} claimed={claimed} {'MATCH' if naive == claimed else 'MISMATCH'}"
    print(line)
    if ok:
        with open(os.path.join(OUT, tag + ".bits"), "w") as f:
            f.write("".join(map(str, bits)) + "\n")
    return ok


EQS_Z = None  # unused placeholder

FILES = [
    ("schemes/known/a_60_addition/3x3x3_m23_additions60_ZT.json", "a60-stapleton"),
    ("schemes/known/alpha_tensor/3x3x3_m23_Z.json", "alphatensor-Z"),
    ("schemes/results/addition_reduced_ZT/3x3x3_m23_cr58_cn119_ZT_reduced.json", "cr58-cn119"),
    ("schemes/results/addition_reduced_ZT/3x3x3_m23_cr58_cn120_ZT_reduced.json", "cr58-cn120"),
    ("schemes/results/addition_reduced_ZT/3x3x3_m23_cr58_cn122_ZT_reduced.json", "cr58-cn122"),
    ("schemes/results/addition_reduced_ZT/3x3x3_m23_cr60_cn97_ZT_reduced.json", "cr60-cn97"),
    ("schemes/results/naive_addition_reduced_ZT/3x3x3_m23_c88_ZT.json", "naive88"),
    ("schemes/results/serendipitous_base/3x3x3_m23_8d34d377660f8f8d8b32cd4b6a1e1c40a5093dd0_ZT.json", "serendipitous139"),
]

if __name__ == "__main__":
    allok = True
    for rel, tag in FILES:
        allok &= process(os.path.join(REPO, rel), tag)
    print("ALL OK" if allok else "SOME FAILED")
