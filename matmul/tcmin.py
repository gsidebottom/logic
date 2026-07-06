#!/usr/bin/env python3
"""Exact output-side (C) additive minimizer via the transposition
principle — the tool that broke 56.

The C side computes 9 outputs from 23 products: a linear map W (9x23,
ternary).  Its additive cost is the shortest +-addition straight-line
program.  Greedy pair-extraction CSE (slp.py) only reaches an upper
bound (e.g. 29 on cn122).  The Tellegen / transposition principle says
that for an addition-only linear map,
    A(W) = A(W^T) + (inputs(W) - outputs(W)) = A(W^T) + (23 - 9)
         = A(W^T) + 14,
and W^T is a 9-input -> 23-output ternary map, i.e. EXACTLY the regime
the input-side minimizer sidemin.min_side solves exactly (and small:
A(W^T) ~ A(W) - 14 ~ 16, well within reach).  So
    exact C = sidemin(rows of W^T over 9 dims) + 14,
computed in milliseconds, and — crucially — CONSTRUCTIVE: transposing
the W^T chain (adjoint) yields an explicit A(W^T)+14-addition program
for the 9 outputs, which we emit and verify.

Combining exact input sides (sidemin) with exact C (this) found the
first sub-56 scheme: 55 = 13+14+28 on class i19w225c4efh (cn122).

Usage:
  tcmin.py selftest
  tcmin.py --bits FILE [--dims 3,3,3,23] [--models 24] [--emit out.slp]
"""
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from brent import var_counts, verify_bits
from lift import lift_models, z_verify
from slp import scheme_forms
from sidemin import min_side, form_vec, canon


# ---------------- transposition core ----------------

def c_transpose_rows(cforms, r):
    """the r rows of W^T (each a 9-vector over the 9 outputs)."""
    return [tuple(cforms[pq].get(m, 0) for pq in range(9)) for m in range(r)]


def c_min_exact(cforms, r, max_slack=6, node_cap=50_000_000):
    """exact C-side additive cost via transposition; returns
    (adds, sidemin_result) or (None, result) if the W^T search is open."""
    res = min_side(c_transpose_rows(cforms, r), 9, max_slack, node_cap)
    if res["status"] != "exact":
        return None, res
    return res["adds"] + (r - 9), res


def build_c_program(cforms, r):
    """transpose sidemin's W^T chain into an explicit C program.
    Returns (lines, couts, adds) — lines are 'cwK = x OP y', couts are
    'Cij = sym', adds is the binary-op count."""
    rows = c_transpose_rows(cforms, r)
    res = min_side(rows, 9, 6, 50_000_000)
    assert res["status"] == "exact", res["status"]
    v2w = {tuple(1 if t == i else 0 for t in range(9)): i for i in range(9)}
    ops = []
    nw = 9
    for (v, x, sx, y, sy) in res["chain"]:
        ops.append((v2w[x], sx, v2w[y], sy))
        v2w[v] = nw
        nw += 1
    taps = [None] * r
    for m in range(r):
        if any(rows[m]):
            c = canon(rows[m])
            taps[m] = (v2w[c], 1 if rows[m] == c else -1)
    ow = list(range(9, 9 + len(ops)))
    back = [[] for _ in range(nw)]     # each wire: list of (sign, symbol)
    for m, tp in enumerate(taps):
        if tp:
            back[tp[0]].append((tp[1], f"M{m + 1}"))
    lines, cw = [], 0

    def emit_sum(terms):
        nonlocal cw
        # fold list of (sign, symbol) into a +- chain; return final symbol
        cur_s, cur_y = terms[0]
        cur = cur_y if cur_s > 0 else f"-{cur_y}"
        for (s, y) in terms[1:]:
            nm = f"cw{cw}"
            cw += 1
            lines.append(f"{nm} = {cur} {'+' if s > 0 else '-'} {y}")
            cur = nm
        return cur

    for idx in range(len(ops) - 1, -1, -1):
        wi, si, wj, sj = ops[idx]
        k = ow[idx]
        if not back[k]:
            continue
        sym = emit_sum(back[k])
        back[wi].append((si, sym))
        back[wj].append((sj, sym))
    couts = []
    for i in range(9):
        sym = emit_sum(back[i]) if back[i] else "0"
        couts.append(f"C{i // 3 + 1}{i % 3 + 1} = {sym}")
    adds = sum(l.count(" + ") + l.count(" - ") for l in lines)
    return lines, couts, adds


# ---------------- exact whole-scheme scoring ----------------

def score_exact(bits, dims, nmodels):
    """min over sign models of exact A + exact B + exact C (transpose).
    Returns (total, A, B, C, model) or None."""
    n1, n2, n3, r = dims
    sa, sb = n1 * n2, n2 * n3
    best = None
    for mi, (signs, _) in enumerate(lift_models(bits, nmodels, dims)):
        assert z_verify(bits, signs, dims) == 0
        fa, fb, fc = scheme_forms(bits, signs, dims)
        ra = min_side([form_vec(f, sa) for f in fa], sa, 3, 20_000_000)
        rb = min_side([form_vec(f, sb) for f in fb], sb, 3, 20_000_000)
        if ra["status"] != "exact" or rb["status"] != "exact":
            continue
        C, _ = c_min_exact(fc, r)
        if C is None:
            continue
        tot = ra["adds"] + rb["adds"] + C
        if best is None or tot < best[0]:
            best = (tot, ra["adds"], rb["adds"], C, mi)
    return best


def emit_full_slp(bits, dims, model):
    """assemble the whole scheme's explicit SLP at a given sign model."""
    n1, n2, n3, r = dims
    sa, sb = n1 * n2, n2 * n3
    signs, _ = lift_models(bits, model + 1, dims)[model]
    assert z_verify(bits, signs, dims) == 0
    fa, fb, fc = scheme_forms(bits, signs, dims)
    anames = [f"a{i + 1}{j + 1}" for i in range(n1) for j in range(n2)]
    bnames = [f"b{i + 1}{j + 1}" for i in range(n2) for j in range(n3)]

    def side(forms, nb, names, pre, out):
        res = min_side([form_vec(f, nb) for f in forms], nb, 3, 20_000_000)
        assert res["status"] == "exact"
        nm = {tuple(1 if t == i else 0 for t in range(nb)): names[i]
              for i in range(nb)}
        L, w = [], 0
        for (v, x, sx, y, sy) in res["chain"]:
            s = f"{pre}w{w}"
            w += 1
            L.append(f"{s} = {'' if sx > 0 else '-'}{nm[x]} "
                     f"{'+' if sy > 0 else '-'} {nm[y]}")
            nm[v] = s
        O = []
        for k, f in enumerate(forms):
            row = form_vec(f, nb)
            if not any(row):
                O.append(f"{out}{k + 1} = 0")
            else:
                c = canon(row)
                O.append(f"{out}{k + 1} = {'' if row == c else '-'}{nm[c]}")
        return L, O, res["adds"]

    al, ao, nA = side(fa, sa, anames, "a", "P")
    bl, bo, nB = side(fb, sb, bnames, "b", "Q")
    cl, co, nC = build_c_program(fc, r)
    prog = [f"# {n1}x{n2}x{n3} r={r}: {nA}(A) + {nB}(B) + {nC}(C) = "
            f"{nA + nB + nC} additions; M_i = P_i * Q_i"]
    prog += ["## A-side"] + al + ao
    prog += ["## B-side"] + bl + bo
    prog += ["## products"] + [f"M{m + 1} = P{m + 1} * Q{m + 1}"
                               for m in range(r)]
    prog += ["## C-side"] + cl + co
    return "\n".join(prog) + "\n", (nA, nB, nC)


# ---------------- selftest ----------------

def selftest():
    # transposition constant on tiny addition-only maps
    def A(rows, nin):
        return min_side([tuple(x) for x in rows], nin, 6, 5_000_000)["adds"]
    cases = [([[1, 1, 0], [0, 1, 1]], 3, 2),
             ([[1, 1, 1]], 3, 1),
             ([[1, 1], [1, 1]], 2, 2),
             ([[1, -1, 0], [0, 1, -1], [1, 0, -1]], 3, 3)]
    for rowsM, nin, nout in cases:
        aM = A(rowsM, nin)
        MT = [[rowsM[o][i] for o in range(nout)] for i in range(nin)]
        aMT = A(MT, nout)
        assert aM == aMT + (nin - nout), (rowsM, aM, aMT)
    print("transposition constant: OK (4 tiny cases)")

    # reproduce known exact C: sun56 -> 30, cn122 -> 28
    base = __file__.rsplit("/", 1)[0]
    for rel, want_c in (("perminov_cache/bits/sun56.bits", 30),
                        ("external/i19-perminov56.bits", 28)):
        bits = [int(c) for c in
                open(f"{base}/{rel}").read().split()[-1].strip()]
        best_c = 10 ** 9
        for signs, _ in lift_models(bits, 24, (3, 3, 3, 23)):
            _, _, fc = scheme_forms(bits, signs, (3, 3, 3, 23))
            C, _ = c_min_exact(fc, 23)
            if C is not None:
                best_c = min(best_c, C)
        assert best_c == want_c, (rel, best_c, want_c)
        print(f"exact C {rel.split('/')[-1]}: {best_c} (want {want_c}) OK")
    print("tcmin selftest: ALL OK")


def main():
    argv = sys.argv[1:]
    if argv and argv[0] == "selftest":
        selftest()
        return

    def opt(name, default, cast=str):
        if name in argv:
            i = argv.index(name)
            v = cast(argv[i + 1])
            del argv[i:i + 2]
            return v
        return default

    dims = tuple(int(x) for x in opt("--dims", "3,3,3,23").split(","))
    nmodels = opt("--models", 24, int)
    emit = opt("--emit", None)
    paths = [a for a in argv if not a.startswith("--")]
    for p in paths:
        bits = [int(c) for c in open(p).read().split()[-1].strip()]
        assert verify_bits(bits, *dims) == 0
        best = score_exact(bits, dims, nmodels)
        if not best:
            print(f"{p}: not liftable / sides open")
            continue
        tot, A, B, C, mi = best
        name = p.split("/")[-1]
        flag = "   *** < 56 ***" if tot < 56 and dims == (3, 3, 3, 23) else ""
        print(f"{name:28s} EXACT {tot} = {A}+{B}+{C} (m{mi}){flag}")
        if emit:
            text, (nA, nB, nC) = emit_full_slp(bits, dims, mi)
            open(emit, "w").write(text)
            print(f"  emitted {nA + nB + nC}-addition SLP -> {emit}")


if __name__ == "__main__":
    main()
