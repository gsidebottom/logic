#!/usr/bin/env python3
"""Exact input-side additive minimizer (addition-chain covering).

A scheme's input side (say all 23 alpha rows) is a set of {-1,0,+1} forms
over the n1*n2 input cells.  Rows equal to a base cell, or to +-(another
row), are free; every other value costs one binary +- addition.  So the
side cost is the length of the shortest addition chain -- values built as
v = +-x +- y from earlier values, starting from the basis vectors --
whose value set contains every distinct multi-term row up to global sign
(Sun's chain-covering structure, arXiv:2604.27645).

Exact search = iterative deepening on the number of HELPERS h (chain
values that are not targets); optimum = #targets + h*.  Normal form,
complete by an exchange argument: since the pool only grows, covering a
creatable target early never hurts and always costs exactly one addition,
so greedily cover every creatable target and branch ONLY on helper
insertion at closure fixpoints.  With one helper left, the helper must
directly complete some uncovered target (else the fixpoint would not
move), which shrinks the last branching level to the "enabling" set.
Helpers may be arbitrary integer vectors (doubling allowed) -- strictly
more general than ternary-only or distinct-pair-only models, so a failure
at slack h here is a stronger impossibility than Sun's pure/aux1
certificates (selftest cross-checks agreement with his on his own U/V).

Usage:
  sidemin.py selftest
  sidemin.py --bits FILE [--dims 3,3,3,23] [--models 24] [--max-slack 3]
             [--c-restarts 120] [--seed 0]
"""
import sys
from itertools import combinations_with_replacement

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from brent import verify_bits
from lift import lift_models, z_verify
from slp import scheme_forms, greedy_slp, verify_slp


# ---------------- values ----------------

def canon(v):
    for x in v:
        if x > 0:
            return v
        if x < 0:
            return tuple(-y for y in v)
    return v


def vcomb(x, sx, y, sy):
    return tuple(sx * a + sy * b for a, b in zip(x, y))


def basis(n):
    return [tuple(1 if i == j else 0 for j in range(n)) for i in range(n)]


def derive(t, pool_list, pool_set):
    """t = sx*x + sy*y with x,y in pool (canon values)?  -> (x,sx,y,sy)"""
    for x in pool_list:
        for sx in (1, -1):
            r = tuple(t[i] - sx * x[i] for i in range(len(t)))
            if not any(r):
                continue
            cy = canon(r)
            if cy in pool_set:
                return (x, sx, cy, 1 if r == cy else -1)
    return None


class Budget(Exception):
    pass


def min_side(rows, nbase, max_slack=3, node_cap=2_000_000):
    """rows: iterable of coefficient tuples (any weight; weight<=1 and
    duplicate-up-to-sign rows are free).  Returns dict with keys
      nt, h, adds, chain, status ('exact' | 'open'), nodes
    chain = [(val, x, sx, y, sy), ...] in creation order; on 'open',
    adds is a LOWER bound (nt + max_slack + 1) and chain is None."""
    tset = []
    seen = set()
    for r in rows:
        c = canon(tuple(r))
        if sum(1 for x in c if x) <= 1 or c in seen:
            continue
        seen.add(c)
        tset.append(c)
    nt = len(tset)
    nodes = [0]

    def close(pool_list, pool_set, uncovered, order):
        progress = True
        while progress:
            progress = False
            for t in list(uncovered):
                d = derive(t, pool_list, pool_set)
                if d:
                    pool_list.append(t)
                    pool_set.add(t)
                    uncovered.discard(t)
                    order.append((t,) + d)
                    progress = True

    def enabling(pool_list, pool_set, uncovered):
        """values u not in pool s.t. some uncovered t = sx*x + sy*u."""
        out = {}
        for t in uncovered:
            for x in pool_list:
                for sx in (1, -1):
                    r = tuple(t[i] - sx * x[i] for i in range(len(t)))
                    if not any(r):
                        continue
                    u = canon(r)
                    if u not in pool_set:
                        out[u] = out.get(u, 0) + 1
        return out

    def creatable(pool_list, pool_set):
        out = set()
        for x, y in combinations_with_replacement(pool_list, 2):
            for sy in (1, -1):
                v = canon(vcomb(x, 1, y, sy))
                if any(v) and v not in pool_set:
                    out.add(v)
        return out

    def dfs(pool_list, pool_set, uncovered, order, h, memo):
        nodes[0] += 1
        if nodes[0] > node_cap:
            raise Budget
        close(pool_list, pool_set, uncovered, order)
        if not uncovered:
            return order
        if h == 0:
            return None
        key = frozenset(pool_set)
        if key in memo[h]:
            return None
        memo[h].add(key)
        enab = enabling(pool_list, pool_set, uncovered)
        if h == 1:
            cands = [u for u in enab]
        else:
            cands = list(creatable(pool_list, pool_set))
        cands.sort(key=lambda u: (-enab.get(u, 0),
                                  sum(1 for x in u if x), u))
        for u in cands:
            d = derive(u, pool_list, pool_set)
            if d is None:
                continue
            res = dfs(pool_list + [u], pool_set | {u},
                      set(uncovered), order + [(u,) + d], h - 1, memo)
            if res is not None:
                return res
        return None

    for h in range(max_slack + 1):
        memo = [set() for _ in range(h + 1)]
        pl = basis(nbase)
        try:
            res = dfs(list(pl), set(pl), set(tset), [], h, memo)
        except Budget:
            # levels < h were exhausted, so nt + h is a valid lower bound
            return {"nt": nt, "h": None, "adds": nt + h, "chain": None,
                    "status": "budget", "nodes": nodes[0]}
        if res is not None:
            assert len(res) == nt + h
            return {"nt": nt, "h": h, "adds": nt + h, "chain": res,
                    "status": "exact", "nodes": nodes[0]}
    return {"nt": nt, "h": None, "adds": nt + max_slack + 1, "chain": None,
            "status": "open", "nodes": nodes[0]}


def verify_chain(rows, nbase, chain):
    """replay: every step is a +-pair of earlier values; every multi-term
    row appears among chain values up to sign."""
    vals = set(basis(nbase))
    for (v, x, sx, y, sy) in chain:
        assert x in vals and y in vals, "operand not available"
        w = vcomb(x, sx, y, sy)
        assert canon(w) == v and v not in vals, "bad step"
        vals.add(v)
    for r in rows:
        c = canon(tuple(r))
        if sum(1 for x in c if x) >= 2:
            assert c in vals, f"row not covered: {r}"
    return True


# ---------------- scheme plumbing ----------------

def form_vec(f, n):
    v = [0] * n
    for k, c in f.items():
        v[k] = c
    return tuple(v)


def best_c(cforms, restarts, seed):
    import random
    best = None
    for rr in range(restarts):
        rng = random.Random(seed * 9176 + rr) if rr else None
        adds, trace = greedy_slp(cforms, rng)
        verify_slp(cforms, trace)
        if best is None or adds < best:
            best = adds
    return best


def emit_slp(path, bits, dims, ra, rb, fa, fb, fc, c_seed, c_restarts):
    """assemble a full SLP text: exact A/B side chains + best greedy C
    trace.  All parts are replay-verified before emission."""
    import random
    n1, n2, n3, r = dims
    sa, sb = n1 * n2, n2 * n3

    def cell(prefix, k, ncols):
        return f"{prefix}{k // ncols + 1}{k % ncols + 1}"

    def side_text(rr, rows, prefix, ncols, out_prefix):
        names = {}
        for i in range(len(rows[0])):
            v = tuple(1 if j == i else 0 for j in range(len(rows[0])))
            names[v] = cell(prefix, i, ncols)
        lines = []
        for wi, (v, x, sx, y, sy) in enumerate(rr["chain"]):
            nm = f"{prefix}w{wi}"
            sxs = "" if sx > 0 else "-"
            sys_ = "+" if sy > 0 else "-"
            lines.append(f"{nm} = {sxs}{names[x]} {sys_} {names[y]}")
            names[v] = nm
        outs = []
        for m, row in enumerate(rows):
            c = canon(row)
            if not any(row):
                outs.append(f"{out_prefix}{m+1} = 0")
            elif c in names:
                sign = "" if row == c else "-"
                outs.append(f"{out_prefix}{m+1} = {sign}{names[c]}")
            else:
                raise AssertionError("row not covered")
        return lines, outs

    best = None
    for rr in range(c_restarts):
        rng = random.Random(c_seed * 7717 + rr) if rr else None
        adds, trace = greedy_slp(fc, rng)
        verify_slp(fc, trace)
        if best is None or adds < best[0]:
            best = (adds, trace)
    c_adds, trace = best
    # rebuild C forms after substitutions to print outputs
    forms = [dict(f) for f in fc]
    cw = {}
    clines = []
    for wi, (w, u, su, v, sv) in enumerate(trace):
        def nm(s, sg):
            t = cw.get(s, f"M{s+1}" if isinstance(s, int) else None) or s
            return ("-" if sg < 0 else "+") + str(t)
        cw[w] = f"cw{wi}"
        clines.append(f"cw{wi} = {nm(u, su)[0:]} {nm(v, sv)}".replace(
            "= +", "= "))
        for f in forms:
            if f.get(u) == su and f.get(v) == sv:
                del f[u], f[v]
                f[w] = 1
            elif f.get(u) == -su and f.get(v) == -sv:
                del f[u], f[v]
                f[w] = -1
    couts = []
    sg_ = n1 * n3
    for pq in range(sg_):
        terms = []
        f = forms[pq]
        for s, c in sorted(f.items(), key=lambda kv: str(kv[0])):
            t = cw.get(s, f"M{s+1}" if isinstance(s, int) else str(s))
            terms.append(("+" if c > 0 else "-") + str(t))
        expr = " ".join(terms).lstrip("+") if terms else "0"
        couts.append(f"C{pq // n3 + 1}{pq % n3 + 1} = {expr}")

    va = [form_vec(f, sa) for f in fa]
    vb = [form_vec(f, sb) for f in fb]
    al, ao = side_text(ra, va, "a", n2, "P")
    bl, bo = side_text(rb, vb, "b", n3, "Q")
    tot = ra["adds"] + rb["adds"] + c_adds
    txt = [f"# {path}: {n1}x{n2}x{n3} r={r} — {tot} additions "
           f"= {ra['adds']} (A, exact) + {rb['adds']} (B, exact) "
           f"+ {c_adds} (C, greedy); M_i = P_i * Q_i",
           f"## A-side: {ra['adds']} additions"]
    txt += al + ao
    txt += [f"## B-side: {rb['adds']} additions"] + bl + bo
    txt += [f"## outputs: {c_adds} additions"] + clines + couts
    return "\n".join(txt) + "\n", tot


def run_scheme(path, dims, nmodels, max_slack, c_restarts, seed,
               emit=None):
    bits = [int(c) for c in open(path).read().split()[-1].strip()]
    assert verify_bits(bits, *dims) == 0
    n1, n2, n3, r = dims
    sa, sb = n1 * n2, n2 * n3
    models = lift_models(bits, nmodels, dims)
    if not models:
        print(f"{path}: not liftable")
        return None
    best = None
    for mi, (signs, _) in enumerate(models):
        assert z_verify(bits, signs, dims) == 0, f"model {mi} fails Z-verify"
        fa, fb, fc = scheme_forms(bits, signs, dims)
        ra = min_side([form_vec(f, sa) for f in fa], sa, max_slack)
        rb = min_side([form_vec(f, sb) for f in fb], sb, max_slack)
        if ra["chain"]:
            verify_chain([form_vec(f, sa) for f in fa], sa, ra["chain"])
        if rb["chain"]:
            verify_chain([form_vec(f, sb) for f in fb], sb, rb["chain"])
        c = best_c(fc, c_restarts, seed + mi)
        tot = ra["adds"] + rb["adds"] + c
        exact = ra["status"] == "exact" and rb["status"] == "exact"
        tag = "" if exact else " (sides open!)"
        print(f"  m{mi:<3d} A {ra['adds']:2d} (nt{ra['nt']}+h{ra['h']}) "
              f"B {rb['adds']:2d} (nt{rb['nt']}+h{rb['h']}) "
              f"C {c:2d} (heur)  total {tot}{tag}", flush=True)
        if best is None or tot < best[0]:
            best = (tot, mi, ra, rb, c)
    tot, mi, ra, rb, c = best
    name = path.split("/")[-1]
    print(f"{name:28s} BEST total {tot} = {ra['adds']}+{rb['adds']}+{c} "
          f"(m{mi}; sides exact, C heuristic)")
    if emit:
        signs = models[mi][0]
        fa, fb, fc = scheme_forms(bits, signs, dims)
        txt, etot = emit_slp(path, bits, dims, ra, rb, fa, fb, fc,
                             seed + mi, c_restarts)
        open(emit, "w").write(txt)
        print(f"  emitted {etot}-addition SLP -> {emit}")
    return best


# ---------------- selftest ----------------

def selftest():
    # micro cases: known optima
    e = basis(4)
    micro = [
        ([(1, 1, 0, 0)], 1, 0),
        ([(1, 1, 0, 0), (1, 1, 1, 0)], 2, 0),
        ([(1, 1, 1, 0)], 2, 1),
        ([(1, 1, 1, 1)], 3, 2),
        ([(1, -1, 0, 0), (0, 1, -1, 0), (1, 0, -1, 0)], 3, 0),
    ]
    for rows, adds, h in micro:
        r = min_side(rows, 4)
        assert (r["adds"], r["h"]) == (adds, h), (rows, r)
        verify_chain(rows, 4, r["chain"])
    print("micro cases: OK (5/5)")

    # Sun gates: his published U/V sides must come out 13 exactly,
    # with h*=1 (U: 12 targets) and h*=2 (V: 11 targets), matching his
    # pure-chain / one-aux impossibility certificates.
    sys.path.insert(0, __file__.rsplit("/", 1)[0] + "/perminov_cache")
    import sun_verify as sv
    for side, want_nt, want_h in (("U", 12, 1), ("V", 11, 2)):
        rows = sv.expand(sv.SIDES[side])
        r = min_side(rows, 9)
        assert r["status"] == "exact", r
        assert (r["nt"], r["h"], r["adds"]) == (want_nt, want_h, 13), \
            (side, r["nt"], r["h"], r["adds"])
        verify_chain(rows, 9, r["chain"])
        print(f"Sun {side}: nt={r['nt']} h*={r['h']} adds=13 "
              f"(chain verified; {r['nodes']} nodes)")
    opt = sv.optimality()
    assert opt["all_claimed_input_optimality_checks_pass"]
    assert not opt["U_pure_at_12_possible"]          # == our h=0 fail on U
    assert not opt["V_pure_at_11_possible"]          # == our h=0 fail on V
    assert not opt["V_aux1_at_12_possible"]          # == our h=1 fail on V
    print("Sun certificates: reproduced (pure/aux1 agree with our IDDFS)")
    print("selftest: ALL OK")


def main():
    argv = sys.argv[1:]
    if argv and argv[0] == "selftest":
        selftest()
        return

    def opt(name, default, cast):
        if name in argv:
            i = argv.index(name)
            v = cast(argv[i + 1])
            del argv[i:i + 2]
            return v
        return default

    dims = tuple(int(x) for x in opt("--dims", "3,3,3,23", str).split(","))
    nmodels = opt("--models", 24, int)
    max_slack = opt("--max-slack", 3, int)
    c_restarts = opt("--c-restarts", 120, int)
    seed = opt("--seed", 0, int)
    emit = opt("--emit", None, str)
    paths = [a for a in argv if not a.startswith("--")]
    for p in paths:
        print(f"== {p} (exact A/B sides, heuristic C; {nmodels} models)")
        run_scheme(p, dims, nmodels, max_slack, c_restarts, seed, emit)


if __name__ == "__main__":
    main()
