#!/usr/bin/env python3
"""exactlns: exact large-neighbourhood search over a PLinOpt straight-line
program (step 3).  Every window of W consecutive lines (in a valid order)
is a small linear map from the variables it reads to the variables it
produces for the rest of the program; qexact finds the cheapest program
for that map (PLinOpt cost model, scalars +-2, +-1/2, +-4, +-1/4); when it
is cheaper than the window, the window is replaced, the program re-ordered
and verified with SLPchecker -M against the matrix.  Passes repeat over
several window sizes until nothing improves.

Usage: exactlns.py --slp PROG.slp --sms MATRIX.sms --bin PLINOPT_BIN --out DIR
         [--windows 6,8,10,12] [--hmax 3] [--nodes 300000] [--seconds 20]
         [--passes 6]
"""
import argparse
import os
import re
import sys
import time
from fractions import Fraction as Fr

H = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, H)
import prune_loop as PL  # noqa: E402
import qexact as Q  # noqa: E402

TERM = re.compile(r"\s*([+-]?)\s*(\(?)([A-Za-z]\w*(?:\s*[+-]\s*[A-Za-z]\w*)*)(\)?)\s*(?:([*/])\s*(\d+))?\s*")


def eval_rhs(rhs, env):
    """vector (dict name->Fraction over program inputs) of an SLP expression.
    Grammar: terms joined by +/-; term = [-]ident[*k|/k] | [-](sum)/k | [-](sum)*k."""
    rhs = rhs.replace(" ", "")
    pos = 0
    total = {}
    sign = 1
    cost_add, cost_mul = 0, 0
    terms = 0
    while pos < len(rhs):
        if rhs[pos] in "+-":
            sign = -1 if rhs[pos] == "-" else 1
            pos += 1
            continue
        if rhs[pos] == "(":
            end = rhs.index(")", pos)
            inner = rhs[pos + 1:end]
            v, ca, cm = eval_rhs(inner, env)
            cost_add += ca
            cost_mul += cm
            pos = end + 1
            coef = Fr(1)
            if pos < len(rhs) and rhs[pos] in "*/":
                m = re.match(r"([*/])(\d+)", rhs[pos:])
                k = Fr(int(m.group(2)))
                coef = k if m.group(1) == "*" else 1 / k
                if k != 1:
                    cost_mul += 1
                pos += m.end()
            for n, x in v.items():
                total[n] = total.get(n, Fr(0)) + sign * coef * x
        else:
            m = re.match(r"([A-Za-z]\w*)(?:([*/])(\d+))?", rhs[pos:])
            name = m.group(1)
            coef = Fr(1)
            if m.group(2):
                k = Fr(int(m.group(3)))
                coef = k if m.group(2) == "*" else 1 / k
                if k != 1:
                    cost_mul += 1
            pos += m.end()
            v = env[name] if name in env else {name: Fr(1)}
            for n, x in v.items():
                total[n] = total.get(n, Fr(0)) + sign * coef * x
        terms += 1
        sign = 1
    total = {n: x for n, x in total.items() if x}
    return total, cost_add + max(terms - 1, 0), cost_mul


def line_cost(rhs):
    _, a, m = eval_rhs(rhs, {})
    return a + m


def program_vectors(lines):
    env = {}
    for lhs, rhs, _ in lines:
        v, _, _ = eval_rhs(rhs, env)
        env[lhs] = v
    return env


def to_local(vec_over_inputs, local_basis_vecs, local_names):
    """express a vector (dict over program inputs) in the local basis given
    as dicts; rational Gaussian elimination, free variables set to 0."""
    names = sorted({n for v in local_basis_vecs for n in v} | set(vec_over_inputs))
    idx = {n: i for i, n in enumerate(names)}
    k = len(local_basis_vecs)
    rows = [[Fr(0)] * (k + 1) for _ in names]
    for j, v in enumerate(local_basis_vecs):
        for n, x in v.items():
            rows[idx[n]][j] = x
    for n, x in vec_over_inputs.items():
        rows[idx[n]][k] = x
    # solve rows * c = rhs for c (k unknowns), equations = len(names)
    piv_cols = []
    r = 0
    for c in range(k):
        p = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        pv = rows[r][c]
        rows[r] = [x / pv for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [x - f * y for x, y in zip(rows[i], rows[r])]
        piv_cols.append(c)
        r += 1
    for i in range(r, len(rows)):
        if rows[i][k] != 0:
            return None  # not in the span
    sol = [Fr(0)] * k
    for i, c in enumerate(piv_cols):
        sol[c] = rows[i][k]
    return sol


def window_map(lines, start, W, env, outputs_needed):
    """targets of lines[start:start+W] over a maximal independent subset of
    its inputs (the local basis); the other inputs come back as free
    signals expressed in that basis.  Returns (basis_names, free_vectors,
    targets, cost) or None."""
    win = lines[start:start + W]
    defined = {l for l, _, _ in win}
    local_in = []
    for _, _, ops in win:
        for o in sorted(ops):
            if o not in defined and o not in local_in:
                local_in.append(o)
    later = lines[start + W:]
    outs = [l for l, _, _ in win if l in outputs_needed or any(l in ops for (_, _, ops) in later)]
    vec = lambda n: env[n] if n in env else {n: Fr(1)}
    basis_names, basis = [], []
    free = []
    for n in local_in:
        sol = to_local(vec(n), basis, basis_names) if basis else None
        if sol is None:
            basis_names.append(n)
            basis.append(vec(n))
        else:
            free.append(sol)
    free = [f + [Fr(0)] * (len(basis) - len(f)) for f in free]
    targets = {}
    for o in outs:
        sol = to_local(vec(o), basis, basis_names)
        if sol is None:
            return None
        targets[o] = sol
    cost = sum(line_cost(r) for _, r, _ in win)
    return basis_names, free, targets, cost


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--slp", required=True)
    ap.add_argument("--sms", required=True)
    ap.add_argument("--bin", required=True)
    ap.add_argument("--out", default="exactlns_out")
    ap.add_argument("--windows", default="6,8,10,12")
    ap.add_argument("--hmax", type=int, default=3)
    ap.add_argument("--nodes", type=int, default=300000)
    ap.add_argument("--seconds", type=float, default=20)
    ap.add_argument("--passes", type=int, default=6)
    ap.add_argument("--mode", default="window", help="window | pairs (mirabelle-style: definitions of two temporaries plus every line using them)")
    ap.add_argument("--maxsub", type=int, default=24, help="pairs mode: largest sub-program size")
    ap.add_argument("--plateau", type=float, default=0.0, help="probability of accepting an equal-cost rewrite (plateau move)")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--budget", type=float, default=0, help="stop after this many seconds (0 = no limit)")
    ap.add_argument("--maxtries", type=int, default=0, help="sub-programs examined per pass and mode (0 = all; bounds a plateau walk in pairs mode, where every move restarts the enumeration)")
    a = ap.parse_args()
    import random
    rng = random.Random(a.seed)
    Q.set_rng(rng if a.plateau > 0 else None)
    t_start = time.time()
    os.makedirs(a.out, exist_ok=True)
    env_os = dict(os.environ)
    sms = os.path.abspath(a.sms)
    program = PL.toposort(PL.parse(open(a.slp).read()))
    cur = PL.check(a.bin, sms, PL.emit(program), env_os)
    assert cur, "program does not verify"
    print(f"start: {cur[0]}+{cur[1]} = {sum(cur)} ops, {len(program)} lines", flush=True)
    outputs = {l for l, _, _ in program if l.startswith("o")}
    fresh_id = [0]

    def fresh():
        while True:
            fresh_id[0] += 1
            nm = f"q{fresh_id[0]}"
            if nm not in used:
                return nm

    improved_total = 0
    plateau_moves = [0]

    def sigset(prog):
        """the set of signals a program computes, up to sign (plateau moves
        must change this set; renaming or reordering lines is not a move)."""
        out = set()
        for name, v in program_vectors(prog).items():
            items = tuple(sorted((k, x) for k, x in v.items() if x))
            if not items:
                continue
            sg = -1 if items[0][1] < 0 else 1
            out.add(tuple((k, sg * x) for k, x in items))
        return out

    def subsets_pairs(prog):
        """mirabelle-style sub-programs: for each pair of temporaries, the
        indices of their defining lines and of every line using either
        (shuffled when the search is randomized)."""
        temps = [l for l, _, _ in prog if not l.startswith("o") and not l.startswith("i")]
        users = {}
        for i, (l, r, ops) in enumerate(prog):
            for o in ops:
                users.setdefault(o, set()).add(i)
        where = {l: i for i, (l, _, _) in enumerate(prog)}
        seen = set()
        keys = []
        for x in temps:
            for y in temps:
                if y <= x:
                    continue
                idx = {where[x], where[y]} | users.get(x, set()) | users.get(y, set())
                key = tuple(sorted(idx))
                if key in seen or len(key) > a.maxsub or len(key) < 3:
                    continue
                seen.add(key)
                keys.append(key)
        if a.plateau > 0:
            rng.shuffle(keys)
        return iter(keys)

    for ps in range(a.passes):
        gained = 0
        if a.mode == "pairs":
            schedule = [("pairs", None)]
        else:
            schedule = [("window", int(w)) for w in a.windows.split(",")]
        for mode, W in schedule:
            start = 0
            tries = 0
            pair_iter = subsets_pairs(program) if mode == "pairs" else None
            while True:
                tries += 1
                if (a.budget and time.time() - t_start > a.budget) or (a.maxtries and tries > a.maxtries):
                    break
                if mode == "pairs":
                    try:
                        idx = next(pair_iter)
                    except StopIteration:
                        break
                    # relocate the sub-program's lines to a contiguous block right after their last predecessor
                    block = [program[i] for i in idx]
                    rest = [ln for i, ln in enumerate(program) if i not in set(idx)]
                    program_view = rest[:min(idx)] + block + rest[min(idx):]
                    try:
                        program_view = PL.toposort(program_view)
                    except ValueError:
                        continue
                    names = {l for l, _, _ in block}
                    start = min(i for i, (l, _, _) in enumerate(program_view) if l in names)
                    W = max(i for i, (l, _, _) in enumerate(program_view) if l in names) - start + 1
                    if any(program_view[start + j][0] not in names for j in range(W)):
                        continue  # the relocated block did not stay contiguous
                    program_cur = program_view
                else:
                    if start + 2 > len(program):
                        break
                    program_cur = program
                used = {l for l, _, _ in program_cur}
                env = program_vectors(program_cur)
                wm = window_map(program_cur, start, W, env, outputs)
                if wm is None:
                    start += 1
                    continue
                local_in, free, targets, wcost = wm
                win_defined = {l for l, _, _ in program_cur[start:start + W]}
                free_names = [o for _, _, ops in program_cur[start:start + W] for o in sorted(ops) if o not in win_defined and o not in local_in]
                free_names = list(dict.fromkeys(free_names))
                m = len(local_in)
                freev = [tuple(int(x * Q.DEN) for x in f) for f in free]
                tv = []
                for o, sol in targets.items():
                    v = tuple(int(x * Q.DEN) if (x * Q.DEN).denominator == 1 else None for x in sol)
                    if any(x is None for x in v):
                        tv = None
                        break
                    tv.append(v)
                if tv is None or m == 0 or wcost <= 1:
                    start += 1
                    continue
                inkeys = {Q.norm(Q.unit(m, i))[0] for i in range(m)} | {Q.norm(f)[0] for f in freev if any(f)}
                ntar = len({Q.norm(t)[0] for t in tv if any(t)} - inkeys)
                helpers = wcost - ntar
                if helpers <= 0:
                    start += 1
                    continue
                t0 = time.time()
                hbudget = helpers - 1 if a.plateau <= 0 or rng.random() >= a.plateau else helpers
                res = Q.solve(m, tv, hmax=min(a.hmax, hbudget), node_cap=a.nodes, seconds=a.seconds, free=freev)
                if res is not None and (res[0] < wcost or (res[0] == wcost and hbudget == helpers)):
                    cost, prog = res
                    # emit: produce each program signal into a fresh temp, then free copies for the outputs
                    tn = {}
                    lines_new = []
                    name_of = {Q.norm(Q.unit(m, i))[0]: (local_in[i], 1) for i in range(m)}
                    for fi, f in enumerate(freev):
                        if any(f):
                            k, sg = Q.norm(f)
                            name_of.setdefault(k, (free_names[fi], sg))
                    for key, rec in prog:
                        nm = fresh()
                        used.add(nm)
                        if rec[0] == "scale":
                            _, av, c = rec
                            an, asg = name_of[Q.norm(av)[0]]
                            coef = Fr(c) * asg
                            lines_new.append((nm, Q.fmt_scale(an, coef)))
                        else:
                            _, av, sa, bv, sb = rec
                            an, asg = name_of[Q.norm(av)[0]]
                            bn, bsg = name_of[Q.norm(bv)[0]]
                            lines_new.append((nm, Q.fmt_sum(an, sa * asg, bn, sb * bsg)))
                        name_of[key] = (nm, 1)
                    ok = True
                    for o, sol in targets.items():
                        v = tuple(int(x * Q.DEN) for x in sol)
                        if not any(v):
                            lines_new.append((o, "0"))
                            continue
                        key, sg = Q.norm(v)
                        if key not in name_of:
                            ok = False
                            break
                        an, asg = name_of[key]
                        lines_new.append((o, ("-" if sg * asg < 0 else "") + an))
                    if not ok:
                        start += 1
                        continue
                    keep = program_cur[:start] + program_cur[start + W:]
                    new_lines = [(l, r, {t for t in PL.IDENT.findall(r)}) for l, r in lines_new]
                    try:
                        cand = PL.toposort(keep + new_lines)
                    except ValueError:
                        start += 1
                        continue
                    res2 = PL.check(a.bin, sms, PL.emit(cand), env_os)
                    if res2 and sum(res2) < sum(cur):
                        print(f"  pass {ps + 1} {mode} W={W} @{start}: sub-program {wcost} -> {cost} ops ({len(targets)} targets, {m} inputs, {time.time() - t0:.1f}s): total {sum(cur)} -> {sum(res2)}", flush=True)
                        program, cur = cand, res2
                        gained += 1
                        improved_total += 1
                        if mode == "pairs":
                            pair_iter = subsets_pairs(program)
                        continue  # re-examine
                    if res2 and sum(res2) == sum(cur) and sigset(cand) != sigset(program):
                        program = cand  # plateau move: a different signal set at the same cost
                        plateau_moves[0] += 1
                        if mode == "pairs":
                            pair_iter = subsets_pairs(program)
                if mode != "pairs":
                    start += 1
        open(os.path.join(a.out, f"pass{ps + 1}.slp"), "w").write(PL.emit(program))
        print(f"pass {ps + 1}: {gained} improvements, {plateau_moves[0]} plateau moves so far -> {cur[0]}+{cur[1]} = {sum(cur)} ops ({time.time() - t_start:.0f}s)", flush=True)
        if gained == 0 and a.plateau <= 0:
            break
        if a.budget and time.time() - t_start > a.budget:
            break
    open(os.path.join(a.out, "best.slp"), "w").write(PL.emit(program))
    print(f"final: {cur[0]}+{cur[1]} = {sum(cur)} ops ({improved_total} improvements) -> {a.out}/best.slp", flush=True)


if __name__ == "__main__":
    main()
