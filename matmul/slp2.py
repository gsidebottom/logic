#!/usr/bin/env python3
"""Upgraded additive-complexity optimizer (v2): kernel intersections +
output reuse, with whole-SLP symbolic verification.

Moves, chosen greedily by saving with temperature/tie randomization:
  KERNEL  extract a signed common sub-sum I (|I| >= 2) shared by k >= 2
          forms: costs |I|-1 adds once, saves |I|-1 in each of k forms
          -> saving (k-1)(|I|-1). (Pair extraction is the |I|=2 case.)
  REUSE   compute form f_i as sigma*F_j + d where d = f_i - sigma*f_j:
          saving |f_i| - |d| - 1 when positive; reuse edges must stay
          acyclic (DAG check). This is the DPS "compute rows from other
          rows" trick, which is where the C-side slack lives.

Cost model: binary adds/subs counted, negation and (here) no non-unit
constants — ternary schemes only. Verification: the emitted SLP (all
auxiliary definitions + final form expressions) is expanded symbolically
over the base variables and must reproduce every original form exactly.

Usage:
  python3 slp2.py --bits FILE [--dims 3,3,3,23] [--models 8]
                  [--restarts 200] [--temp 0.15] [--emit out.slp]
"""
import random
import sys

USE_KERN = True
USE_REUSE = True
KERN_MIN_K = 2
SCORE_K_FIRST = False
from itertools import combinations

from brent import var_counts, verify_bits
from lift import lift_models


# ---------------- core optimizer ----------------

def optimize(forms0, rng=None, temp=0.0, use_kern=True, use_reuse=True):
    """forms0: list of dict sym->+-1 over base symbols ('v', idx).
    Returns (adds, assigns, finals):
      assigns: list of (aux_sym, [(sym, +-1), ...]) in creation order
      finals:  list of [(sym, +-1), ...] per form (syms may include aux
               ('w', i) and form refs ('F', j))."""
    forms = [dict(f) for f in forms0]
    n = len(forms)
    assigns = []
    reuse_edges = {i: set() for i in range(n)}  # i uses F_j: edge j->i

    def reaches(a, b, seen=None):
        # is there a path a -> b in reuse graph (j->i edges)?
        if a == b:
            return True
        if seen is None:
            seen = set()
        for i in range(n):
            if a in reuse_edges[i] and i not in seen:
                seen.add(i)
                if reaches(i, b, seen):
                    return True
        return False

    def canon_kernel(items):
        items = sorted(items, key=lambda kv: str(kv[0]))
        if items[0][1] < 0:
            items = [(s, -c) for s, c in items]
        return tuple(items)

    while True:
        cands = []
        seen_k = {}
        # PAIR candidates with true global counts (v1 granularity —
        # essential: big kernels usually appear in only 2 forms, while
        # a sub-pair may appear in many; the pool must contain both)
        pair_counts = {}
        for f in forms:
            ks = [s for s in f
                  if not (isinstance(s, tuple) and s[0] == "F")]
            ks.sort(key=str)
            for u, v in combinations(ks, 2):
                key = canon_kernel([(u, f[u]), (v, f[v])])
                pair_counts[key] = pair_counts.get(key, 0) + 1
        for key, k in pair_counts.items():
            if k >= 2:
                seen_k[key] = True
                sv = (k - 1) * 1000 + 1 if SCORE_K_FIRST else k - 1
                cands.append((sv, 0, ("kern", key)))
        # KERNEL candidates from maximal pairwise intersections
        if not use_kern:
            pass  # pair candidates above already collected
        for i, j in (combinations(range(n), 2) if use_kern else []):
            fi, fj = forms[i], forms[j]
            if len(fi) < 2 or len(fj) < 2:
                continue
            for sgn in (1, -1):
                # F (output-reuse) symbols are excluded from kernels:
                # a kernel containing F_j substituted back into form j
                # would create a reference cycle (caught by verify()).
                inter = [(s, c) for s, c in fi.items()
                         if fj.get(s) == sgn * c
                         and not (isinstance(s, tuple) and s[0] == "F")]
                if len(inter) < 2:
                    continue
                key = canon_kernel(inter)
                if key in seen_k:
                    continue
                # count containing forms (either global sign)
                k = 0
                for f in forms:
                    if len(f) < len(key):
                        continue
                    if all(f.get(s) == c for s, c in key) or \
                       all(f.get(s) == -c for s, c in key):
                        k += 1
                if k >= KERN_MIN_K:
                    saving = (k - 1) * (len(key) - 1)
                    if SCORE_K_FIRST:
                        saving = (k - 1) * 1000 + (len(key) - 1)
                    seen_k[key] = True
                    cands.append((saving, 0, ("kern", key)))
        # REUSE candidates
        for i in (range(n) if use_reuse else []):
            for j in range(n):
                if i == j or len(forms[j]) < 2:
                    continue
                # skip if would create a cycle: i -> ... -> j exists?
                if reaches(i, j):
                    continue
                fi, fj = forms[i], forms[j]
                for sgn in (1, -1):
                    d = dict(fi)
                    ok = True
                    for s, c in fj.items():
                        nv = d.get(s, 0) - sgn * c
                        if nv == 0:
                            d.pop(s, None)
                        elif nv in (1, -1):
                            d[s] = nv
                        else:
                            ok = False
                            break
                    if not ok:
                        continue
                    saving = len(fi) - (len(d) + 1)
                    if saving > 0:
                        sv = saving * 1000 if SCORE_K_FIRST else saving
                        cands.append((sv, 1,
                                      ("reuse", i, j, sgn, d)))
        if not cands:
            break
        cands.sort(key=lambda x: -x[0])
        pick = 0
        if rng is not None:
            best = cands[0][0]
            pool = [c for c in cands if c[0] == best]
            if temp > 0 and len(cands) > len(pool) and rng.random() < temp:
                pick = rng.randrange(min(len(cands), 3 * len(pool)))
            else:
                pick = rng.randrange(len(pool))
        saving, _, move = cands[pick]
        if move[0] == "kern":
            key = move[1]
            w = ("w", len(assigns))
            assigns.append((w, list(key)))
            for f in forms:
                if all(f.get(s) == c for s, c in key):
                    for s, _ in key:
                        del f[s]
                    f[w] = 1
                elif all(f.get(s) == -c for s, c in key):
                    for s, _ in key:
                        del f[s]
                    f[w] = -1
        else:
            _, i, j, sgn, d = move
            nf = dict(d)
            nf[("F", j)] = sgn
            forms[i] = nf
            reuse_edges[i].add(j)

    adds = sum(len(rhs) - 1 for _, rhs in assigns)
    adds += sum(max(len(f) - 1, 0) for f in forms)
    finals = [sorted(f.items(), key=lambda kv: str(kv[0]))
              for f in forms]
    return adds, assigns, finals


def verify(forms0, assigns, finals):
    """expand the emitted SLP over base symbols; must equal forms0."""
    table = {}
    for w, rhs in assigns:
        acc = {}
        for s, c in rhs:
            sub = table.get(s, {s: 1})
            for b, bc in sub.items():
                acc[b] = acc.get(b, 0) + c * bc
        table[w] = {b: c for b, c in acc.items() if c}
    # form expansions in reuse-DAG order (iterate until stable)
    expanded = [None] * len(finals)

    def expand_form(i, stack):
        if expanded[i] is not None:
            return expanded[i]
        assert i not in stack, "reuse cycle!"
        stack.add(i)
        acc = {}
        for s, c in finals[i]:
            if isinstance(s, tuple) and s[0] == "F":
                sub = expand_form(s[1], stack)
            else:
                sub = table.get(s, {s: 1})
            for b, bc in sub.items():
                acc[b] = acc.get(b, 0) + c * bc
        stack.discard(i)
        expanded[i] = {b: c for b, c in acc.items() if c}
        return expanded[i]

    for i, f0 in enumerate(forms0):
        got = expand_form(i, set())
        assert got == dict(f0), f"form {i}: {got} != {dict(f0)}"
    return True


# ---------------- scheme plumbing ----------------

def forms_of(bits, signs, dims):
    n1, n2, n3, r = dims
    na, nb, ng = var_counts(*dims)
    sa, sb, sg = n1 * n2, n2 * n3, n1 * n3
    fa = [{("v", k): signs[m * sa + k] for k in range(sa)
           if bits[m * sa + k]} for m in range(r)]
    fb = [{("v", k): signs[na + m * sb + k] for k in range(sb)
           if bits[na + m * sb + k]} for m in range(r)]
    fc = []
    for pq in range(sg):
        fc.append({("v", m): signs[na + nb + m * sg + pq]
                   for m in range(r) if bits[na + nb + m * sg + pq]})
    return fa, fb, fc


def best2(bits, dims, nmodels=8, restarts=200, temp=0.15, seed=0):
    models = lift_models(bits, nmodels, dims)
    if not models:
        return None
    best = None
    for mi, (signs, _) in enumerate(models):
        fa, fb, fc = forms_of(bits, signs, dims)
        for rr in range(restarts):
            rng = random.Random(seed * 7919 + mi * 653 + rr) if rr else None
            parts = []
            for forms in (fa, fb, fc):
                adds, assigns, finals = optimize(
                    forms, rng, temp if rr else 0.0,
                    use_kern=USE_KERN, use_reuse=USE_REUSE)
                verify(forms, assigns, finals)
                parts.append(adds)
            tot = sum(parts)
            if best is None or tot < best[0]:
                best = (tot, tuple(parts), mi)
    return best


def main():
    argv = sys.argv[1:]

    def opt(name, default, cast):
        if name in argv:
            i = argv.index(name)
            v = cast(argv[i + 1])
            del argv[i:i + 2]
            return v
        return default

    dims = tuple(int(x)
                 for x in opt("--dims", "3,3,3,23", str).split(","))
    nmodels = opt("--models", 8, int)
    restarts = opt("--restarts", 200, int)
    temp = opt("--temp", 0.15, float)
    global USE_KERN, USE_REUSE, KERN_MIN_K, SCORE_K_FIRST
    if "--kern-min-k" in argv:
        i = argv.index("--kern-min-k")
        KERN_MIN_K = int(argv[i + 1])
        del argv[i:i + 2]
    if "--score-k-first" in argv:
        SCORE_K_FIRST = True
        argv.remove("--score-k-first")
    if "--no-kern" in argv:
        USE_KERN = False
        argv.remove("--no-kern")
    if "--no-reuse" in argv:
        USE_REUSE = False
        argv.remove("--no-reuse")
    paths = [a for a in argv if not a.startswith("--")]
    print(f"{'scheme':30s} {'support':>7s} {'v2-CSE':>7s}  (A+B+C, model)"
          f"   [{nmodels} models x {restarts} restarts, temp {temp}]")
    for p in paths:
        bits = [int(c) for c in open(p).read().split()[-1].strip()]
        assert verify_bits(bits, *dims) == 0
        res = best2(bits, dims, nmodels, restarts, temp)
        if res is None:
            print(f"{p}: not liftable")
            continue
        tot, parts, mi = res
        print(f"{p.split('/')[-1]:30s} {sum(bits):7d} {tot:7d}  "
              f"({parts[0]}+{parts[1]}+{parts[2]}, m{mi})", flush=True)


if __name__ == "__main__":
    main()
