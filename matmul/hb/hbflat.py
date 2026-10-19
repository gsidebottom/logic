#!/usr/bin/env python3
"""Whole-orbit lower bound on the flat (no basis change) addition count of
3x3 rank-23 classes over F2: the 3x3 form of xor47 lbscan's cheap pass.

A representative costs c(A) + c(B) + c(C~) + 14 additions, where c(X) is
the fewest XORs computing the 23 nine-bit rows of leg X from the 9 inputs
(the output side counts transposed; 23 - 9 = 14).  Lower bound per leg:
the number of distinct non-unit rows, plus one when the closure of the
inputs under "add any target that is the XOR of two available signals"
misses a target (some gate must then compute a non-target).  A Z-program
reduced mod 2 never gets longer, so the bound holds over Z.

Under (P, Q, R) in GL(3,2)^3 the legs become P A Q^-1, Q B R^-1,
R C~ P^-1, so A depends on (P, Q), B on (Q, R), C~ on (R, P), and each
factor only through its LEFT coset of the permutation matrices: P -> pi P
permutes the rows of every P A Q^-1 and the columns of every R C~ P^-1
(P^-1 -> P^-1 pi^-1), the same way for all 23 rows, which leaves XOR
costs unchanged, and likewise for Q and R: 28 cosets
per factor, three 28x28 tables, min-plus over 28^3 triples.  Slot
symmetries permute the legs and leave the total unchanged, so one
variant covers the whole de Groote orbit.  The coset invariance is
checked on random elements before the tables are trusted.

Usage: hbflat.py BITS_TXT VERDICTS_CSV OUT_CSV [--jobs N] [--target 54]
       hbflat.py --one BITSFILE            (one scheme, verbose)
"""
import os
import random
import sys
import time
from concurrent.futures import ProcessPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)) + "/..")
from equiv import bits_to_summands, mat_inv, mat_mul, mat_rank  # noqa: E402

GL = [m for m in range(512) if mat_rank(m) == 3]
PERM = [m for m in GL if all(bin((m >> (3 * i)) & 7).count("1") == 1 for i in range(3)) and bin(m).count("1") == 3]
assert len(GL) == 168 and len(PERM) == 6
REP_OF = {}
for g in GL:
    if g not in REP_OF:
        coset = [mat_mul(p, g) for p in PERM]  # left coset: pi * g
        r = min(coset)
        for c in coset:
            REP_OF[c] = r
REPS = sorted(set(REP_OF.values()))
assert len(REPS) == 28
INV = {g: mat_inv(g) for g in GL}
POP = [bin(x).count("1") for x in range(512)]


def leg_rows(fam, left, right):
    return [mat_mul(mat_mul(left, m), right) for m in fam]


def tcount(rows):
    return len({x for x in rows if POP[x] >= 2})


def closure_misses(rows):
    rem = {x for x in rows if POP[x] >= 2}
    have = {1 << i for i in range(9)}
    grew = True
    while rem and grew:
        grew = False
        for t in list(rem):
            if any((t ^ c) in have for c in have):
                have.add(t)
                rem.discard(t)
                grew = True
    return 1 if rem else 0


def tables(summ, func):
    """three 28x28 tables of func(rows): A[p][q], B[q][r], C[r][p]."""
    fa, fb, fc = ([s[k] for s in summ] for k in range(3))
    n = len(REPS)
    ta = [[func(leg_rows(fa, REPS[p], INV[REPS[q]])) for q in range(n)] for p in range(n)]
    tb = [[func(leg_rows(fb, REPS[q], INV[REPS[r]])) for r in range(n)] for q in range(n)]
    tc = [[func(leg_rows(fc, REPS[r], INV[REPS[p]])) for p in range(n)] for r in range(n)]
    return ta, tb, tc


def minplus(ta, tb, tc, target):
    """orbit-wide minimum of A+B+C over coset triples, and the number of
    triples at or below target - 14."""
    n = len(REPS)
    best, cnt = 10**9, 0
    for p in range(n):
        for q in range(n):
            a = ta[p][q]
            rowb = tb[q]
            colc = tc
            for r in range(n):
                s = a + rowb[r] + colc[r][p]
                if s < best:
                    best = s
                if s + 14 <= target:
                    cnt += 1
    return best + 14, cnt


def gate(summ, rng):
    """coset invariance of both leg bounds on random elements."""
    fams = [[s[k] for s in summ] for k in range(3)]
    for _ in range(30):
        fam = rng.choice(fams)
        g, h, pi = rng.choice(GL), rng.choice(GL), rng.choice(PERM)
        base = leg_rows(fam, g, INV[h])
        v1 = leg_rows(fam, mat_mul(pi, g), INV[h])  # g -> pi g: row permutation
        v2 = leg_rows(fam, g, INV[mat_mul(pi, h)])  # h -> pi h: column permutation
        for v in (v1, v2):
            assert tcount(v) == tcount(base) and closure_misses(v) == closure_misses(base), "coset invariance gate failed"


def bound(bits, target=54, verbose=False):
    summ = bits_to_summands([int(c) for c in bits])
    ta, tb, tc = tables(summ, tcount)
    b1, c1 = minplus(ta, tb, tc, target)
    if verbose:
        print(f"  target counts alone: orbit bound {b1}, {c1} coset triples <= {target}")
    if b1 > target:
        return b1, b1, 0
    ca, cb, cc = tables(summ, closure_misses)
    n = len(REPS)
    ta2 = [[ta[p][q] + ca[p][q] for q in range(n)] for p in range(n)]
    tb2 = [[tb[q][r] + cb[q][r] for r in range(n)] for q in range(n)]
    tc2 = [[tc[r][p] + cc[r][p] for p in range(n)] for r in range(n)]
    b2, c2 = minplus(ta2, tb2, tc2, target)
    if verbose:
        print(f"  with closure bits: orbit bound {b2}, {c2} coset triples <= {target}")
    return b1, b2, c2


def work(item):
    cls, name, bits, floor2, target = item
    t0 = time.time()
    b1, b2, c2 = bound(bits, target)
    return cls, name, floor2, b1, b2, c2, time.time() - t0


def main():
    if sys.argv[1] == "--one":
        bits = open(sys.argv[2]).read().split()[-1].strip()
        assert len(bits) == 621
        rng = random.Random(1)
        gate(bits_to_summands([int(c) for c in bits]), rng)
        print("coset gate ok")
        t0 = time.time()
        b1, b2, c2 = bound(bits, int(sys.argv[3]) if len(sys.argv) > 3 else 54, verbose=True)
        print(f"orbit lower bound on the flat count: {b2} ({time.time() - t0:.1f} s)")
        return
    bits_txt, verdicts, out = sys.argv[1:4]
    jobs = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else 4
    target = int(sys.argv[sys.argv.index("--target") + 1]) if "--target" in sys.argv else 54
    bits = {}
    for ln in open(bits_txt):
        name, bs = ln.split()
        bits[name] = bs
    reps = {}
    for ln in open(verdicts):
        f = ln.rstrip("\n").split(",")
        if f[1] == "NEW" and f[2] not in reps:
            reps[f[2]] = (f[0], int(f[3]))
    done = set()
    if os.path.exists(out):
        done = {ln.split(",")[0] for ln in open(out) if not ln.startswith("class,")}
    else:
        open(out, "w").write("class,rep,floor2,bound_targets,bound_closure,triples_le_target,secs\n")
    items = [(cls, name, bits[name], fl, target) for cls, (name, fl) in sorted(reps.items(), key=lambda t: (t[1][1], t[0])) if cls not in done]
    first = bits_to_summands([int(c) for c in items[0][2]]) if items else None
    if first:
        gate(first, random.Random(7))
        print("coset gate ok on the first class", flush=True)
    print(f"{len(reps)} new classes; {len(items)} to bound ({len(done)} done); target {target}", flush=True)
    t0 = time.time()
    nlow = 0
    with ProcessPoolExecutor(max_workers=jobs) as ex:
        for i, (cls, name, floor2, b1, b2, c2, secs) in enumerate(ex.map(work, items, chunksize=4)):
            with open(out, "a") as f:
                f.write(f"{cls},{name},{floor2},{b1},{b2},{c2},{secs:.1f}\n")
            if b2 <= target:
                nlow += 1
                print(f"*** {cls} ({name}) floor2={floor2}: flat orbit bound {b2} <= {target} ({c2} coset triples)", flush=True)
            if (i + 1) % 100 == 0:
                print(f"  {i + 1}/{len(items)} classes, {nlow} with bound <= {target} ({time.time() - t0:.0f}s)", flush=True)
    print(f"done: {len(items)} classes, {nlow} with bound <= {target} ({time.time() - t0:.0f}s)", flush=True)


if __name__ == "__main__":
    main()
