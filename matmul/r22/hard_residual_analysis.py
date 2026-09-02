#!/usr/bin/env python3
"""Study of the depth-5/6 pure-side-A residuals of the t=16 deep probe
(matmul/r22/hard_residuals.txt, from schemesearch3 --probe-pool --dump-hard):
3-4 active A-slices (9x9 each over F2), target 11/10. "hard" = every floor
(flatten, strassen, koszul<=4) fails; "leaf" = koszul settles it.
What distinguishes them? Slice-span rank profile, common kernels, pencil
sub-structure.  (2026-09-02)"""
import sys, itertools
from collections import Counter, defaultdict

def rank(rows):
    rows = list(rows); rk = 0
    for c in range(8, -1, -1):
        piv = next((i for i in range(rk, len(rows)) if rows[i] >> c & 1), None)
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        for i in range(len(rows)):
            if i != rk and rows[i] >> c & 1:
                rows[i] ^= rows[rk]
        rk += 1
    return rk

def transpose(m):
    t = [0] * 9
    for i in range(9):
        for j in range(9):
            if m[i] >> j & 1:
                t[j] |= 1 << i
    return t

def kernel_dim(m):          # right kernel of 9x9
    return 9 - rank(m)

def common_kernel_dim(slices):   # vectors x with M x = 0 for all M: stack rows
    return 9 - rank([r for m in slices for r in m])

def parse(path):
    out = []
    import re
    pat = re.compile(r"(\w+) depth (\d+) target (\d+) folds (\S+) flatten \[([^\]]*)\] koszul (\d+) slices (.*)")
    for line in open(path):
        m = pat.match(line.strip())
        if not m:
            continue
        kind, depth, target, folds, flat, kos, rest = m.groups()
        slices = []
        for tok in rest.split():
            slices.append([int(tok[3 * j:3 * j + 3], 16) for j in range(9)])
        out.append((kind, int(depth), int(target), int(kos), slices, folds))
    return out

def profile(slices):
    k = len(slices)
    combos = []
    for mask in range(1, 1 << k):
        m = [0] * 9
        for i in range(k):
            if mask >> i & 1:
                m = [a ^ b for a, b in zip(m, slices[i])]
        combos.append(rank(m))
    ck = common_kernel_dim(slices)
    clk = common_kernel_dim([transpose(m) for m in slices])
    # span of all row spaces / column spaces
    rowspan = rank([r for m in slices for r in m])
    colspan = rank([r for m in slices for r in transpose(m)])
    return {
        'k': k,
        'combo_max': max(combos),
        'combo_min': min(combos),
        'n_full': sum(1 for c in combos if c == max(combos)),
        'combo_hist': tuple(sorted(Counter(combos).items())),
        'common_ker': ck,
        'common_coker': clk,
        'rowspan': rowspan,
        'colspan': colspan,
    }

def main():
    path = sys.argv[1] if len(sys.argv) > 1 else 'matmul/r22/hard_residuals.txt'
    data = parse(path)
    print(f"records: {len(data)}")
    # dedupe by slices
    seen = {}
    for rec in data:
        key = (rec[0], tuple(tuple(m) for m in rec[4]))
        seen.setdefault(key, rec)
    print(f"distinct: {len(seen)}")
    by = defaultdict(list)
    for (kind, _), rec in seen.items():
        by[(kind, rec[1])].append(rec)
    for (kind, depth), recs in sorted(by.items()):
        print(f"\n=== {kind} depth {depth} target {recs[0][2]} n={len(recs)}")
        profs = [profile(r[4]) for r in recs]
        for key in ['combo_max', 'combo_min', 'n_full', 'common_ker', 'common_coker', 'rowspan', 'colspan']:
            c = Counter(p[key] for p in profs)
            print(f"  {key:13s} {dict(sorted(c.items()))}")
        c = Counter(p['combo_hist'] for p in profs)
        print("  top combo-rank histograms:")
        for h, n in c.most_common(6):
            print(f"    {n:5d}  {h}")
        c = Counter(r[3] for r in recs)
        print(f"  koszul values {dict(sorted(c.items()))}")
        # slice-rank multiset
        c = Counter(tuple(sorted(rank(m) for m in r[4])) for r in recs)
        print(f"  slice ranks {dict(c.most_common(6))}")

if __name__ == '__main__':
    main()
