#!/usr/bin/env python3
"""After canon_enum.py: every (c_L, c_R, c_P) reachable from maximal selections; and the distinct P's with
many canonical columns.  P depends only on modes X and Z: A rows and C^-1 columns.  A selection that fixes
all four rows of A and all four columns of C^-1 gives P up to diagonal scalings, so the classes are finite.

  canon_classes.py PREFIX CANON.json OUT.json
"""
import sys
src = open('/Users/greg/projects/logic/matmul/dps48/rfc2610/canon_enum.py').read()
sys.argv = [sys.argv[0], sys.argv[1], '/dev/null', sys.argv[2], sys.argv[3]] if len(sys.argv) > 3 else sys.argv
exec(src[:src.index('t = time.time()')])
OUTF = sys.argv[4]
tri = Counter()
for x in range(len(sel["X"])):
    for y in range(len(sel["Y"])):
        l = int(LT[x, y])
        r = RT[y]; p = PT[:, x]
        c = Counter(zip(r.tolist(), p.tolist()))
        for (rr, pp), n in c.items(): tri[(l, rr, pp)] += n
print(f"{len(tri)} distinct (c_L, c_R, c_P) from maximal selections; those with c_P >= 8 or sum >= 24:")
rows = sorted(tri.items(), key=lambda kv: (-kv[0][2], -sum(kv[0]), kv[0]))
for k, v in rows:
    if k[2] >= 8 and sum(k) >= 22 or sum(k) >= 24: print(f"   {k}  sum {sum(k)}: {v}")
print("P side: number of (mode Z, mode X) selection pairs by canonical columns:", sorted(Counter(PT.ravel().tolist()).items(), reverse=True))
# reduce to distinct P: use full bases only
inv = lambda M: np.linalg.inv(M)
def key(col_mask, row_mask, cols, rows_):
    return tuple(i for i in range(8) if (col_mask >> i) & 1), tuple(i for i in range(8) if (row_mask >> i) & 1)
Wn = np.array([[[float(x) for x in r] for r in w] for w in W])
seen = {}
und = 0
for z, (sz, qz) in enumerate(sel["Z"]):
    for x, (sx, qx) in enumerate(sel["X"]):
        n = int(PT[z, x])
        if n < 8: continue
        S = [col["Z"][i] for i in range(8) if (sz >> i) & 1]; Q = [row["X"][i] for i in range(8) if (qx >> i) & 1]
        if len(S) != 4 or len(Q) != 4: und += 1; continue
        Ci = np.array(S, float).T; A = np.array(Q, float)
        Wp = np.linalg.inv(Ci) @ Wn @ np.linalg.inv(A)
        # scale each column to first nonzero 1, compare as a set of patterns under row/column order of C and A
        nzp = sum(int(np.count_nonzero(np.abs(w) > 1e-9)) for w in Wp)
        pat = sorted(tuple(sorted(np.count_nonzero(np.abs(w) > 1e-9, axis=0).tolist())) + tuple(sorted(np.count_nonzero(np.abs(w) > 1e-9, axis=1).tolist())) for w in Wp)
        k = (n, nzp, tuple(pat))
        seen.setdefault(k, []).append((z, x))
print(f"selection pairs with >= 8 canonical but an underdetermined basis: {und}")
print(f"distinct P patterns with full bases: {len(seen)}")
for k, v in sorted(seen.items(), key=lambda kv: (-kv[0][0], kv[0][1])):
    print(f"   c_P {k[0]}  nnz {k[1]}  pairs {len(v)}  first {v[0]}")
json.dump([[k[0], k[1], v] for k, v in seen.items()], open(OUTF, 'w'))
