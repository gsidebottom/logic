#!/usr/bin/env python3
"""Analysis of the adversary's winning frontier in the substitution game
(subgame --dump-frontier): every refuted state with depth, quotient dims,
target k and leaf value, plus the quotient tensor when a side has dim <= 4.

Question: at the frontier states, is the TRUE rank >= the target (then the
game is leaf-limited: a stronger small-tensor oracle would lift it) or
below it (then the adversary's kill was genuinely good and no leaf helps)?
Decided by SAT (cadical) on the compressed tensor: 'rank <= k-1' UNSAT =>
leaf-limited; SAT => genuine; TIMEOUT => unknown.  (2026-09-03)"""
import sys, os, re, random, time, subprocess
from collections import Counter, defaultdict
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tensor_sat import encode

PER_CLASS = int(os.environ.get("FRONTIER_PER_CLASS", "24"))
TMO = int(os.environ.get("FRONTIER_TMO", "60"))

pat = re.compile(r"(\w+) depth (\d+) dims (\d+),(\d+),(\d+) k (\d+) lb (\d+) leaf (\d+),(\d+),(\d+) u (\S*) v (\S*) x (\S*)(?: tensor (.*))?")

def rank(rows, n):
    rows = list(rows); rk = 0
    for c in range(n - 1, -1, -1):
        piv = next((i for i in range(rk, len(rows)) if rows[i] >> c & 1), None)
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        for i in range(len(rows)):
            if i != rk and rows[i] >> c & 1:
                rows[i] ^= rows[rk]
        rk += 1
    return rk

def rref_basis(vecs, n):
    rows = list(vecs); rk = 0
    for c in range(n - 1, -1, -1):
        piv = next((i for i in range(rk, len(rows)) if rows[i] >> c & 1), None)
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        for i in range(len(rows)):
            if i != rk and rows[i] >> c & 1:
                rows[i] ^= rows[rk]
        rk += 1
    return rows[:rk]

def coords(v, basis):
    out = 0
    for i, b in enumerate(basis):
        lb = b.bit_length() - 1
        if v >> lb & 1:
            v ^= b; out |= 1 << i
    assert v == 0
    return out

def parse(path):
    recs = []
    for line in open(path):
        m = pat.match(line.strip())
        if not m:
            continue
        kind, depth, da, db, dc, k, lb, l1, l2, l3, u, v, x, tens = m.groups()
        da, db, dc, k, lb = int(da), int(db), int(dc), int(k), int(lb)
        tensor = None
        if tens:
            toks = tens.split()
            tensor = [[int(tok[3 * b:3 * b + 3], 16) for b in range(db)] for tok in toks]  # t[a][b] mask over c
        recs.append(dict(kind=kind, depth=int(depth), dims=(da, db, dc), k=k, lb=lb, leaf=(int(l1), int(l2), int(l3)), tensor=tensor, u=u, v=v, x=x))
    return recs

def to_slices_min_side(t, da, db, dc):
    """return (k, slices) with the smallest side first; slices are k matrices given as rows (m rows of n bits)."""
    dims = [(da, 0), (db, 1), (dc, 2)]
    side = min(dims)[1]
    if side == 0:
        return da, [[t[a][b] for b in range(db)] for a in range(da)], db, dc          # A-slices: db x dc
    if side == 1:
        return db, [[t[a][b] for a in range(da)] for b in range(db)], da, dc          # B-slices: da x dc
    sl = []
    for c in range(dc):
        rows = []
        for a in range(da):
            r = 0
            for b in range(db):
                if t[a][b] >> c & 1:
                    r |= 1 << b
            rows.append(r)
        sl.append(rows)
    return dc, sl, da, db                                                            # C-slices: da x db

def compress(slices, m, n):
    Q = rref_basis([r for s in slices for r in s], n); rs = len(Q)
    A = [[coords(r, Q) for r in s] for s in slices]                                  # m x rs
    def transpose(rows, ncols):
        t = [0] * ncols
        for i, r in enumerate(rows):
            for j in range(ncols):
                if r >> j & 1:
                    t[j] |= 1 << i
        return t
    At = [transpose(a, rs) for a in A]                                                 # rs rows of m bits
    P = rref_basis([r for at in At for r in at], m); cs = len(P)
    C = [[coords(r, P) for r in at] for at in At]                                      # rs x cs
    X = [[0] * cs for _ in slices]
    for s in range(len(slices)):
        for l in range(rs):
            for j in range(cs):
                if C[s][l] >> j & 1:
                    X[s][j] |= 1 << l
    return X, cs, rs

def sat_rank_le(X, k, m, n, r, tmo):
    nn = max(m, n)
    Xp = [[X[s][j] if j < m else 0 for j in range(nn)] for s in range(k)]
    nv, cls = encode(Xp, k, nn, r)
    path = f"/tmp/fr_{os.getpid()}.cnf"
    with open(path, "w") as f:
        f.write(f"p cnf {nv} {len(cls)}\n")
        for c in cls:
            f.write(" ".join(map(str, c)) + " 0\n")
    t0 = time.time()
    try:
        out = subprocess.run(["cadical", "-q", path], capture_output=True, text=True, timeout=tmo)
        res = "SAT" if out.returncode == 10 else "UNSAT" if out.returncode == 20 else f"rc{out.returncode}"
    except subprocess.TimeoutExpired:
        res = "TIMEOUT"
    return res, time.time() - t0

def main():
    path = sys.argv[1]
    recs = parse(path)
    print(f"records: {len(recs)}")
    print("by kind:", dict(Counter(r['kind'] for r in recs)))
    finals = [r for r in recs if r['kind'] == 'final']
    print(f"\nfinal (all prover moves failed): {len(finals)}")
    c = Counter((r['depth'], tuple(sorted(r['dims'])), r['k'] - r['lb']) for r in finals)
    print("  (depth, sorted dims, gap k-lb) -> count, top 25:")
    for key, n in c.most_common(25):
        print(f"    {key}: {n}")
    c2 = Counter(r['k'] - r['lb'] for r in finals)
    print("  gap distribution:", dict(sorted(c2.items())))
    with_t = [r for r in finals if r['tensor'] is not None]
    print(f"\nfinal states with tensor (a side of dim <= 4): {len(with_t)}")
    # dedupe by tensor + k
    seen = {}
    for r in with_t:
        key = (tuple(tuple(row) for row in r['tensor']), r['k'])
        seen.setdefault(key, r)
    uniq = list(seen.values())
    print(f"distinct: {len(uniq)}")
    by = defaultdict(list)
    for r in uniq:
        by[(tuple(sorted(r['dims'])), r['k'])].append(r)
    random.seed(11)
    summary = []
    for (dims, k), rs in sorted(by.items(), key=lambda kv: (kv[0][0][0] * kv[0][0][1] * kv[0][0][2], kv[0][1])):
        sample = random.sample(rs, min(PER_CLASS, len(rs)))
        tally = Counter()
        times = []
        for r in sample:
            da, db, dc = r['dims']
            kk, slices, m, n = to_slices_min_side(r['tensor'], da, db, dc)
            X, cs, rsp = compress(slices, m, n)
            res, dt = sat_rank_le(X, kk, cs, rsp, k - 1, TMO)
            verdict = {"UNSAT": "leaf-limited (true rank >= k)", "SAT": "genuine (rank <= k-1)", "TIMEOUT": "unknown"}.get(res, res)
            tally[verdict] += 1
            times.append(dt)
            print(f"  dims {dims} k {k} lb {r['lb']} compressed {kk}x{cs}x{rsp}: rank<={k-1} {res} {dt:.1f}s", flush=True)
        summary.append((dims, k, len(rs), dict(tally), sum(times) / len(times)))
    print("\nSUMMARY per (sorted dims, k): total states, verdicts on the sample, mean SAT time")
    for dims, k, n, tally, mt in summary:
        print(f"  {dims} k={k}: {n} states; {tally}; {mt:.1f}s")

if __name__ == "__main__":
    main()
