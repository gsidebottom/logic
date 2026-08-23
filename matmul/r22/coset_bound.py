#!/usr/bin/env python3
"""Checker for the coset-counting rank lower bound over F_2.

  python3 matmul/r22/coset_bound.py [n]

Setting: a rank-r scheme for <n,n,n> is a set of r distinct rank-one
N x N matrices u_i = alpha_i (x) beta_i (N = n^2) whose span S contains
W = span{E_pq}, E_pq[(a,b),(c,d)] = [b=c][a=p][d=q] (gamma = the
coefficients). Let pi : S -> S/W, t = dim S/W <= r - N.

Argument (needs: no nonzero element of W has rank <= 2):
  * pi(u_i) != 0          (a rank-one matrix is not in W);
  * pi(u_i) != pi(u_j)    (else u_i + u_j in W \\ {0} has rank >= 3,
                           but rank(u_i + u_j) <= 2);
  so the r products inject into the 2^t - 1 nonzero cosets:
      r <= 2^t - 1 <= 2^(r-N) - 1.
For n = 3 this forces r >= 13. Over F_2 only (it counts cosets).

This script verifies the ingredients by exhaustive computation (dim W,
the rank distribution of all nonzero elements of W -- every element is
X (x) I_n with rank n*rank X -- and the absence of rank <= 2 elements)
and evaluates the inequality. For n = 2 the premise fails (W has
rank-2 elements), consistent with rank 7 existing.
"""
import sys


def rank_f2(rows):
    rows = [r for r in rows if r]
    rk = 0
    while rows:
        piv = max(rows)
        rows.remove(piv)
        rk += 1
        hb = piv.bit_length() - 1
        rows = [r ^ piv if (r >> hb) & 1 else r for r in rows]
        rows = [r for r in rows if r]
    return rk


def target_basis(n):
    N = n * n
    E = []
    for p in range(n):
        for q in range(n):
            rows = [0] * N
            for a in range(n):
                for b in range(n):
                    for c in range(n):
                        for d in range(n):
                            if b == c and a == p and d == q:
                                rows[a * n + b] |= 1 << (c * n + d)
            E.append(rows)
    return E


def main(n):
    N = n * n
    E = target_basis(n)
    flat = [sum(r << (i * N) for i, r in enumerate(rows)) for rows in E]
    dimW = rank_f2(flat)
    assert dimW == N, f"dim W = {dimW} != {N}"
    from collections import Counter
    cnt = Counter()
    for code in range(1, 1 << N):
        rows = [0] * N
        for k in range(N):
            if code >> k & 1:
                rows = [x ^ y for x, y in zip(rows, E[k])]
        cnt[rank_f2(rows)] += 1
    dist = dict(sorted(cnt.items()))
    minrank = min(dist)
    print(f"n={n}: dim W = {dimW}; ranks of the {2**N - 1} nonzero elements of W: {dist}")
    # every element should be X (x) I_n: ranks are multiples of n
    assert all(k % n == 0 for k in dist), "ranks not multiples of n"
    if minrank <= 2:
        print(f"  premise FAILS (W has rank-{minrank} elements): no coset bound for n={n}")
        return
    print(f"  premise holds: no element of W has rank <= 2 (min rank {minrank})")
    r = N
    while not (r <= 2 ** (r - N) - 1):
        r += 1
    print(f"  r <= 2^(r-{N}) - 1 first holds at r = {r}  =>  rank_F2(<{n},{n},{n}>) >= {r}")
    for rr in range(N, r):
        print(f"    r={rr}: {rr} <= 2^{rr - N} - 1 = {2 ** (rr - N) - 1}? no -> rank {rr} impossible")


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 3)
