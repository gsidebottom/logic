#!/usr/bin/env python3
"""Rosowski 2019 commutative (non-bilinear) matmul schemes, implemented
from the formulas and GATED by exact evaluation — over Z and mod BabyBear.

Theorem 2 (n even, divisions-free, any commutative ring):
  <l,n,m> in n(lm+l+m-1)/2 multiplications.
Algorithm 1 (<n,3,3> = 6n+3): the 21-mult <3,3,3>.

Products mix A and B entries in both factors — legal for scalar
(commuting) entries, and legal as R1CS/AIR multiplication gates (a gate
multiplies two arbitrary linear forms over the witness). NOT liftable
to block recursion.
"""
import random

P_BB = (1 << 31) - (1 << 27) + 1  # BabyBear 2^31 - 2^27 + 1

def thm2(l, n, m, A, B):
    """Rosowski Thm 2. Returns (C, n_products, n_B_only_products)."""
    assert n % 2 == 0
    K = n // 2
    nprod = 0
    P1 = {}; P2 = {}; S = {}; Q = {}
    for i in range(l):
        for k in range(K):
            P1[i, k] = A[i][2*k] * (B[2*k][0] + A[i][2*k+1]); nprod += 1
            P2[i, k] = A[i][2*k+1] * (B[2*k+1][0] - A[i][2*k]); nprod += 1
    for j in range(1, m):
        for k in range(K):
            S[j, k] = B[2*k+1][j] * (B[2*k][0] + B[2*k][j]); nprod += 1
    for i in range(l):
        for j in range(1, m):
            for k in range(K):
                Q[i, j, k] = (A[i][2*k] + B[2*k+1][j]) * \
                             (A[i][2*k+1] + B[2*k][0] + B[2*k][j]); nprod += 1
    C = [[0]*m for _ in range(l)]
    for i in range(l):
        C[i][0] = sum(P1[i, k] + P2[i, k] for k in range(K))
        for j in range(1, m):
            C[i][j] = sum(Q[i, j, k] - P1[i, k] - S[j, k] for k in range(K))
    return C, nprod, len(S)

def alg1_333(A, B):
    """Rosowski Algorithm 1 specialised to <3,3,3> (21 products)."""
    nprod = 0
    C = [[0]*3 for _ in range(3)]
    # B-only products, shared across rows
    p7 = B[0][1]*B[1][0]; p8 = B[0][2]*B[2][0]; p9 = B[1][2]*B[2][1]
    nprod += 3
    for i in range(3):
        a1, a2, a3 = A[i][0], A[i][1], A[i][2]
        p1 = (a2 + B[0][1]) * (a1 + B[1][0]); nprod += 1
        p2 = (a3 + B[0][2]) * (a1 + B[2][0]); nprod += 1
        p3 = (a3 + B[1][2]) * (a2 + B[2][1]); nprod += 1
        p4 = a1 * (B[0][0] - B[0][1] - B[0][2] - a2 - a3); nprod += 1
        p5 = a2 * (B[1][1] - B[1][0] - B[1][2] - a1 - a3); nprod += 1
        p6 = a3 * (B[2][2] - B[2][0] - B[2][1] - a1 - a2); nprod += 1
        C[i][0] = p4 + p1 + p2 - p7 - p8
        C[i][1] = p5 + p1 + p3 - p7 - p9
        C[i][2] = p6 + p2 + p3 - p8 - p9
    return C, nprod, 3

def gate(fn, l, n, m, trials=8, mod=None):
    rng = random.Random(4)
    for _ in range(trials):
        lo, hi = (-99, 99) if mod is None else (0, mod - 1)
        A = [[rng.randint(lo, hi) for _ in range(n)] for _ in range(l)]
        B = [[rng.randint(lo, hi) for _ in range(m)] for _ in range(n)]
        C, np_, nb = fn(l, n, m, A, B) if fn is thm2 else fn(A, B)
        want = [[sum(A[i][k]*B[k][j] for k in range(n)) for j in range(m)]
                for i in range(l)]
        if mod:
            C = [[x % mod for x in r] for r in C]
            want = [[x % mod for x in r] for r in want]
        assert C == want, f"{fn.__name__} <{l},{n},{m}> WRONG"
    return np_, nb

if __name__ == "__main__":
    for tag, fn, (l, n, m) in [("<3,3,3> Alg1", alg1_333, (3, 3, 3)),
                                ("<4,4,4> Thm2", thm2, (4, 4, 4)),
                                ("<4,4,8> Thm2", thm2, (4, 4, 8)),
                                ("<8,4,4> Thm2", thm2, (8, 4, 4)),
                                ("<16,4,4> Thm2", thm2, (16, 4, 4))]:
        np_z, nb = gate(fn, l, n, m, mod=None)
        np_b, _ = gate(fn, l, n, m, mod=P_BB)
        print(f"{tag}: VERIFIED over Z and BabyBear — {np_z} products "
              f"({nb} B-only, amortizable across A-rows / fixed-W)")
