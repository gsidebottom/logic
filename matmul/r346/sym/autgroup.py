#!/usr/bin/env python3
"""The symmetry group of a scheme inside GL_g1 x GL_g2 x GL_g3 (2026-11-14), by frames.

(X, Y, Z) acts by A -> X A Y^-1, B -> Y B Z^-1, C -> X^-T C Z^T and fixes the matrix multiplication
tensor; it is a symmetry of the scheme if it permutes its products (as rank-one tensors).  For the
<3x4x6:54> scheme: the rank-one C factors u z^T have u in {e1, e2, e3}, so X^-T, hence X, is a
permutation times a diagonal matrix, and the rank-one A factors' six u directions fix the diagonal
up to signs: X is one of the 48 signed permutations.  Y^-T permutes the nine v directions of the
rank-one A factors, which contain projective frames of P^3: every image of one frame gives a
candidate Y.  For a pair (X, Y) that maps the set of A factors to itself, the permutation of the
products is read off the A factors, and Z^-1 is the solution of the linear system
Y B_t Z^-1 = mu_t B_pi(t); the triple is kept if it permutes the products.
   autgroup.py scheme.json
"""
import sys, json, itertools, numpy as np
sys.path.insert(0, '/Users/greg/projects/logic/matmul/vdescent')
from vd import load
g, U, V, W = load(sys.argv[1]); g1, g2, g3 = g; r = U.shape[0]
A, B, C = U.reshape(r, g1, g2), V.reshape(r, g2, g3), W.reshape(r, g1, g3)
def unit(x):
    x = x / np.linalg.norm(x); i = np.argmax(np.abs(x) > 1e-9); return x * np.sign(x[i])
def dirs(vs):
    out = []
    for x in vs:
        x = unit(x)
        if not any(np.allclose(x, y, atol=1e-7) for y in out): out.append(x)
    return np.array(out)
def same_dir_sets(P, Q):
    return len(P) == len(Q) and all(any(np.allclose(p, q, atol=1e-6) for q in Q) for p in P)
rank1 = [t for t in range(r) if np.linalg.matrix_rank(A[t]) == 1]
va = dirs([np.linalg.svd(A[t])[2][0] for t in rank1])                # the v directions (rows) of the rank-one A factors
An = np.array([unit(A[t].ravel()) for t in range(r)])
print(f"{len(va)} v directions; {len(dirs(An))} distinct A factors among {r} products", flush=True)
# a frame of P^3 among the v directions: 5 points, every 4 independent
frame = next(c for c in itertools.combinations(range(len(va)), g2 + 1)
             if all(abs(np.linalg.det(va[list(s)])) > 1e-6 for s in itertools.combinations(c, g2)))
F = va[list(frame)]
co = np.linalg.solve(F[:g2].T, F[g2])                                # F[g2] = sum co_i F[i]
Ycands = []
for img in itertools.permutations(range(len(va)), g2 + 1):
    G = va[list(img)]
    if abs(np.linalg.det(G[:g2])) < 1e-6: continue
    co2 = np.linalg.solve(G[:g2].T, G[g2])
    if np.abs(co2).min() < 1e-6: continue
    # M F[i] = s_i G[i] with s_i = co2_i / co_i (so that M F[g2] = G[g2] up to scale)
    M = (G[:g2].T * (co2 / co)) @ np.linalg.inv(F[:g2].T)            # M = Y^-T on directions
    if same_dir_sets(dirs((M @ va.T).T), va): Ycands.append(np.linalg.inv(M).T)
print(f"{len(Ycands)} candidates for Y from the frames", flush=True)
Xcands = []
for perm in itertools.permutations(range(g1)):
    for signs in itertools.product([1, -1], repeat=g1 - 1):
        X = np.zeros((g1, g1))
        for i, p in enumerate(perm): X[p, i] = (1,) + signs if False else ((1,) + signs)[i]
        Xcands.append(X)
tens = lambda A, B, C: np.einsum('tij,tkl,tmn->tijklmn', A, B, C).reshape(len(A), -1)
t0 = tens(A, B, C)
found = {}
for X in Xcands:
    Xit = np.linalg.inv(X).T
    for Y in Ycands:
        Yi = np.linalg.inv(Y)
        A2 = np.array([unit((X @ A[t] @ Yi).ravel()) for t in range(r)])
        d = 1 - np.abs(A2 @ An.T)                                    # 0 where the factors are parallel
        if (d.min(1) > 1e-7).any(): continue
        # the products whose A factor is parallel to the image of product t's: candidates for pi(t); Z^-1 from
        # Y B_t Zi = mu_t B_s, tried for the matchings the A factors allow (a product's B factor decides among them)
        opts = [np.nonzero(d[t] < 1e-7)[0] for t in range(r)]
        if max(len(o) for o in opts) > 2: continue
        amb = [t for t in range(r) if len(opts[t]) > 1]
        for choice in itertools.product(*[range(len(opts[t])) for t in amb[:10]]):
            pi = [int(o[0]) for o in opts]
            for t, c in zip(amb, choice): pi[t] = int(opts[t][c])
            if len(set(pi)) != r: continue
            rows = []
            for t in range(r):
                YB = Y @ B[t]                                        # (YB Zi)[j,k] - mu_t B_s[j,k] = 0
                for j in range(g2):
                    for k in range(g3):
                        row = np.zeros(g3 * g3 + r)
                        for l in range(g3): row[l * g3 + k] = YB[j, l]
                        row[g3 * g3 + t] = -B[pi[t]][j, k]
                        rows.append(row)
            sv = np.linalg.svd(np.array(rows))
            if sv[1][-1] > 1e-8 * sv[1][0]: continue
            sol = sv[2][-1]; Zi = sol[:g3 * g3].reshape(g3, g3)
            if abs(np.linalg.det(Zi)) < 1e-12: continue
            Z = np.linalg.inv(Zi)
            t2 = tens(X @ A @ Yi, Y @ B @ Zi, Xit @ C @ Z.T)
            dd = ((t2[:, None, :] - t0[None, :, :]) ** 2).sum(2)
            p2 = dd.argmin(1)
            if dd[np.arange(r), p2].max() < 1e-12 and len(set(p2)) == r:
                found[tuple(int(x) for x in p2)] = (X, Y, Z)
perms = list(found)
def order(pi):
    q, n = pi, 1
    while q != tuple(range(r)): q = tuple(pi[i] for i in q); n += 1
    return n
closed = all(tuple(a[i] for i in b) in found for a in perms for b in perms)
print(f"# {sys.argv[1].split('/')[-1]}: {len(perms)} symmetries; closed under composition: {closed}; orders {sorted(order(p) for p in perms)}")
out = []
for pi, (X, Y, Z) in found.items():
    fixed = sum(1 for i, j in enumerate(pi) if i == j); q = order(pi)
    # the action on the factor spaces (vec row-major): A -> X A Y^-1, B -> Y B Z^-1, C -> X^-T C Z^T, each scaled
    # so that its q-th power is the identity (the scalings cancel on the products)
    Yi, Zi, Xit = np.linalg.inv(Y), np.linalg.inv(Z), np.linalg.inv(X).T
    acts = []
    for M in (np.kron(X, Yi.T), np.kron(Y, Zi.T), np.kron(Xit, Z)):
        c = np.trace(np.linalg.matrix_power(M, q)) / len(M)
        M = M / (np.sign(c) * abs(c) ** (1 / q)) if q % 2 else M / abs(c) ** (1 / q)
        assert np.abs(np.linalg.matrix_power(M, q) - np.eye(len(M))).max() < 1e-8, 'the action does not have order q on a factor space'
        acts.append(M)
    out.append({'perm': list(pi), 'order': q, 'fixed': fixed, 'X': X.tolist(), 'Y': Y.tolist(), 'Z': Z.tolist(),
                'MA': acts[0].tolist(), 'MB': acts[1].tolist(), 'MC': acts[2].tolist()})
    print(f"   order {q}, {fixed} products fixed; fixed subspaces of the factor spaces: "
          f"{[int(round(np.trace(sum(np.linalg.matrix_power(M, j) for j in range(q)) / q))) for M in acts]}")
json.dump(out, open(sys.argv[1].replace('.json', '_aut.json'), 'w'))
