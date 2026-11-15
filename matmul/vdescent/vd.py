#!/usr/bin/env python3
"""vd.py: matrix-multiplication schemes as points of a variety (2026-11-14).

The exact decompositions of <g1 x g2 x g3> with r products are the zeros of
F(U, V, W) = sum_t U_t (x) V_t (x) W_t - T, a variety V_r in R^(r (I + J + K)).  Two tools:

  moduli   the tangent space of V_r at a scheme (the kernel of the Jacobian of F) against the
           directions every scheme has: the 2r rescalings of the products and the action of
           GL_g1 x GL_g2 x GL_g3.  What is left over ("moduli") are continuous families of
           inequivalent schemes through the point -- room to move.
  load / check / trivial / split, shared with descend.py.

Conventions: A is g1 x g2 (row-major, I = g1 g2), B is g2 x g3 (J), C is g1 x g3 (K, entry (i,k));
T[(i,j), (j,k), (i,k)] = 1.  Catalog files (Perminov's JSON: u, v, w) are read with either
orientation of C; PLinOpt's L/R/P .sms triples too.
"""
import json, sys, numpy as np
from fractions import Fraction

def tensor(g1, g2, g3, transpose_c=False):
    I, J, K = g1 * g2, g2 * g3, g1 * g3
    T = np.zeros((I, J, K))
    for i in range(g1):
        for j in range(g2):
            for k in range(g3):
                T[i * g2 + j, j * g3 + k, (k * g1 + i) if transpose_c else (i * g3 + k)] = 1
    return T

def residual(U, V, W, T):
    return np.einsum('ra,rb,rc->abc', U, V, W) - T

def load(path):
    """-> (g1, g2, g3), U, V, W with C in the (i,k) row-major convention"""
    if path.endswith('.json'):
        d = json.load(open(path))
        g = tuple(d['n'])
        f = lambda X: np.array([[float(Fraction(str(x))) for x in row] for row in X])
        U, V, W = f(d['u']), f(d['v']), f(d['w'])
    else:                                   # PLinOpt base name: base_L.sms, base_R.sms, base_P.sms
        sys.path.insert(0, '/Users/greg/projects/logic/matmul/levels')
        from levels import parse_sms
        import re
        m = re.search(r'(\d+)x(\d+)x(\d+)', path.split('/')[-1])
        g = tuple(int(x) for x in m.groups())
        U, V, P = (parse_sms(f'{path}_{s}.sms') for s in 'LRP')
        W = P.T if P.shape[1] == U.shape[0] else P
    g1, g2, g3 = g
    if np.abs(residual(U, V, W, tensor(*g))).max() > 1e-9:
        perm = [k * g1 + i for i in range(g1) for k in range(g3)]      # C given as (k,i): reorder to (i,k)
        W2 = W[:, perm]
        assert np.abs(residual(U, V, W2, tensor(*g))).max() < 1e-9, 'not a scheme in either orientation of C'
        W = W2
    return g, U, V, W

def trivial(g1, g2, g3):
    r = g1 * g2 * g3
    U, V, W = np.zeros((r, g1 * g2)), np.zeros((r, g2 * g3)), np.zeros((r, g1 * g3))
    t = 0
    for i in range(g1):
        for j in range(g2):
            for k in range(g3):
                U[t, i * g2 + j] = V[t, j * g3 + k] = W[t, i * g3 + k] = 1; t += 1
    return U, V, W

def normal_matrix(U, V, W):
    """J^T J for x = (U, V, W) flattened row-major, without forming J"""
    r, I = U.shape; J = V.shape[1]; K = W.shape[1]
    GU, GV, GW = U @ U.T, V @ V.T, W @ W.T
    n = r * (I + J + K)
    N = np.zeros((n, n))
    oU, oV, oW = 0, r * I, r * (I + J)
    N[oU:oV, oU:oV] = np.kron(GV * GW, np.eye(I))
    N[oV:oW, oV:oW] = np.kron(GU * GW, np.eye(J))
    N[oW:, oW:] = np.kron(GU * GV, np.eye(K))
    UV = np.einsum('rs,sa,rb->rasb', GW, U, V).reshape(r * I, r * J)
    UW = np.einsum('rs,sa,rc->rasc', GV, U, W).reshape(r * I, r * K)
    VW = np.einsum('rs,sb,rc->rbsc', GU, V, W).reshape(r * J, r * K)
    N[oU:oV, oV:oW] = UV; N[oV:oW, oU:oV] = UV.T
    N[oU:oV, oW:] = UW; N[oW:, oU:oV] = UW.T
    N[oV:oW, oW:] = VW; N[oW:, oV:oW] = VW.T
    return N

def trivial_tangents(g, U, V, W):
    """the tangent directions every scheme has: per product two rescalings; the Lie algebra of
    GL_g1 x GL_g2 x GL_g3 acting by A -> X A - A Y, B -> Y B - B Z, C -> X C - C Z"""
    g1, g2, g3 = g; r = U.shape[0]
    out = []
    for t in range(r):
        for s in range(2):
            dU, dV, dW = np.zeros_like(U), np.zeros_like(V), np.zeros_like(W)
            if s == 0: dU[t] = U[t]; dW[t] = -W[t]
            else: dV[t] = V[t]; dW[t] = -W[t]
            out.append(np.concatenate([dU.ravel(), dV.ravel(), dW.ravel()]))
    A = U.reshape(r, g1, g2); B = V.reshape(r, g2, g3); C = W.reshape(r, g1, g3)
    # the scheme pairs A with B with C^T-like; the action preserving sum a (x) b (x) c with T(i,j),(j,k),(i,k):
    # A -> X A Y^-1, B -> Y B Z^-1, C -> X^-T C Z^T
    for (n, slot) in ((g1, 'X'), (g2, 'Y'), (g3, 'Z')):
        for p in range(n):
            for q in range(n):
                E = np.zeros((n, n)); E[p, q] = 1
                dA, dB, dC = np.zeros_like(A), np.zeros_like(B), np.zeros_like(C)
                if slot == 'X': dA = np.einsum('pq,rqj->rpj', E, A); dC = -np.einsum('qp,rqk->rpk', E, C)
                if slot == 'Y': dA = -np.einsum('rip,pq->riq', A, E); dB = np.einsum('pq,rqk->rpk', E, B)
                if slot == 'Z': dB = -np.einsum('rjp,pq->rjq', B, E); dC = np.einsum('rip,qp->riq', C, E)
                out.append(np.concatenate([dA.reshape(r, -1).ravel(), dB.reshape(r, -1).ravel(), dC.reshape(r, -1).ravel()]))
    return np.array(out)

def moduli(g, U, V, W, tol=1e-9):
    N = normal_matrix(U, V, W)
    ev, evec = np.linalg.eigh(N)
    null = evec[:, ev < tol * ev[-1]]
    Tr = trivial_tangents(g, U, V, W)
    # every trivial tangent must be in the kernel (a check of the conventions)
    leak = np.abs(N @ Tr.T).max() / ev[-1]
    rank_tr = np.linalg.matrix_rank(Tr, tol=1e-8)
    gap = ev[ev >= tol * ev[-1]][0] / ev[-1] if (ev >= tol * ev[-1]).any() else 0
    return null.shape[1], rank_tr, leak, gap

if __name__ == '__main__':
    for path in sys.argv[1:]:
        if path.startswith('trivial:'):
            g = tuple(int(x) for x in path[8:].split('x')); U, V, W = trivial(*g)
        else:
            g, U, V, W = load(path)
        r = U.shape[0]
        nul, rtr, leak, gap = moduli(g, U, V, W)
        print(f"{path.split('/')[-1]}: <{g[0]}x{g[1]}x{g[2]}:{r}>  unknowns {r * (U.shape[1] + V.shape[1] + W.shape[1])}  "
              f"tangent space {nul}  rescalings + group orbit {rtr}  MODULI {nul - rtr}  (check {leak:.0e}, gap {gap:.1e})", flush=True)
