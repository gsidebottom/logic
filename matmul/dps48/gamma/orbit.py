"""The (inf,2)-growth factor of Dumas, Pernet and Sedoglavic (arXiv:2603.18699, eq. 4) on the
orbit of a <4x4x4:48> scheme: role assignments (which factor set computes the outputs) and the
De Groot isotropies (U, V, W) acting as L (U^-1 x V^T), R (V^-1 x W^T), (U x W^-T) P on row-major
vectorizations (PLinOpt's orbiter uses the same group).

  gamma_{inf,2} = max_j sum_i ||L_i||_2 ||R_i||_2 |P_ji|
"""
import os, sys
import numpy as np
np.seterr(all="ignore")   # numpy on Accelerate raises spurious FP flags in matmul

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "fastmm"))
import growth                                   # exact parsing and checking (rationals)

DATA = os.path.join(HERE, "..", "plinopt", "data")
N = 4

def load(prefix, r=48):
    """a scheme as float matrices, checked exactly first"""
    if os.path.exists(prefix + "_L.slp"):
        L, R, P = growth.from_slp(prefix, N * N, r)
    else:
        L, R, P = growth.from_sms(prefix)
    assert growth.check_scheme(L, R, P, N, N, N), prefix
    f = lambda M: np.array([[float(x) for x in row] for row in M])
    return f(L), f(R), f(P)

def to_trace(L, R, P):
    """X_i, Y_i, Z_i with sum_i tr(X_i A) tr(Y_i B) tr(Z_i G) = tr(A B G)"""
    r = L.shape[0]
    X = L.reshape(r, N, N).transpose(0, 2, 1)
    Y = R.reshape(r, N, N).transpose(0, 2, 1)
    Z = P.T.reshape(r, N, N)
    return X, Y, Z

def from_trace(X, Y, Z):
    r = X.shape[0]
    return X.transpose(0, 2, 1).reshape(r, N * N), Y.transpose(0, 2, 1).reshape(r, N * N), Z.reshape(r, N * N).T

def roles(L, R, P):
    """the three cyclic rotations: rotation k makes factor set k the output"""
    X, Y, Z = to_trace(L, R, P)
    return [from_trace(X, Y, Z), from_trace(Y, Z, X), from_trace(Z, X, Y)]

def brent_error(L, R, P):
    """max deviation from the matrix multiplication tensor (floating point check)"""
    T = np.einsum("ia,ib,ci->abc", L, R, P)
    W = np.zeros((N * N,) * 3)
    for i in range(N):
        for j in range(N):
            for l in range(N):
                W[i * N + j, j * N + l, i * N + l] = 1
    return np.abs(T - W).max()

def act(L, R, P, U, V, W):
    iU, iV, iW = np.linalg.inv(U), np.linalg.inv(V), np.linalg.inv(W)
    return L @ np.kron(iU, V.T), R @ np.kron(iV, W.T), np.kron(U, iW.T) @ P

def g_inf2(L, R, P):
    w = np.linalg.norm(L, axis=1) * np.linalg.norm(R, axis=1)
    return (np.abs(P) @ w).max()

def g_inf_inf(L, R, P):
    w = np.abs(L).sum(axis=1) * np.abs(R).sum(axis=1)
    return (np.abs(P) @ w).max()

def g2(L, R, P):
    return (np.linalg.norm(L, axis=1) * np.linalg.norm(R, axis=1) * np.linalg.norm(P, axis=0)).sum()

SCHEMES = {
    "table1": os.path.join(DATA, "4x4x4_48_accurate"),
    "dps25": os.path.join(DATA, "4x4x4_48_rational"),
    "ours201": os.path.join(HERE, "..", "cand48", "p005_201n"),
}

if __name__ == "__main__":
    for name, prefix in SCHEMES.items():
        base = load(prefix)
        for k, (L, R, P) in enumerate(roles(*base)):
            print(f"{name:<8} output = factor set {k}:  brent err {brent_error(L, R, P):.1e}  "
                  f"g(inf,2) {g_inf2(L, R, P):8.3f}  g(inf,inf) {g_inf_inf(L, R, P):8.2f}  gamma2 {g2(L, R, P):8.3f}")
