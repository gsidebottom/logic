"""Exact schemes at the gamma_{inf,2} optima found by gamma48: snap the orthogonal factors to
their exact forms (entries 0, +-1/sqrt2 or +-1/2 or signed permutations), pick the free V among
the 1152 orthogonal matrices with entries 0, +-1/sqrt2 for the sparsest L and R, rescale each
term so every coefficient is dyadic, and check the result exactly (rationals)."""
import itertools, os, sys
from fractions import Fraction as F
import numpy as np
np.seterr(all="ignore")
import orbit
sys.path.insert(0, os.path.join(orbit.HERE, "..", "..", "fastmm"))
import growth

S2 = np.sqrt(2.0)

def q45_all():
    """all 4x4 Q in {0,+-1} with Q Q^T = 2 I (Q / sqrt2 orthogonal): 1152 of them"""
    rows = [v for v in itertools.product([-1, 0, 1], repeat=4) if sum(map(abs, v)) == 2]
    out = []
    def rec(acc):
        if len(acc) == 4:
            out.append(np.array(acc, dtype=float))
            return
        for v in rows:
            if all(np.dot(v, a) == 0 for a in acc):
                rec(acc + [v])
    rec([])
    return out

def snap(M, scales=(S2, 2.0, 1.0)):
    """M (up to scale and sign) as Q / s with Q in {0,+-1}, orthogonal: (Q, s) or None"""
    M = M / np.abs(M).max()
    for s in scales:
        Q = np.round(M * np.abs(M).max() * 1.0 / np.abs(M).max())   # entries are +-1 or 0 after scaling
        Q = np.where(np.abs(M) > 0.5, np.sign(M), 0.0)
        if np.allclose(Q @ Q.T, (s * s) * np.eye(4) / 1.0 * (1.0 if s == 1.0 else 1.0)) and np.allclose(M, Q, atol=1e-3):
            return Q, s
    return None

def transform_float(L, R, P, U, V, W):
    return orbit.act(L, R, P, U, V, W)

def nnz(M):
    return int((np.abs(M) > 1e-12).sum())

def to_exact(M):
    """a float matrix of dyadic values (small denominators) as Fractions, checked"""
    E = [[F(x).limit_denominator(1 << 20) for x in row] for row in M]
    assert all(float(e) == x for re, rx in zip(E, M) for e, x in zip(re, rx)), "not dyadic"
    return E

def dyadic_rescale(L, R, P):
    """per-term scaling (alpha, beta, 1/(alpha beta)) making each term's entries dyadic: a term
    whose L (or R) row carries 1/sqrt2 is multiplied by sqrt2 there and its P column by 1/sqrt2"""
    L, R, P = L.copy(), R.copy(), P.copy()
    def is_dyadic(v):
        return all(abs(x * 2**20 - round(x * 2**20)) < 1e-6 for x in v)
    for i in range(L.shape[0]):
        a = 1.0 if is_dyadic(L[i]) else S2
        b = 1.0 if is_dyadic(R[i]) else S2
        L[i] *= a
        R[i] *= b
        P[:, i] /= a * b
        assert is_dyadic(L[i]) and is_dyadic(R[i]) and is_dyadic(P[:, i]), f"term {i} not dyadic after rescaling"
    # snap to exact dyadics
    snapd = lambda M: np.round(M * 2**20) / 2**20
    return snapd(L), snapd(R), snapd(P)

def report(name, L, R, P):
    E = [to_exact(M) for M in (L, R, P)]
    ok = growth.check_scheme(*E, 4, 4, 4)
    g = growth.gammas(*E)
    print(f"{name}: exact {ok}  g(inf,2) {g[('inf', 2)]:.6f}  g(inf,inf) {g[('inf', 'inf')]:.3f}  g(2,2) {g[(2, 2)]:.4f}  "
          f"gamma2 {g['g2']:.4f}  nnz L {nnz(L)} R {nnz(R)} P {nnz(P)}  "
          f"denominators {sorted({x.denominator for M in E for row in M for x in row})}")
    return E, ok

def write_sms(path, E, comment):
    rows, cols = len(E), len(E[0])
    with open(path, "w") as f:
        f.write(f"# {comment}\n{rows} {cols} R\n")
        for i in range(rows):
            for j in range(cols):
                if E[i][j] != 0:
                    f.write(f"{i + 1} {j + 1} {E[i][j]}\n")
        f.write("0 0 0\n")

def load_point(path, k=0):
    rows = [l.split() for l in open(path)]
    x = np.array([float(t) for t in rows[k][2:]])
    return float(rows[k][0]), x[:16].reshape(4, 4), x[16:32].reshape(4, 4), x[32:].reshape(4, 4)


def signed_perms():
    out = []
    for p in itertools.permutations(range(4)):
        for sg in itertools.product([-1, 1], repeat=4):
            Q = np.zeros((4, 4))
            for i in range(4):
                Q[i, p[i]] = sg[i]
            out.append(Q)
    return out

def snap_factor(M, tol=2e-3):
    """M = (scalar) D Q / c with Q in {0,+-1}, Q Q^T = c^2 I and D diagonal (row scales, the
    largest 1): (D, Q, c) or None"""
    rn = np.linalg.norm(M, axis=1)
    Mn = M / rn[:, None]                    # unit rows
    for c2 in (1, 2, 4):
        Q = np.where(np.abs(Mn) > 0.5 / np.sqrt(c2), np.sign(Mn), 0.0)
        if np.allclose(Q @ Q.T, c2 * np.eye(4)) and np.allclose(Mn, Q / np.sqrt(c2), atol=tol):
            return np.diag(rn / rn.max()), Q, np.sqrt(c2)
    return None

def build(L0, R0, P0, U, V, W, dU=None, dW=None):
    """the scheme moved by U = D_U Q_U / c_U, V = Q_V / c_V, W = D_W Q_W / c_W (each a (D, Q, c)),
    rescaled per term so L, R carry no constants and P the dyadic 1 / (c_U c_V c_W)^2; dU, dW
    override the row scales (to put a dyadic value in place of an irrational one)"""
    (DU, QU, cU), (DV, QV, cV), (DW, QW, cW) = U, V, W
    assert np.allclose(DV, np.eye(4)), "V must be orthogonal"
    DU = DU if dU is None else dU
    DW = DW if dW is None else dW
    iDU, iDW = np.linalg.inv(DU), np.linalg.inv(DW)
    r = L0.shape[0]
    A, B, Z = L0.reshape(r, 4, 4), R0.reshape(r, 4, 4), P0.T.reshape(r, 4, 4)
    A2 = np.einsum("pa,ab,ibc,dc->ipd", iDU, QU, A, QV)             # D_U^-1 Q_U A Q_V^T
    B2 = np.einsum("ab,ibc,dc,de->iae", QV, B, QW, DW)              # Q_V B Q_W^T D_W
    c2 = round(cU * cU) * round(cV * cV) * round(cW * cW)          # exact: each c^2 is 1, 2 or 4
    Z2 = np.einsum("pa,ab,ibc,dc,de->ipe", DU, QU, Z, QW, iDW) / c2
    # balance each term by powers of two (free in floating point): largest |L|, |R| entries in [1/2, 1)
    for i in range(r):
        ea = np.floor(np.log2(np.abs(A2[i]).max())) + 1
        eb = np.floor(np.log2(np.abs(B2[i]).max())) + 1
        A2[i] /= 2.0 ** ea
        B2[i] /= 2.0 ** eb
        Z2[i] *= 2.0 ** (ea + eb)
    return A2.reshape(r, 16), B2.reshape(r, 16), Z2.reshape(r, 16).T
