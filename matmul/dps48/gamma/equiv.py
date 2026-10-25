"""Equivalence of two <4x4x4:48> schemes under signed permutations of (U, V, W), a permutation
and rescaling of the products, and optionally the input-swapping symmetry (X, Y, Z) ->
(Y^T, X^T, Z^T): returns (swapped, pi_U, pi_V, pi_W) or None."""
import numpy as np
from exact import signed_perms

def terms(L, R, P):
    r = L.shape[0]
    return L.reshape(r, 4, 4), R.reshape(r, 4, 4), P.T.reshape(r, 4, 4)

def canon(M):
    v = M.ravel()
    k = np.nonzero(np.abs(v) > 1e-12)[0][0]
    return tuple(np.round(v / v[k], 9))

def equivalent(s1, s2):
    A1, B1, Z1 = terms(*s1)
    A2, B2, Z2 = terms(*s2)
    sp = signed_perms()
    for swapped in (False, True):
        if swapped:
            A2, B2, Z2 = np.array([B.T for B in B2]), np.array([A.T for A in A2]), np.array([Z.T for Z in Z2])
        target = {(canon(A2[j]), canon(B2[j]), canon(Z2[j])) for j in range(len(A2))}
        targetA = {canon(A) for A in A2}
        for PU in sp:
            for PV in sp:
                if canon(PU @ A1[0] @ PV.T) not in targetA:
                    continue
                for PW in sp:
                    if all((canon(PU @ A1[i] @ PV.T), canon(PV @ B1[i] @ PW.T), canon(PU @ Z1[i] @ PW.T)) in target
                           for i in range(len(A1))):
                        return swapped, PU, PV, PW
    return None
