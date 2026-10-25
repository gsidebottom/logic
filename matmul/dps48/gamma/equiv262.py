"""Is our 16 sqrt2 scheme the same as PLinOpt's 4x4x4_48_accurate_262 up to signed permutations
(U, V, W), a permutation of the 48 products and per-product scaling?  Their files are read
from GitHub into memory (nothing saved).  Each product is compared as its rank-one tensor
A x B x Z (scaling-invariant), so only the signed permutations have to be found: pi_U, pi_V
from the first product's A factor, then pi_W, then every product checked."""
import base64, itertools, subprocess, sys
import numpy as np
sys.path.insert(0, "../../fastmm")
import growth
from exact import signed_perms

def fetch(name):
    out = subprocess.run(["gh", "api", f"repos/jgdumas/plinopt/contents/data/{name}", "--jq", ".content"],
                         capture_output=True, text=True, check=True).stdout
    return base64.b64decode(out).decode()

def sms(text):
    lines = [l for l in text.split("\n") if l.strip() and not l.lstrip().startswith("#")]
    r, c, _ = lines[0].split()
    M = np.zeros((int(r), int(c)))
    for l in lines[1:]:
        f = l.split()
        if f[0] == "0":
            continue
        a, b = f[2].split("/") if "/" in f[2] else (f[2], "1")
        M[int(f[0]) - 1, int(f[1]) - 1] = float(a) / float(b)
    return M

def terms(L, R, P):
    r = L.shape[0]
    return L.reshape(r, 4, 4), R.reshape(r, 4, 4), P.T.reshape(r, 4, 4)

def canon(M):
    """a matrix up to a nonzero scalar: divided by its first nonzero entry, rounded"""
    v = M.ravel()
    k = np.nonzero(np.abs(v) > 1e-12)[0][0]
    return tuple(np.round(v / v[k], 9))

def tensor_key(A, B, Z):
    return (canon(A), canon(B), canon(Z))

ours = tuple(np.array([[float(x) for x in row] for row in growth.parse_sms(f"g16s2_{s}.sms")]) for s in "LRP")
theirs = tuple(sms(fetch(f"4x4x4_48_accurate_262_{s}.sms")) for s in "LRP")
A1, B1, Z1 = terms(*ours)
A2, B2, Z2 = terms(*theirs)
print("nonzeros ours", [int((np.abs(M) > 1e-12).sum()) for M in ours], " theirs", [int((np.abs(M) > 1e-12).sum()) for M in theirs])
target = {tensor_key(A2[j], B2[j], Z2[j]) for j in range(48)}
targetA = {canon(A2[j]) for j in range(48)}
sp = signed_perms()
found = None
# the action of signed permutations: Mat(L') = U^-T A V^T = U A V^T (orthogonal), Mat(R') = V B W^T, Z' = U Z W^T
for PU in sp:
    for PV in sp:
        if canon(PU @ A1[0] @ PV.T) not in targetA:
            continue
        for PW in sp:
            ok = all(tensor_key(PU @ A1[i] @ PV.T, PV @ B1[i] @ PW.T, PU @ Z1[i] @ PW.T) in target for i in range(48))
            if ok:
                found = (PU, PV, PW)
                break
        if found:
            break
    if found:
        break
if found:
    print("EQUIVALENT: signed permutations found mapping all 48 products of ours onto theirs")
    for nm, M in zip("UVW", found):
        print(f"  pi_{nm} =", M.astype(int).tolist())
else:
    print("no signed-permutation equivalence found")

# the input-swapping symmetry (X, Y, Z) -> (Y^T, X^T, Z^T) of the trace form: Mat(L) = X^T, so
# the new A factor is B^T... in matrix terms: A_new = B2^T, B_new = A2^T, Z_new = Z2^T
if not found:
    A3 = np.array([B.T for B in B2]); B3 = np.array([A.T for A in A2]); Z3 = np.array([Z.T for Z in Z2])
    target = {tensor_key(A3[j], B3[j], Z3[j]) for j in range(48)}
    targetA = {canon(A3[j]) for j in range(48)}
    for PU in sp:
        for PV in sp:
            if canon(PU @ A1[0] @ PV.T) not in targetA:
                continue
            for PW in sp:
                if all(tensor_key(PU @ A1[i] @ PV.T, PV @ B1[i] @ PW.T, PU @ Z1[i] @ PW.T) in target for i in range(48)):
                    found = (PU, PV, PW)
                    break
            if found:
                break
        if found:
            break
    print("with their inputs swapped (the transpose symmetry):", "EQUIVALENT" if found else "no equivalence")
    if found:
        for nm, M in zip("UVW", found):
            print(f"  pi_{nm} =", M.astype(int).tolist())
