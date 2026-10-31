import json, sys
sys.path.append('/Users/greg/Library/Python/3.9/lib/python/site-packages')
sys.path.insert(0, '/Users/greg/projects/logic/matmul/dps48/rfc2610')
import numpy as np, gamma_fixed as GF
SP = sys.argv[1]
def stats(T):
    L = T[0].reshape(48, 16); R = T[1].reshape(48, 16); P = T[2].transpose(0, 2, 1).reshape(48, 16).T
    w = np.linalg.norm(L, axis=1) * np.linalg.norm(R, axis=1)
    return GF.gamma2(T), float((np.abs(P) @ w).max()), float((.5 * np.sqrt((P ** 2) @ (w ** 2))).max()), sum(int(np.count_nonzero(np.abs(M) > 1e-9)) for M in T)
a = GF.load(f"{SP}/plinopt_main/data/4x4x4_48_accurate_262")
print("accurate_262       gamma_2 %.4f  gamma_inf,2 %.4f  amp %.4f  nnz %d" % stats(a))
rows = []
for r in json.load(open(f"{SP}/td/perfect/score.json")):
    rows.append((r['tag'],) + stats(GF.load(f"{SP}/td/perfect/{r['tag']}")))
g2 = [r[1] for r in rows]; gi = [r[2] for r in rows]; am = [r[3] for r in rows]; nz = [r[4] for r in rows]
print(f"24 dyadic points   gamma_2 {min(g2):.4f}-{max(g2):.4f}  gamma_inf,2 {min(gi):.4f}-{max(gi):.4f}  amp {min(am):.4f}-{max(am):.4f}  nnz {min(nz)}-{max(nz)}")
A, B, C = np.load(f"{SP}/td/frames64.npy")
U, V, W = a
T = (A @ U @ B.T, B @ V @ C.T, C @ W @ A.T)
print("all-64 point Q(sqrt2): gamma_2 %.4f  gamma_inf,2 %.4f  amp %.4f  nnz %d" % stats(T))
irr = 0
for M in T:
    x = M.ravel(); x = x[np.abs(x) > 1e-9]
print("rows of L with entries of two different magnitudes at the all-64 point:", sum(1 for m in T[0] if len(set(np.round(np.abs(m[np.abs(m) > 1e-9]), 5).tolist())) > 1))
