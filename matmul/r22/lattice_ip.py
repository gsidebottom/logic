#!/usr/bin/env python3
"""The LATTICE INTEGER PROGRAM (2026-09-06). For any decomposition of T with
r products let m_c = #products whose A-coefficient is c in F2^9 \\ 0. For
every killed subspace U the products with a_i in U vanish in T|U, so
    sum_{c not in U} m_c >= rank(T|U) >= t_U   (t_U = Wang's verified value).
Codim-1 (all t=19) + integrality already forces r >= 20 (his DP value);
the question is whether codim-2 (18/19) and the slice-rank (code-bound)
constraints force 21. LP relaxation first, then the MIP (HiGHS)."""
import sys, time
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix, csr_matrix
def rank3(m):
    rows=[m&7,m>>3&7,m>>6&7]; rk=0
    for c in (2,1,0):
        piv=next((i for i in range(rk,3) if rows[i]>>c&1),None)
        if piv is None: continue
        rows[rk],rows[piv]=rows[piv],rows[rk]
        for i in range(3):
            if i!=rk and rows[i]>>c&1: rows[i]^=rows[rk]
        rk+=1
    return rk
n=511; idx=lambda c: c-1
rows=[]; rhs=[]
val1={}; val2=[]
for line in open('matmul/r22/lattice_values.txt'):
    f=line.split()
    if f[0]=='1': val1[int(f[1])]=int(f[2])
    else: val2.append((int(f[1]),int(f[2]),int(f[3])))
# codim-1: sum_{c != v} m_c >= t_v
for v,t in val1.items():
    r=np.ones(n); r[idx(v)]=0; rows.append(r); rhs.append(t)
# codim-2: sum_{c not in {a,b,a^b}} m_c >= t_U
for a,b,t in val2:
    r=np.ones(n); r[idx(a)]=0; r[idx(b)]=0; r[idx(a^b)]=0; rows.append(r); rhs.append(t)
# code bound (hyperplanes): sum_{c: <c,phi>=1} m_c >= rank T(phi,.,.) = 3 rank(phi)
for phi in range(1,512):
    r=np.zeros(n)
    for c in range(1,512):
        if bin(c&phi).count('1')%2==1: r[idx(c)]=1
    rows.append(r); rhs.append(3*rank3(phi))
A=csr_matrix(np.array(rows)); b=np.array(rhs,dtype=float)
print(f"constraints: {A.shape[0]} (511 codim-1, {len(val2)} codim-2, 511 slice-rank); variables: {n}", flush=True)
cobj=np.ones(n)
t0=time.time()
lp=milp(cobj, constraints=LinearConstraint(A, b, np.inf), bounds=Bounds(0, np.inf), integrality=np.zeros(n))
print(f"LP relaxation: {lp.fun:.4f} [{time.time()-t0:.1f}s] -> ceil {int(np.ceil(lp.fun-1e-9))}", flush=True)
t0=time.time()
mip=milp(cobj, constraints=LinearConstraint(A, b, np.inf), bounds=Bounds(0, np.inf), integrality=np.ones(n), options={"time_limit": float(sys.argv[1]) if len(sys.argv)>1 else 1800.0, "disp": False})
print(f"MIP: status {mip.status} ({mip.message}); objective {mip.fun}; mip_dual_bound {getattr(mip,'mip_dual_bound',None)}; mip_gap {getattr(mip,'mip_gap',None)} [{time.time()-t0:.1f}s]", flush=True)
if mip.x is not None:
    m=np.round(mip.x).astype(int); support=[(c+1,m[c]) for c in range(n) if m[c]>0]
    print("an optimal type distribution (c, m_c):", support, flush=True)
    print("ranks of the types:", sorted(rank3(c) for c,_ in support for _ in range(1)), flush=True)
