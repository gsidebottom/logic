#!/usr/bin/env python3
"""LP-pruned rung r=17 (2026-09-05): for every level-1 residual R = T + m
(matmul/r22/level1_residuals.txt, all 211 true orbits), every side-A fold
R|ker(e8 + lambda) must have rank >= 16. Certify each fold by the code
bound (HiGHS LP, exact rational dual certificate); write the rest to a
probe set for schemesearch3 --probe-tensor-file at target 16."""
import sys, os
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from code_bound import slices_side, rank

def rank_basis(vecs, n=9):
    rows=list(vecs); rk=0
    for c in range(n-1,-1,-1):
        piv=next((i for i in range(rk,len(rows)) if rows[i]>>c&1),None)
        if piv is None: continue
        rows[rk],rows[piv]=rows[piv],rows[rk]
        for i in range(len(rows)):
            if i!=rk and rows[i]>>c&1: rows[i]^=rows[rk]
        rk+=1
    return rows[:rk]

def annihilator(U):
    return rank_basis([phi for phi in range(1,512) if all(bin(phi&u).count('1')%2==0 for u in U)])

def quotient_A(t, U):
    phis=annihilator(U)
    return [[__import__('functools').reduce(lambda x,y:x^y,[t[a][b] for a in range(9) if phi>>a&1],0) for b in range(9)] for phi in phis]

def exact_code_bound_side(base):
    """LP on the dual + exact rational certificate; returns a sound integer lower bound."""
    k=len(base); phis=list(range(1,1<<k))
    ranks={}
    for phi in phis:
        acc=[0]*len(base[0])
        for i in range(k):
            if phi>>i&1: acc=[x^y for x,y in zip(acc,base[i])]
        ranks[phi]=rank(acc)
    n=len(phis)
    # dual: maximize sum r_phi y_phi s.t. for each c: sum_{phi:<c,phi>=1} y_phi <= 1
    A=np.zeros((n,n))
    for i,c in enumerate(phis):
        for j,phi in enumerate(phis):
            if bin(c&phi).count('1')%2==1: A[i,j]=1
    cvec=-np.array([ranks[phi] for phi in phis],dtype=float)
    res=linprog(cvec, A_ub=A, b_ub=np.ones(n), bounds=[(0,None)]*n, method='highs')
    if not res.success: return max(ranks.values())
    D=1<<20
    yq=[max(0,int(np.floor(v*D))) for v in res.x]
    loads=[sum(yq[j] for j,phi in enumerate(phis) if bin(c&phi).count('1')%2==1) for c in phis]
    L=max(loads)
    if L==0: return max(ranks.values())
    val=sum(yq[j]*ranks[phi] for j,phi in enumerate(phis))
    return max(max(ranks.values()), -(-val//L))

def code_bound(t, da, db, dc):
    return max(exact_code_bound_side(slices_side(t,da,db,dc,s)) for s in range(3))

def work(args):
    name, t = args
    out=[]
    for lam in range(256):
        v=(1<<8)|lam
        q=quotient_A(t,[v])
        b=code_bound(q,8,9,9)
        out.append((lam,b,q))
    return name, out

if __name__=="__main__":
    target=int(sys.argv[1]) if len(sys.argv)>1 else 16
    shard=int(sys.argv[2]) if len(sys.argv)>2 else 0
    nshard=int(sys.argv[3]) if len(sys.argv)>3 else 1
    roots=[]
    for i,line in enumerate(open('matmul/r22/level1_residuals.txt')):
        if i%nshard!=shard: continue
        f=line.split(); name=f[0]; da,db,dc=map(int,f[2:5])
        t=[[int(f[5+a*db+b],16) for b in range(db)] for a in range(da)]
        roots.append((name,t))
    probe=open(f'matmul/r22/lp_ladder_unresolved_t{target}_s{shard}.txt','w')
    from collections import Counter
    tot=Counter(); n_unres=0
    for name,t in roots:
        name,res=work((name,t))
        hist=Counter(b for _,b,_ in res)
        unres=[(lam,b,q) for lam,b,q in res if b<target]
        n_unres+=len(unres)
        for lam,b,q in unres:
            probe.write(f"{name}_lam{lam}_lp{b} {target} 8 9 9 {' '.join(f'{q[a][bb]:03x}' for a in range(8) for bb in range(9))}\n")
        probe.flush()
        tot.update(hist)
        print(f"{name}: fold code bounds {dict(sorted(hist.items()))}; unresolved {len(unres)}", flush=True)
    print(f"\nSHARD {shard}/{nshard} TOTAL fold code-bound histogram: {dict(sorted(tot.items()))}; unresolved folds: {n_unres} of {256*len(roots)}", flush=True)
