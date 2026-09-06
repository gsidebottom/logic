#!/usr/bin/env python3
"""The CODE BOUND over F_2 (2026-09-05): for a tensor concise on a side of
dimension k, the products' coefficient vectors on that side form a k-dim
binary linear code in F_2^r; for every covector phi the slice T(phi,.,.)
is the sum of the rank-one matrices of the products in S_phi = {i :
phi(a_i) = 1}, so |S_phi| >= rank(T(phi,.,.)).  With m_c = number of
products of column type c in F_2^k \ 0:
    rank(T) >= min sum_c m_c  s.t.  sum_{c: <c,phi>=1} m_c >= rank(w_phi)  (all phi != 0)
an integer program in 2^k - 1 variables; max over sides.  LP relaxation
(ceil) is a valid lower bound; the ILP is solved exactly by bounded
enumeration when 2^k - 1 <= 15.
Input: the frontier probe set (VERDICT k da db dc hexes) or --root."""
import sys, os, itertools
from math import ceil
try:
    import numpy as np
    from scipy.optimize import linprog
    HAVE_LP=True
except ImportError:
    HAVE_LP=False

def rank(rows):
    rows=list(rows); rk=0; n=max((r.bit_length() for r in rows), default=0)
    for c in range(n-1,-1,-1):
        piv=next((i for i in range(rk,len(rows)) if rows[i]>>c&1),None)
        if piv is None: continue
        rows[rk],rows[piv]=rows[piv],rows[rk]
        for i in range(len(rows)):
            if i!=rk and rows[i]>>c&1: rows[i]^=rows[rk]
        rk+=1
    return rk

def slices_side(t, da, db, dc, side):
    """t[a][b] mask over c. Return (k, list of slices as row-lists, slice(phi) function)"""
    if side==0:
        base=[[t[a][b] for b in range(db)] for a in range(da)]      # A-slice a: db rows of dc bits
    elif side==1:
        base=[[t[a][b] for a in range(da)] for b in range(db)]      # B-slice b: da rows of dc bits
    else:
        base=[]
        for c in range(dc):
            rows=[]
            for a in range(da):
                r=0
                for b in range(db):
                    if t[a][b]>>c&1: r|=1<<b
                rows.append(r)
            base.append(rows)                                       # C-slice c: da rows of db bits
    return base

def code_bound_side(base, exact=True):
    """base: list of k slices (each a list of row masks). Returns (lp_bound, ilp_bound or None)."""
    # concise on this side? reduce to independent slices: rank of the slice span
    k=len(base)
    # slice for covector phi (bitmask over k): XOR of base slices
    phis=list(range(1,1<<k))
    ranks={}
    for phi in phis:
        acc=[0]*len(base[0])
        for i in range(k):
            if phi>>i&1:
                acc=[x^y for x,y in zip(acc,base[i])]
        ranks[phi]=rank(acc)
    # if some phi has rank 0 the tensor is not concise here: the code is still valid (weight >= 0)
    cols=list(range(1,1<<k))   # column types c
    # LP: minimize sum m_c s.t. for each phi: sum_{c: parity(c&phi)=1} m_c >= rank
    lp=max(ranks.values())
    if HAVE_LP:
        A=np.zeros((len(phis),len(cols))); b=np.zeros(len(phis))
        for i,phi in enumerate(phis):
            for j,c in enumerate(cols):
                if bin(c&phi).count('1')%2==1: A[i,j]=-1
            b[i]=-ranks[phi]
        res=linprog(np.ones(len(cols)), A_ub=A, b_ub=b, bounds=[(0,None)]*len(cols), method='highs')
        if res.success: lp=max(lp, ceil(res.fun-1e-9))
    ilp=None
    if exact and len(cols)<=15:
        # exact ILP by branch and bound over integer m with sum <= lp+3 (search upward)
        need=[(phi,ranks[phi]) for phi in phis]
        def feasible(total):
            # DFS assigning m_c in order with pruning by remaining budget and residual needs
            m=[0]*len(cols)
            def rec(j, budget):
                if j==len(cols):
                    return all(sum(m[jj] for jj,c in enumerate(cols) if bin(c&phi).count('1')%2==1)>=r for phi,r in need)
                for v in range(budget,-1,-1):
                    m[j]=v
                    if rec(j+1,budget-v): return True
                m[j]=0
                return False
            return rec(0,total)
        t=lp
        while t<=lp+8 and not feasible(t): t+=1
        ilp=t if t<=lp+8 else None
    return lp, ilp

def bound_all(t, da, db, dc, exact=True):
    out=[]
    for side,dim in ((0,da),(1,db),(2,dc)):
        if dim>9: continue
        base=slices_side(t,da,db,dc,side)
        out.append((side, code_bound_side(base, exact=exact and dim<=4)))
    return out

if __name__=="__main__":
    if sys.argv[1]=="--root":
        t=[[0]*9 for _ in range(9)]
        for i in range(3):
            for j in range(3):
                for k in range(3):
                    t[3*i+j][3*j+k]|=1<<(3*k+i)
        print("root <3,3,3>:", bound_all(t,9,9,9,exact=False))
        sys.exit()
    from collections import Counter
    tally=Counter(); lines=0
    for line in open(sys.argv[1]):
        f=line.split(); v=f[0]; k=int(f[1]); da,db,dc=map(int,f[2:5])
        t=[[int(f[5+a*db+b],16) for b in range(db)] for a in range(da)]
        res=bound_all(t,da,db,dc)
        best_lp=max(r[1][0] for r in res); best_ilp=max((r[1][1] or 0) for r in res)
        cert = "certified" if max(best_lp,best_ilp)>=k else "no"
        tally[(v,cert)]+=1; lines+=1
        if lines<=8 or (v=="genuine" and cert=="certified"):
            print(f"  {v} k={k} dims {da}x{db}x{dc}: sides {[(s,lp,il) for s,(lp,il) in res]} -> {cert}")
    print("\nTALLY:", dict(tally))
