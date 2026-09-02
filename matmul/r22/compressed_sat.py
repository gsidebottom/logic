#!/usr/bin/env python3
"""SAT feasibility on COMPRESSED hard residuals (2026-09-02): each dumped
residual (k slices on its thinnest side) is rewritten in bases of its row
and column spans (k x cs x rs), then 'rank <= target-1' (the refutation
the probe would need) and 'rank <= target' are handed to cadical."""
import sys, re, random, time, os, subprocess
sys.path.insert(0, os.path.dirname(__file__))
from tensor_sat import encode
def rank_basis(vecs, n=9):
    rows=list(vecs); rk=0
    for c in range(n-1,-1,-1):
        piv=next((i for i in range(rk,len(rows)) if rows[i]>>c&1),None)
        if piv is None: continue
        rows[rk],rows[piv]=rows[piv],rows[rk]
        for i in range(len(rows)):
            if i!=rk and rows[i]>>c&1: rows[i]^=rows[rk]
        rk+=1
    return rows[:rk]  # rref basis
def coords(v, basis):
    # basis is rref (distinct leading bits); coordinates of v
    out=0
    for i,b in enumerate(basis):
        lb=b.bit_length()-1
        if v>>lb&1: v^=b; out|=1<<i
    assert v==0
    return out
def transpose(m, n=9):
    t=[0]*n
    for i in range(n):
        for j in range(n):
            if m[i]>>j&1: t[j]|=1<<i
    return t
def compress(slices):
    Q=rank_basis([r for m in slices for r in m]); rs=len(Q)
    A=[[coords(r,Q) for r in m] for m in slices]          # 9 x rs, rows in Q-coords
    # column space: columns of A_i are vectors in F^9 -> transpose A_i (rs x 9)
    At=[transpose_rect(a,9,rs) for a in A]                # rs rows of 9 bits
    P=rank_basis([r for at in At for r in at]); cs=len(P)
    C=[[coords(r,P) for r in at] for at in At]            # rs x cs (row c of C_i = column c of A_i in P-coords)
    # tensor entries: X[s][j][l] with j in cs, l in rs: C_i[l] bit j
    X=[[0]*cs for _ in slices]
    for s in range(len(slices)):
        for l in range(rs):
            for j in range(cs):
                if C[s][l]>>j&1: X[s][j]|=1<<l
    return X, cs, rs
def transpose_rect(rows, ncols, nrows_out):
    t=[0]*nrows_out
    for i,r in enumerate(rows):
        for j in range(nrows_out):
            if r>>j&1: t[j]|=1<<i
    return t
def solve_rect(X,k,m,n,r,timeout):
    # reuse tensor_sat.encode with square n: pad m up to n if needed
    nn=max(m,n)
    Xp=[[X[s][j] if j<m else 0 for j in range(nn)] for s in range(k)]
    nv,cls=encode(Xp,k,nn,r)
    path=f"/tmp/cs_{os.getpid()}.cnf"
    with open(path,"w") as f:
        f.write(f"p cnf {nv} {len(cls)}\n")
        for c in cls: f.write(" ".join(map(str,c))+" 0\n")
    t0=time.time()
    try:
        out=subprocess.run(["cadical","-q",path],capture_output=True,text=True,timeout=timeout)
        res="SAT" if out.returncode==10 else "UNSAT" if out.returncode==20 else f"rc{out.returncode}"
    except subprocess.TimeoutExpired:
        res="TIMEOUT"
    return res, time.time()-t0
pat=re.compile(r"(\w+) depth (\S+) target (\d+) folds (\S+) flatten \[([^\]]*)\] koszul (\d+) slices (.*)")
recs=[]
for line in open(sys.argv[1]):
    m=pat.match(line.strip())
    if not m: continue
    kind,depth,target,folds,flat,kos,rest=m.groups()
    slices=[[int(tok[3*j:3*j+3],16) for j in range(9)] for tok in rest.split()]
    recs.append((kind,depth,int(target),int(kos),slices,folds))
random.seed(3)
per=int(sys.argv[2]) if len(sys.argv)>2 else 4
tmo=int(sys.argv[3]) if len(sys.argv)>3 else 120
by={}
for r in recs:
    if r[0]=="hard": by.setdefault(r[1],[]).append(r)
for depth,rs_ in sorted(by.items(), key=lambda kv:-len(kv[1])):
    if len(rs_)<20: continue
    sample=random.sample(rs_,min(per,len(rs_)))
    for kind,d,target,kos,slices,folds in sample:
        X,cs,rs=compress(slices)
        k=len(slices)
        print(f"pattern {d} target {target} koszul {kos} {folds}: compressed {k}x{cs}x{rs}", flush=True)
        for r in (target-1, target):
            res,dt=solve_rect(X,k,cs,rs,r,tmo)
            print(f"   rank<={r}: {res} {dt:.1f}s", flush=True)
            if res=="SAT": break
