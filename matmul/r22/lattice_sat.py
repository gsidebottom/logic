#!/usr/bin/env python3
"""Does a 20-product decomposition of <3,3,3> over F2 survive Wang's codim-1
and codim-2 values plus the slice-rank constraints?  At r = 20 every
A-coefficient type appears at most once (codim-1: sum_{c != v} m_c >= 19), so
the type set S is a 20-subset of F2^9 \\ 0 with:
  - no 19-orbit pencil contains two elements of S (sum_{c not in U} >= 19),
  - no 18-orbit pencil contains all three of its nonzero vectors in S,
  - for every covector phi: |{c in S : <c,phi> = 1}| >= 3 rank(phi).
UNSAT  =>  the lattice integer program's optimum is 21  =>  rank >= 21.
Encoding: x_c booleans, sequential counters for the cardinalities."""
import sys, subprocess, itertools, time
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
nv=[511]; cls=[]
x=lambda c: c            # variable for vector c in 1..511
def new():
    nv[0]+=1; return nv[0]
def at_most_k(lits, k):
    """sequential counter: sum lits <= k"""
    n=len(lits)
    if k>=n: return
    if k==0:
        for l in lits: cls.append([-l]); return
    s=[[new() for _ in range(k)] for _ in range(n)]
    cls.append([-lits[0], s[0][0]])
    for j in range(1,k): cls.append([-s[0][j]])
    for i in range(1,n):
        cls.append([-lits[i], s[i][0]]); cls.append([-s[i-1][0], s[i][0]])
        for j in range(1,k):
            cls.append([-lits[i], -s[i-1][j-1], s[i][j]]); cls.append([-s[i-1][j], s[i][j]])
        cls.append([-lits[i], -s[i-1][k-1]])
def at_least_k(lits, k):
    at_most_k([-l for l in lits], len(lits)-k)
# exactly 20 chosen
allv=list(range(1,512))
at_most_k([x(c) for c in allv], 20); at_least_k([x(c) for c in allv], 20)
n18=n19=0
for line in open('matmul/r22/lattice_values.txt'):
    f=line.split()
    if f[0]!='2': continue
    a,b,t=int(f[1]),int(f[2]),int(f[3]); c=a^b
    if t==19:
        n19+=1
        for u,v in ((a,b),(a,c),(b,c)): cls.append([-x(u),-x(v)])
    else:
        n18+=1; cls.append([-x(a),-x(b),-x(c)])
for phi in range(1,512):
    lits=[x(c) for c in allv if bin(c&phi).count('1')%2==1]
    at_least_k(lits, 3*rank3(phi))
# codim-3 (optional, --dim3 FILE): at most 20 - t_U of the 7 nonzero vectors of U
n3=0
if "--dim3" in sys.argv:
    path3=sys.argv[sys.argv.index("--dim3")+1]
    for line in open(path3):
        f=line.split()
        if f[0]!='3': continue
        a,b,c,t=int(f[1]),int(f[2]),int(f[3]),int(f[4])
        if t==0: continue
        els=[a,b,c,a^b,a^c,b^c,a^b^c]
        k=20-t
        if k>=7: continue
        n3+=1
        for sub in itertools.combinations(els,k+1):
            cls.append([-x(e) for e in sub])
    print(f"codim-3 constraints: {n3} subspaces", flush=True)
path='matmul/r22/lattice20_dim3.cnf' if '--dim3' in sys.argv else 'matmul/r22/lattice20.cnf'
with open(path,'w') as f:
    f.write(f"p cnf {nv[0]} {len(cls)}\n")
    for c in cls: f.write(" ".join(map(str,c))+" 0\n")
print(f"CNF: {nv[0]} vars, {len(cls)} clauses ({n19} 19-pencils, {n18} 18-pencils, 511 slice constraints)", flush=True)
tmo=int(sys.argv[1]) if len(sys.argv)>1 and sys.argv[1].isdigit() else 1800
t0=time.time()
try:
    out=subprocess.run(["cadical","-q",path],capture_output=True,text=True,timeout=tmo)
    res="SAT" if out.returncode==10 else "UNSAT" if out.returncode==20 else f"rc{out.returncode}"
    if res=="SAT":
        model=[int(t) for l in out.stdout.splitlines() if l.startswith("v") for t in l.split()[1:]]
        S=sorted(v for v in model if 0<v<=511)
        print("a 20-set:", S, "ranks:", sorted(rank3(c) for c in S), flush=True)
except subprocess.TimeoutExpired:
    res="TIMEOUT"
print(f"cadical: {res} [{time.time()-t0:.0f}s]", flush=True)
