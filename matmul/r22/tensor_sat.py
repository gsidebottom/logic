# CNF for "k x n x n tensor X over F2 has rank <= r", solved by cadical/kissat.
import subprocess, sys, time, random, itertools, os
def encode(X, k, n, r, symbreak=True):
    nv=[0]; cls=[]
    def new():
        nv[0]+=1; return nv[0]
    a=[[new() for s in range(k)] for i in range(r)]
    b=[[new() for j in range(n)] for i in range(r)]
    c=[[new() for l in range(n)] for i in range(r)]
    # lexicographic ordering of products: encode a_i as integer (k bits) nonzero, and
    # forbid a_i == 0 (a zero-alpha product is useless); order by a-value non-decreasing? skip (cheap sym-break only)
    for i in range(r):
        cls.append([a[i][s] for s in range(k)])  # alpha nonzero
        cls.append([b[i][j] for j in range(n)])
        cls.append([c[i][l] for l in range(n)])
    def and3(x,y,z):
        t=new()
        cls.append([-t,x]); cls.append([-t,y]); cls.append([-t,z]); cls.append([t,-x,-y,-z]); return t
    def xor_eq(lits, val):
        # chain: acc = lits[0] ^ lits[1] ^ ...; assert acc == val
        acc=lits[0]
        for u in lits[1:]:
            t=new()
            # t = acc ^ u
            cls.append([-t,acc,u]); cls.append([-t,-acc,-u]); cls.append([t,-acc,u]); cls.append([t,acc,-u])
            acc=t
        cls.append([acc] if val else [-acc])
    for s in range(k):
        for j in range(n):
            for l in range(n):
                ts=[and3(a[i][s],b[i][j],c[i][l]) for i in range(r)]
                xor_eq(ts, X[s][j]>>l&1)
    return nv[0], cls
def solve(X,k,n,r,solver="cadical",timeout=600):
    nv,cls=encode(X,k,n,r)
    path=f"/tmp/ts_{os.getpid()}.cnf"
    with open(path,"w") as f:
        f.write(f"p cnf {nv} {len(cls)}\n")
        for c in cls: f.write(" ".join(map(str,c))+" 0\n")
    t0=time.time()
    try:
        out=subprocess.run([solver,"-q",path] if solver=="cadical" else [solver,"-q",path],capture_output=True,text=True,timeout=timeout)
        res="SAT" if out.returncode==10 else "UNSAT" if out.returncode==20 else f"rc{out.returncode}"
    except subprocess.TimeoutExpired:
        res="TIMEOUT"
    return res, time.time()-t0
def rank_exact(X,k,n,lo,hi,solver="cadical"):
    # smallest r in [lo,hi] with SAT
    for r in range(lo,hi+1):
        res,dt=solve(X,k,n,r,solver,timeout=60)
        print(f"   r={r}: {res} {dt:.2f}s", flush=True)
        if res=="SAT": return r
    return None
if __name__=="__main__":
    n=9; random.seed(7)
    # (a) constructed: 3 copies of L_2 (2x3 blocks: A=[[1,0,0],[0,1,0]], B=[[0,1,0],[0,0,1]]) padded to 9x9 -> rank 9, all combos rank 6
    A=[0]*9; B=[0]*9
    for blk in range(3):
        r0=2*blk; c0=3*blk
        A[r0]|=1<<(c0); A[r0+1]|=1<<(c0+1)
        B[r0]|=1<<(c0+1); B[r0+1]|=1<<(c0+2)
    print("3 x L_2 (expected rank 9):", flush=True); rank_exact([A,B],2,n,7,9)
    # (b) random regular pencils
    for trial in range(3):
        A=[random.randrange(1<<n) for _ in range(n)]; B=[random.randrange(1<<n) for _ in range(n)]
        print(f"random pencil {trial}:", flush=True); rank_exact([A,B],2,n,8,11)
    # (c) random 3-slice
    for trial in range(2):
        X=[[random.randrange(1<<n) for _ in range(n)] for _ in range(3)]
        print(f"random 3-slice {trial}:", flush=True); rank_exact(X,3,n,9,12)
