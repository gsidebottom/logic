# Ground truth vs formula for REGULAR pencils (I, A) over F2, small n.
# rank(I,A) = min_X rank(X)+rank(I+X)+rank(A+X)  (terms grouped by alpha-type)
# Formula (Ja'Ja' 1979): n + m, m = # invariant factors of A that are not a
# product of DISTINCT LINEAR factors over F2.
import random, itertools, sys
def rank(rows, n):
    rows=list(rows); rk=0
    for c in range(n-1,-1,-1):
        piv=next((i for i in range(rk,len(rows)) if rows[i]>>c&1),None)
        if piv is None: continue
        rows[rk],rows[piv]=rows[piv],rows[rk]
        for i in range(len(rows)):
            if i!=rk and rows[i]>>c&1: rows[i]^=rows[rk]
        rk+=1
    return rk
def matmul(A,B,n):
    C=[]
    for i in range(n):
        r=0
        for j in range(n):
            if A[i]>>(n-1-j)&1: r^=B[j]
        C.append(r)
    return C
def brute(A,n):
    I=[1<<(n-1-i) for i in range(n)]
    best=10**9
    for bits in range(1<<(n*n)):
        X=[(bits>>(n*i))&((1<<n)-1) for i in range(n)]
        v=rank(X,n)+rank([I[i]^X[i] for i in range(n)],n)+rank([A[i]^X[i] for i in range(n)],n)
        if v<best: best=v
    return best
# polynomials over F2 as ints (bit i = coeff of x^i)
def pmul(a,b):
    r=0
    while b:
        if b&1: r^=a
        a<<=1; b>>=1
    return r
def pmod(a,m):
    dm=m.bit_length()-1
    while a and a.bit_length()-1>=dm:
        a^=m<<(a.bit_length()-1-dm)
    return a
def irreducibles(maxdeg):
    out=[]
    for d in range(1,maxdeg+1):
        for p in range(1<<d, 1<<(d+1)):
            if all(pmod(p,q)!=0 for q in out if q.bit_length()-1<=d//2): out.append(p)
    return out
def polyA(p,A,n):
    # p(A) as matrix
    I=[1<<(n-1-i) for i in range(n)]
    R=[0]*n; P=I
    for i in range(p.bit_length()):
        if p>>i&1: R=[R[j]^P[j] for j in range(n)]
        P=matmul(P,A,n)
    return R
def invariant_factors(A,n):
    # elementary divisors via ranks of p(A)^j; then invariant factors
    ed={}
    for p in irreducibles(n):
        d=p.bit_length()-1
        M=polyA(p,A,n); prev=n; sizes=[]
        # number of blocks of size >= j = (rank p(A)^{j-1} - rank p(A)^j)/d
        P=[1<<(n-1-i) for i in range(n)]; ranks=[n]
        for j in range(1,n+1):
            P=matmul(P,M,n); ranks.append(rank(P,n))
            if ranks[-1]==ranks[-2]: break
        ge=[(ranks[j-1]-ranks[j])//d for j in range(1,len(ranks))]
        blocks=[]
        for j in range(len(ge)):
            cnt=ge[j]-(ge[j+1] if j+1<len(ge) else 0)
            blocks+= [j+1]*cnt
        if blocks: ed[p]=sorted(blocks,reverse=True)
    k=max(len(v) for v in ed.values())
    inv=[]
    for i in range(k):
        inv.append({p:v[i] for p,v in ed.items() if i<len(v)})
    return inv
def formula(A,n):
    inv=invariant_factors(A,n)
    m=sum(1 for q in inv if any(e>=2 or p.bit_length()-1>=2 for p,e in q.items()))
    return n+m
random.seed(1)
for n in (2,3,4):
    bad=0; tested=0; dist={}
    for _ in range(60 if n==4 else 200):
        A=[random.randrange(1<<n) for _ in range(n)]
        b=brute(A,n); f=formula(A,n); tested+=1
        dist[(b,f)]=dist.get((b,f),0)+1
        if b!=f: bad+=1; print("MISMATCH n=%d A=%s brute %d formula %d inv %s"%(n,A,b,f,invariant_factors(A,n)))
    print(f"n={n}: tested {tested}, mismatches {bad}, (brute,formula) counts {dist}")
