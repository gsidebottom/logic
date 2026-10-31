# Score Sedoglavic's 160 decompositions: exact Brent, floors and non-units (orbit48's proxy), nonzeros,
# canonical rows, and the best PLinOpt totals he recorded in summary*.txt.
import sys, os, re, glob, csv, collections
sys.path.append('/Users/greg/Library/Python/3.9/lib/python/site-packages')
D = '/Users/greg/projects/logic/matmul/dps48'; sys.path.insert(0, D)
import numpy as np
import orbit48 as O
SP, out = sys.argv[1], sys.argv[2]
pts = sorted({os.path.basename(p)[:-6] for p in glob.glob(f"{SP}/td/pts/*_L.sms")})
def summ(path):
    d, tag, side = {}, None, None
    for ln in open(path):
        ln = re.sub(r'\x1b\[[0-9;]*m', '', ln).strip()
        if ln.startswith('res_4x4x4'): tag = ln.replace('res_4x4x4_48_202_', '').replace('_shortRun', ''); d[tag] = {}
        elif ln in 'LRP' and ln: side = ln
        elif ln.endswith('Total') and tag: d[tag][side] = int(ln.split()[0])
    return d
s1, s2 = summ(f"{SP}/td/summary.txt"), summ(f"{SP}/td/summary_shortrun.txt")
rows, bad = [], []
E = np.zeros((4,) * 6, dtype=np.int64)
for a, b, c in __import__('itertools').product(range(4), repeat=3): E[a, b, b, c, a, c] = O.SCAL ** 3
for t in pts:
    try: U, V, W = O.load(f"{SP}/td/pts/{t}")
    except AssertionError as e: bad.append((t, str(e))); continue
    ok = np.array_equal(np.einsum('kab,kcd,kef->abcdef', U.astype(np.int64), V.astype(np.int64), W.astype(np.int64)), E)
    _, floor, (fl, fr, fp), nu = O.objective(U, V, W, 0)
    can = [sum(1 for k in range(48) if np.count_nonzero(M[k]) == 1) for M in (U, V, W)]
    nz = [int(np.count_nonzero(M)) for M in (U, V, W)]
    den = max(int(np.max(np.abs(M))) for M in (U, V, W)) / O.SCAL
    fin = min(sorted({abs(int(x)) for M in (U, V, W) for x in M.ravel() if x}))/O.SCAL
    b = {s: min(x.get(t, {}).get(s, 10 ** 6) for x in (s1, s2)) for s in 'LRP'}
    fam = '_'.join(t.split('_')[:2]) + '_' + t.split('_')[-1]
    rows.append(dict(tag=t, fam=fam, brent=int(ok), nl=nz[0], nr=nz[1], np=nz[2], nnz=sum(nz), cl=can[0], cr=can[1], cp=can[2], fl=fl, fr=fr, fp=fp, floor=floor, nonunit=nu, maxabs=den, minabs=fin, pl=b['L'], pr=b['R'], pp=b['P'], ptot=sum(b.values())))
w = csv.DictWriter(open(out, 'w', newline=''), fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)
print(f"{len(rows)} points scored, {len(bad)} unreadable, Brent exact on {sum(r['brent'] for r in rows)}")
for b_ in bad[:5]: print("  bad:", b_)
print(f"{'family':12s} {'n':>3s} {'nnz':>9s} {'canon':>10s} {'side floors L/R/Pt':>24s} {'floor':>9s} {'nonunit':>9s} {'plinopt L':>9s} {'R':>7s} {'P':>8s} {'total':>9s} {'max|x|':>6s}")
fams = collections.defaultdict(list)
for r in rows: fams[r['fam']].append(r)
rng = lambda f, k: (lambda v: f"{min(v)}-{max(v)}" if min(v) != max(v) else str(min(v)))([r[k] for r in f])
for n, f in sorted(fams.items()):
    print(f"{n:12s} {len(f):3d} {rng(f,'nnz'):>9s} {rng(f,'cl')+'/'+rng(f,'cr')+'/'+rng(f,'cp'):>10s} {rng(f,'fl')+' / '+rng(f,'fr')+' / '+rng(f,'fp'):>24s} {rng(f,'floor'):>9s} {rng(f,'nonunit'):>9s} {rng(f,'pl'):>9s} {rng(f,'pr'):>7s} {rng(f,'pp'):>8s} {rng(f,'ptot'):>9s} {max(r['maxabs'] for r in f):6.2f}")
print("\nreference points:")
for n, p in (("lam01c0_201", f"{D}/cand48/lam01c0_201"), ("p005_201", f"{D}/cand48/p005_201n"), ("203 files", f"{SP}/rfc2610/files/4x4x4_48_203"), ("204", f"{SP}/plinopt_main/data/4x4x4_48_204"), ("202", f"{SP}/plinopt_main/data/4x4x4_48_202"), ("accurate_262", f"{SP}/plinopt_main/data/4x4x4_48_accurate_262")):
    try:
        U, V, W = O.load(p); _, floor, fs, nu = O.objective(U, V, W, 0)
        print(f"  {n:13s} nnz {[int(np.count_nonzero(M)) for M in (U, V, W)]} sum {sum(int(np.count_nonzero(M)) for M in (U, V, W))} canon {[sum(1 for k in range(48) if np.count_nonzero(M[k]) == 1) for M in (U, V, W)]} floors {fs} floor {floor} nonunit {nu}")
    except Exception as e: print(f"  {n}: {type(e).__name__} {e}")
