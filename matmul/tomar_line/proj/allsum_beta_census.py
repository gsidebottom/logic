#!/usr/bin/env python3
"""Rank-one census of every member of the all-sum family of an F2 scheme.
(Prior art: the move is the block flip of LITA -- K. Khoruzhii, L. Serafin, P. Gelss, S. Pokutta, "Local
Improvements to Trilinear Aggregation", github.com/khoruzhii/lita: a rank-one element u' (x) v' of the span of the
pair factors X_t = u_t (x) v_t replaces one of them.  "All-sum" is the case where it is the sum of all X_t.)

A scheme whose all-sum in direction d is rank one (x (x) y) sits in the family
    S_beta = {a_t (x) (b_t + beta) (x) c_t} + {x (x) beta (x) y},   beta any vector of slot d   (written for d = the b slot)
with one more product (the same number when beta is a slot-d factor of the scheme).  For every beta in [LO, HI) this runs
kres --census on S_beta and, in the two OTHER directions dd, records
  * the Kronecker deficit (products - dim G; a deficit drops a product at once),
  * every extra rank-one element of G (index set J, |J| >= 2): a translation of the slot-dd factors of J by any vector g
    leaves the tensor fixed after adding the product (x', g, y'); g = a slot-dd factor of J kills that product, and kills
    c of them when c products of J share it -- c >= 2 is a rank reduction ("REDUCING").
usage: allsum_beta_census.py N scheme.bits KRES WORKDIR LO HI [--workers W] [--extras FILE]
"""
import sys, os, re, subprocess, json
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from allsum_flip import load, dump, allsum, rank_rows

RC = [(1, 2), (0, 2), (0, 1)]
HEAD = re.compile(r' d=(\d): products (\d+), dim G (\d+), dependencies (\d+), rank-one elements (\d+) \(originals (\d+), extra (\d+)\)')
EXTRA = re.compile(r'^\s+EXTRA \|J\|=(\d+) x=\S+ y=\S+ J=\[([0-9, ]*)\]')

def member(prods, d, x, y, beta):
    r, c = RC[d]
    S = []
    for p in prods:
        q = list(p); q[d] ^= beta
        if q[d]: S.append(q)
    if beta:
        q = [0, 0, 0]; q[r] = x; q[c] = y; q[d] = beta; S.append(q)
    return S

def work(args):
    n, w, prods, d, x, y, kres, workdir, lo, hi = args
    os.nice(15)
    path = os.path.join(workdir, f'w{os.getpid()}.bits')
    out = []
    for beta in range(lo, hi):
        S = member(prods, d, x, y, beta)
        with open(path, 'w') as f:
            f.write(dump(S, w) + '\n')
        txt = subprocess.run([kres, str(n), str(n), str(n), path, '--census'], capture_output=True, text=True, timeout=600).stdout
        cur = None
        rec = {'beta': beta, 'products': len(S), 'dirs': {}}
        for line in txt.splitlines():
            m = HEAD.search(line)
            if m:
                cur = int(m.group(1))
                rec['dirs'][cur] = {'dim': int(m.group(3)), 'originals': int(m.group(6)), 'extra': int(m.group(7)), 'J': []}
                assert int(m.group(2)) == len(S)
                continue
            m = EXTRA.match(line)
            if m and cur is not None:
                J = [int(v) for v in m.group(2).split(',') if v.strip()]
                assert len(J) == int(m.group(1))
                # products of J sharing their slot-`cur` factor: translating by it kills them all
                f = {}
                for t in J: f[S[t][cur]] = f.get(S[t][cur], 0) + 1
                rec['dirs'][cur]['J'].append((J, max(f.values())))
        assert len(rec['dirs']) == 3, txt[:400]
        out.append(rec)
    return out

if __name__ == '__main__':
    n = int(sys.argv[1]); w = n * n
    prods = load(sys.argv[2], w)
    kres, workdir = sys.argv[3], sys.argv[4]
    lo, hi = int(sys.argv[5]), int(sys.argv[6])
    workers = int(sys.argv[sys.argv.index('--workers') + 1]) if '--workers' in sys.argv else 4
    extras = sys.argv[sys.argv.index('--extras') + 1] if '--extras' in sys.argv else None
    d = next(dd for dd in range(3) if rank_rows(allsum(prods, dd, w)) == 1)
    rows = allsum(prods, d, w)
    y = next(v for v in rows if v); x = sum(1 << i for i in range(w) if rows[i])
    os.makedirs(workdir, exist_ok=True)
    step = 64
    tasks = [(n, w, prods, d, x, y, kres, workdir, a, min(a + step, hi)) for a in range(lo, hi, step)]
    hist, jhist, nred, done = {}, {}, 0, 0
    ef = open(extras, 'w') if extras else None
    print(f'family direction d={d}; beta in [{lo}, {hi}); {workers} workers', flush=True)
    with Pool(workers) as pool:
        for recs in pool.imap_unordered(work, tasks):
            for rec in recs:
                for dd, v in rec['dirs'].items():
                    if dd == d: continue
                    key = (rec['products'], dd, rec['products'] - v['dim'], v['extra'])
                    hist[key] = hist.get(key, 0) + 1
                    for J, c in v['J']:
                        jhist[(rec['products'], dd, len(J), c)] = jhist.get((rec['products'], dd, len(J), c), 0) + 1
                        if c >= 2:
                            nred += 1
                            print(f'REDUCING beta={rec["beta"]} direction {dd}: |J|={len(J)}, {c} products of J share the factor: J={J}', flush=True)
                        if ef: ef.write(json.dumps({'beta': rec['beta'], 'dd': dd, 'J': J, 'c': c}) + '\n')
                    if rec['products'] - v['dim'] > 0:
                        print(f'DEFICIT beta={rec["beta"]} direction {dd}: {rec["products"]} products, dim G {v["dim"]}', flush=True)
            done += len(recs)
            if done % 8192 == 0: print(f'  .. {done} members done', flush=True)
    if ef: ef.close()
    print('members:', done)
    print('hist (products, direction, deficit, extras) -> members:', sorted(hist.items()))
    print('extras (products, direction, |J|, products sharing the factor) -> count:', sorted(jhist.items()))
    print('reducing extras:', nred)
