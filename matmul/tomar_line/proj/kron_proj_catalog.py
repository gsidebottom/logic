#!/usr/bin/env python3
"""Every single-index projection of every scheme of a catalog, reduced by the pivot search (a screen modulo p).

Deleting one row/column index (I: rows of A, J: columns of A = rows of B, K: columns of B) restricts a scheme
for <n0, n1, n2> to a shape with one dimension less; products with a zero factor vanish.  When the Kronecker
products of two slots of the projected scheme are dependent (LITA's 2-reducibility, github.com/khoruzhii/lita),
kron_kill.trial looks for the reduction that leaves the fewest products.  The outcome is compared with the
catalog's best rank of the smaller shape in every ring.  Everything is modulo one 20-bit prime: a hit is a claim
that kron_project.py + kron_reduce.py --pivots must repeat exactly over Q.

Files are taken in order of size (below --bigm products), then by the distance of their rank from the best
neighbouring record.  --resume skips the files listed in OUT.csv.done.
usage: kron_proj_catalog.py SCHEMES_DIR STATUS.json OUT.csv [--workers W] [--minm A] [--maxm B] [--bigm M]
                            [--skip DIR,DIR] [--bar SHAPE=RANK,...] [--walk W] [--only I0] [--resume]
"""
import sys, os, re, json, csv, time, zlib
from multiprocessing import Pool
os.environ.setdefault('VECLIB_MAXIMUM_THREADS', '1')
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kron_fast as kf, kron_chain as kc, kron_kill as kk

G = {}

def init(best, walk, only):
    os.nice(15); G['best'] = best; G['walk'] = walk; G['only'] = only

def work(path):
    t0 = time.time(); best = G['best']
    try:
        n, X = kc.load_scheme_mod(path)
    except Exception as e:
        return path, f'UNREADABLE ({type(e).__name__}: {str(e)[:60]})', [], 0.0
    if len(n) != 3 or any(x.shape[0] != X[0].shape[0] for x in X): return path, 'UNREADABLE (layout)', [], 0.0
    m = X[0].shape[0]; rows = []; rng = np.random.default_rng(zlib.crc32(path.encode()))
    for s in range(3):
        if n[s] < 2: continue
        for i in range(n[s]):
            if G['only'] and G['only'] != ('IJK'[s], i): continue
            n2 = tuple(n[t] - (t == s) for t in range(3)); key = 'x'.join(map(str, sorted(n2)))
            b = best.get(key)
            if b is None: continue
            keep = [[j for j in range(n[t]) if not (t == s and j == i)] for t in range(3)]
            Y, alive = kf.project_mod(n, X, keep); a = int(len(alive))
            if a == 0: continue
            rk = [int(r) for r in kf.kron_ranks(Y)]; null = a - min(rk); mout = a; steps = ''; bad = ''
            if null > 0:
                Z, pth = kk.trial(n2, [y.copy() for y in Y], rng, walk=G['walk'], restarts=1)
                mout = int(Z[0].shape[0]); bad = int(kc.brent_mod(n2, Z))
                steps = ' '.join(f"d{st['direction']}:{st['nullity']}dep:{st['m'] - st['m_out']}gone" for st in pth)
            rows.append([key, 'IJK'[s], i, a, rk[0], rk[1], rk[2], null, mout, bad, steps, b.get('Q'), b.get('Z'), b.get('ZT')])
    return path, 'ok', rows, time.time() - t0

if __name__ == '__main__':
    args = sys.argv[1:]; opt = {'--workers': 2, '--minm': 0, '--maxm': 10 ** 9, '--bigm': 1000, '--skip': '', '--bar': '', '--walk': 100, '--only': ''}
    resume = '--resume' in args
    if resume: args.remove('--resume')
    for key in list(opt):
        if key in args:
            i = args.index(key); v = args[i + 1]; del args[i:i + 2]; opt[key] = v if key in ('--skip', '--bar', '--only') else int(v)
    root, status_path, out = args
    status = json.load(open(status_path))
    best = {k: dict(v['ranks']) for k, v in status.items() if isinstance(v, dict) and 'ranks' in v}
    for item in filter(None, opt['--bar'].split(',')):
        k, v = item.split('='); best[k]['Q'] = min(best[k].get('Q', 10 ** 9), int(v))
    skip = set(filter(None, opt['--skip'].split(',')))
    done = set()
    if resume and os.path.exists(out + '.done'): done = set(open(out + '.done').read().split('\n'))
    jobs = []
    for dp, dn, fn in os.walk(root):
        if skip & set(os.path.relpath(dp, root).split(os.sep)): continue
        for f in fn:
            mm = re.match(r'^(\d+)x(\d+)x(\d+)_m(\d+).*\.json$', f)
            if not mm: continue
            n = [int(mm.group(i)) for i in (1, 2, 3)]; m = int(mm.group(4)); p = os.path.join(dp, f)
            if not (opt['--minm'] <= m <= opt['--maxm']) or os.path.relpath(p, root) in done: continue
            gap = 10 ** 9
            for s in range(3):
                b = best.get('x'.join(map(str, sorted(n[t] - (t == s) for t in range(3)))))
                if b: gap = min(gap, m - max(b.values()))
            if gap == 10 ** 9: continue
            jobs.append(((m >= opt['--bigm'], gap if m >= opt['--bigm'] else m, m), p))
    jobs.sort(); paths = [p for _, p in jobs]
    print(f'{len(paths)} scheme files under {root} ({len(done)} done before); {opt["--workers"]} workers; walk {opt["--walk"]}', flush=True)
    t0 = time.time(); nfiles = ndef = ncand = 0; new = not (resume and os.path.exists(out))
    with Pool(opt['--workers'], initializer=init, initargs=(best, opt['--walk'], (opt['--only'][0], int(opt['--only'][1:])) if opt['--only'] else None)) as pool, open(out, 'w' if new else 'a', newline='') as fh, open(out + '.done', 'a') as dh:
        wr = csv.writer(fh)
        if new: wr.writerow(['source', 'shape', 'slot', 'index', 'alive', 'rk0', 'rk1', 'rk2', 'nullity', 'm_out', 'brent_wrong', 'steps', 'best_Q', 'best_Z', 'best_ZT'])
        for p, state, rows, dt in pool.imap_unordered(work, paths, chunksize=1):
            rel = os.path.relpath(p, root); nfiles += 1
            ring = re.search(r'_(Q|ZT|Z)(?=[_.])', os.path.basename(p))      # a scheme can only set a record in its own ring or a larger one
            allowed = {'Q': ('Q',), 'Z': ('Q', 'Z'), 'ZT': ('Q', 'Z', 'ZT')}.get(ring.group(1) if ring else None, ('Q', 'Z', 'ZT'))
            if state != 'ok': print(f'{rel}: {state}', flush=True)
            hits = []
            for row in rows:
                wr.writerow([rel] + row)
                key, slot, i, a, r0, r1, r2, null, mout, bad, steps, bq, bz, bt = row
                if bad not in ('', 0): print(f'{rel}: {key} del {slot}[{i}]: BRENT FAILS modulo p ({bad} wrong entries) -- ignore this row and investigate', flush=True); continue
                if null > 0: ndef += 1
                cols = [(r, v) for r, v in (('Q', bq), ('Z', bz), ('ZT', bt)) if r in allowed and v is not None]
                beats = [r for r, v in cols if mout < v]; ties = [r for r, v in cols if mout == v]
                if beats:
                    note = '' if beats == ['Q'] or null == 0 else ' (Z/ZT only if the reduction keeps the ring)'
                    hits.append(f'  {key} del {slot}[{i}]: {a} alive, ranks [{r0}, {r1}, {r2}], {steps or "no reduction"} -> {mout}; catalog Q {bq} Z {bz} ZT {bt}   <<< BELOW {"/".join(beats)}{note}')
                elif null > 0 and ties:
                    hits.append(f'  {key} del {slot}[{i}]: {a} alive, {steps} -> {mout}; catalog Q {bq} Z {bz} ZT {bt}   (ties {"/".join(ties)})')
            fh.flush(); dh.write(rel + '\n'); dh.flush()
            if hits:
                ncand += sum('<<<' in h for h in hits)
                print(f'{rel} ({dt:.0f} s):', flush=True)
                for h in hits: print(h, flush=True)
            if nfiles % 100 == 0: print(f'... {nfiles} files, {ndef} deficient projections, {ncand} below a catalog rank, {time.time() - t0:.0f} s', flush=True)
    print(f'done: {nfiles} files, {ndef} deficient projections, {ncand} below a catalog rank, {time.time() - t0:.0f} s', flush=True)
