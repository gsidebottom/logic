#!/usr/bin/env python3
"""Chains of single-index deletions of one scheme with the pivot search after every deletion (a screen modulo p).

A sequence such as I0,J3 deletes row index 0 of A, reduces the projected scheme with kron_kill.trial when the
Kronecker products of two slots are dependent (LITA's 2-reducibility, github.com/khoruzhii/lita), then deletes
index 3 of the columns of A (= rows of B) OF THE CURRENT SCHEME and reduces again.  --mode end reduces only after
the last deletion.  The outcome is compared with the catalog's best rank of the final shape.  Everything is modulo
one 20-bit prime: a hit must be repeated exactly, stage by stage, with kron_project.py and kron_reduce.py --pivots
(the path file that --paths writes holds each stage's deletions, direction and pivots; for the exact replay run
kron_kill.py on each exact projection, since a file's product order can differ from the modular run's).

SEQS is a list of sequences separated by ';' or one of the generators
    next:PREFIX   every one-more deletion after the prefix (all slots, all indices); PREFIX may be empty
    pairs         every unordered pair of deletions (indices of the ORIGINAL scheme, larger index of a slot first)
A stage's random choices depend only on the source name and the sequence up to that stage, so runs repeat.
usage: kron_proj_multi.py SCHEME.json STATUS.json OUT.csv SEQS [--workers W] [--walk W] [--restarts R]
                          [--mode each|end] [--paths DIR] [--bar SHAPE=RANK,...]
"""
import sys, os, re, json, csv, time, zlib
from multiprocessing import Pool
os.environ.setdefault('VECLIB_MAXIMUM_THREADS', '1')
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kron_fast as kf, kron_chain as kc, kron_kill as kk

G = {}

def init(path, walk, restarts, mode):
    os.nice(15); G.update(path=path, walk=walk, restarts=restarts, mode=mode, cache={})
    G['n'], G['X'] = kc.load_scheme_mod(path)

def stage(n, X, dele, tag, reduce):
    """Delete one index of the current scheme, then (reduce) run the pivot search.  -> n2, Y, record."""
    s = 'IJK'.index(dele[0]); i = int(dele[1:])
    keep = [[j for j in range(n[t]) if not (t == s and j == i)] for t in range(3)]
    n2 = tuple(n[t] - (t == s) for t in range(3))
    Y, alive = kf.project_mod(n, X, keep); a = int(len(alive)); rec = {'delete': dele, 'n': list(n2), 'm_in': int(X[0].shape[0]), 'alive': a, 'steps': []}
    if reduce and a:
        rk = [int(r) for r in kf.kron_ranks(Y)]; rec['ranks'] = rk
        if a > min(rk):
            rng = np.random.default_rng(zlib.crc32((os.path.basename(G['path']) + '|' + tag).encode()))
            Y, pth = kk.trial(n2, [y.copy() for y in Y], rng, walk=G['walk'], restarts=G['restarts'])
            rec['steps'] = [{k: st[k] for k in ('m', 'direction', 'nullity', 'pivots', 'also_zero', 'm_out')} for st in pth]
    rec['m_out'] = int(Y[0].shape[0])
    return n2, Y, rec

def work(seq):
    t0 = time.time(); dels = seq.split(','); n, X = tuple(G['n']), G['X']; recs = []
    for q, dele in enumerate(dels):
        tag = ','.join(dels[:q + 1]); last = q == len(dels) - 1
        if not last and tag in G['cache']: n, X, rec = G['cache'][tag]
        else:
            n, X, rec = stage(n, X, dele, tag, G['mode'] == 'each' or last)
            if not last and len(G['cache']) < 4: G['cache'][tag] = (n, X, rec)
        recs.append(rec)
        if rec['m_out'] == 0: break
    bad = int(kc.brent_mod(n, X)) if X[0].shape[0] else -1
    return seq, list(n), recs, bad, time.time() - t0

def sequences(spec, n):
    if spec.startswith('next:'):
        pre = [d for d in spec[5:].split(',') if d]; cur = list(n)
        for d in pre: cur['IJK'.index(d[0])] -= 1
        return [','.join(pre + [f'{"IJK"[s]}{i}']) for s in range(3) for i in range(cur[s])]
    if spec == 'pairs':
        all1 = [(s, i) for s in range(3) for i in range(n[s])]; out = []
        for a in range(len(all1)):
            for b in range(a + 1, len(all1)):
                (s1, i1), (s2, i2) = all1[b], all1[a]      # the larger index first, so that both are indices of the original scheme
                out.append(f'{"IJK"[s1]}{i1},{"IJK"[s2]}{i2}')
        return out
    return [s for s in spec.split(';') if s]

if __name__ == '__main__':
    args = sys.argv[1:]; opt = {'--workers': 2, '--walk': 100, '--restarts': 1, '--mode': 'each', '--paths': '', '--bar': ''}
    for key in list(opt):
        if key in args:
            i = args.index(key); v = args[i + 1]; del args[i:i + 2]; opt[key] = v if key in ('--mode', '--paths', '--bar') else int(v)
    path, status_path, out, spec = args
    status = json.load(open(status_path)); best = {k: dict(v['ranks']) for k, v in status.items() if isinstance(v, dict) and 'ranks' in v}
    for item in filter(None, opt['--bar'].split(',')):
        k, v = item.split('='); best[k]['Q'] = min(best[k].get('Q', 10 ** 9), int(v))
    mm = re.match(r'^(\d+)x(\d+)x(\d+)_m(\d+)', os.path.basename(path)); n0 = [int(mm.group(i)) for i in (1, 2, 3)]
    seqs = sequences(spec, n0); name = os.path.basename(path)
    print(f'{name}: {len(seqs)} deletion sequences ({spec[:60]}), mode {opt["--mode"]}, walk {opt["--walk"]}, restarts {opt["--restarts"]}, {opt["--workers"]} workers', flush=True)
    if opt['--paths']: os.makedirs(opt['--paths'], exist_ok=True)
    t0 = time.time(); nbelow = 0; seen = {}
    with Pool(opt['--workers'], initializer=init, initargs=(path, opt['--walk'], opt['--restarts'], opt['--mode'])) as pool, open(out, 'w', newline='') as fh:
        wr = csv.writer(fh); wr.writerow(['source', 'sequence', 'shape', 'm_out', 'brent_wrong', 'stages', 'best_Q', 'best_Z', 'best_ZT'])
        for seq, n, recs, bad, dt in pool.imap_unordered(work, seqs, chunksize=1):
            key = 'x'.join(map(str, sorted(n))); b = best.get(key, {}); mout = recs[-1]['m_out']
            desc = ' | '.join(f"{r['delete']}: {r['alive']} alive" + ''.join(f", d{st['direction']}:{st['nullity']}dep:{st['m'] - st['m_out']}gone" for st in r['steps']) + f" -> {r['m_out']}" for r in recs)
            wr.writerow([name, seq, key, mout, bad, desc, b.get('Q'), b.get('Z'), b.get('ZT')]); fh.flush()
            flag = ''
            if bad != 0: flag = f'   BRENT FAILS modulo p ({bad} wrong entries) -- ignore and investigate'
            elif b.get('Q') is not None and mout < b['Q']: flag = f'   <<< BELOW Q {b["Q"]}'; nbelow += 1
            elif b.get('Q') is not None and mout == b['Q']: flag = f'   (ties Q {b["Q"]})'
            elif not b: flag = '   (shape not in the catalog)'
            seen.setdefault(key, []).append(mout)
            print(f'{seq}: {key} {desc}; catalog Q {b.get("Q")} Z {b.get("Z")} ZT {b.get("ZT")}{flag} ({dt:.0f} s)', flush=True)
            if opt['--paths'] and bad == 0 and b.get('Q') is not None and mout < b['Q']:
                json.dump({'source': path, 'sequence': seq, 'n': n, 'm_out': mout, 'prime': kc.P0, 'mode': opt['--mode'], 'stages': recs},
                          open(os.path.join(opt['--paths'], f'{key}_m{mout}_{seq.replace(",", "_")}.path.json'), 'w'))
    for key in sorted(seen): print(f'  {key}: best {min(seen[key])}, worst {max(seen[key])} over {len(seen[key])} sequences; catalog {best.get(key)}', flush=True)
    print(f'done: {len(seqs)} sequences, {nbelow} below the catalog\'s Q rank, {time.time() - t0:.0f} s', flush=True)
