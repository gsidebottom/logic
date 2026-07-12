#!/usr/bin/env python3
"""Novelty screen for the thin-storm pools (d40 / d38): the 54-adds
experiment readout, stage 1.

Per arm: strict-integer schemes -> mod-2 dedupe -> rank-pattern
absence test vs the 302 DB patterns -> cross-dedupe vs our 53 lifted
classes AND the 48 already-harvested storm classes -> certified-new
bits emitted for the floors stage.  Single-process (no mp)."""
import glob, os, re, sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, f'{ROOT}/matmul')
from equiv import mat_rank
from novelty import letters_of, compatible
from census23 import load_lifted

def pv(s):
    l, r = s.rsplit('], ', 1)
    return [int(x) for x in l.strip()[2:].split(',')], int(r.rstrip(') \n'))

def screen_pool(path, known_keys, patterns):
    blocks = [b for b in open(path).read().split('---\n') if b.strip()]
    stats = Counter()
    new = {}
    for b in blocks:
        S = [[pv(p) for p in ln.split(' | ')] for ln in b.strip().split('\n')]
        if len(S) != 23:
            continue
        stats['blocks'] += 1
        exps = [f[1] for t in S for f in t]
        if any(e != 0 for e in exps):
            stats['dyadic_or_even'] += 1
            continue
        m2 = [tuple(sum(((abs(v) & 1) << k) for k, v in enumerate(f[0]))
                    for f in t) for t in S]
        if len(set(m2)) != 23:
            stats['mod2_collision'] += 1
            continue
        key = tuple(sorted(m2))
        if key in known_keys or key in new:
            stats['dup'] += 1
            continue
        types = Counter(tuple(sorted((mat_rank(a), mat_rank(b), mat_rank(c))))
                        for (a, b, c) in m2)
        if any(compatible(ls, types) for _, ls in patterns):
            stats['db_compatible'] += 1
            new[key] = None  # count distinct but not novel
            continue
        stats['CERTIFIED_NEW'] += 1
        new[key] = b
    return stats, {k: v for k, v in new.items() if v is not None}

if __name__ == '__main__':
    patterns = [(p, letters_of(p)) for p in
                open(f'{ROOT}/matmul/db_rank_patterns.txt').read().split()]
    known = set()
    # our 53
    for p in glob.glob(f'{ROOT}/matmul/lifted/walk-*.txt'):
        S = load_lifted(p)
        known.add(tuple(sorted(
            tuple(sum(((abs(v) & 1) << k) for k, v in enumerate(f)) for f in t)
            for t in S)))
    # the 48 from the first (unconstrained) harvest
    cur = []
    for ln in open(f'{ROOT}/matmul/found23q/certified_new_mod2.txt'):
        if ln.startswith('#'):
            continue
        if ln.strip() == '---':
            known.add(tuple(sorted(tuple(t) for t in cur)))
            cur = []
        else:
            cur.append(tuple(int(x) for x in ln.split()))
    print(f'known keys (ours + harvest-48): {len(known)}', flush=True)

    for arm in ['d40', 'd38']:
        path = f'{ROOT}/matmul/found23q/{arm}/pool23.txt'
        stats, new = screen_pool(path, known, patterns)
        print(f'\n[{arm}] {dict(stats)}', flush=True)
        outdir = f'{HERE}/bits_{arm}'
        os.makedirs(outdir, exist_ok=True)
        with open(f'{HERE}/thinnew_{arm}.txt', 'w') as pool_out:
            for i, (key, b) in enumerate(new.items()):
                S = [[pv(p) for p in ln.split(' | ')]
                     for ln in b.strip().split('\n')]
                bits = ''.join(str(abs(x) & 1)
                               for sl in range(3) for t in S for x in t[sl][0])
                open(f'{outdir}/{arm}-{i:03}.bits', 'w').write(bits + '\n')
                pool_out.write(b + '---\n')
        print(f'[{arm}] emitted {len(new)} certified-new bits to {outdir}',
              flush=True)
