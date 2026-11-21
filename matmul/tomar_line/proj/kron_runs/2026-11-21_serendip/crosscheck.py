#!/usr/bin/env python3
"""crosscheck.py [PROCS]: scheme_modp_sparse.py (random matrices modulo four primes, other code than kronexact)
on every built/*.json.gz that has no crosscheck/NAME.txt yet.  Deletes nothing."""
import os, subprocess, sys
from multiprocessing import Pool
here = os.path.dirname(os.path.abspath(__file__))
tool = os.path.join(here, '..', '..', 'scheme_modp_sparse.py')


def one(fn):
    out = os.path.join(here, 'crosscheck', fn[:-len('.json.gz')] + '.txt')
    r = subprocess.run([sys.executable, '-I', tool, os.path.join(here, 'built', fn)], capture_output=True, text=True, timeout=7200)
    open(out, 'w').write(r.stdout + r.stderr)
    return fn, 'PASS' in r.stdout


if __name__ == '__main__':
    os.makedirs(os.path.join(here, 'crosscheck'), exist_ok=True)
    todo = [f for f in sorted(os.listdir(os.path.join(here, 'built'))) if f.endswith('.json.gz')
            and not os.path.exists(os.path.join(here, 'crosscheck', f[:-len('.json.gz')] + '.txt'))]
    bad = []
    with Pool(int(sys.argv[1]) if len(sys.argv) > 1 else 3) as pool:
        for fn, ok in pool.imap_unordered(one, todo):
            if not ok: bad.append(fn)
    print('%d checked, %d not PASS %s' % (len(todo), len(bad), bad[:10]))
