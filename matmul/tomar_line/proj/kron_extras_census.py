#!/usr/bin/env python3
"""Rank-one census of F2 scheme stores: the translation moves a scheme admits.
(Prior art: the move is the block flip of LITA -- K. Khoruzhii, L. Serafin, P. Gelss, S. Pokutta, "Local
Improvements to Trilinear Aggregation", github.com/khoruzhii/lita: a rank-one element u' (x) v' of the span of the
pair factors X_t = u_t (x) v_t replaces one of them.  "All-sum" is the case where it is the sum of all X_t.)

In direction d (slots r, c the two others) a rank-one element x (x) y = sum_{t in J} f_t (x) g_t of the span
of the Kronecker products lets one add any vector gamma to the slot-d factors of J and append the product
(x, gamma, y); the count becomes r + 1 - #{t in J : slot-d factor = gamma}.  |J| = 2 is the flip of
Kauers-Moosbauer (two products sharing a factor); an element whose products do not all share a factor is a
move the flip graph does not have.  If two products of J share their slot-d factor the scheme REDUCES.
usage: kron_extras_census.py N,M,P KRES [--workers W] [--rank R] [--out FILE] DIR_OR_FILE ...
KRES is the kres binary (its --census mode lists the rank-one elements).  Per store: the histogram of the
non-flip elements by (direction, |J|), and every REDUCING element.
"""
import sys, os, re, subprocess, collections
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from kron_bits_scan import load, RC

EXTRA = re.compile(r'^\s+EXTRA \|J\|=(\d+) x=\S+ y=\S+ J=\[([0-9, ]*)\]')
HEAD = re.compile(r' d=(\d): products (\d+), dim G (\d+), dependencies (\d+), rank-one elements (\d+) \(originals (\d+), extra (\d+)\)')

def work(arg):
    path, shape, W, kres, want = arg
    try:
        F = load(path, W)
        if F is None: return (path, None, 'length')
        r = len(F[0])
        if want and r != want: return (path, None, 'rank')
        out = subprocess.run([kres, *map(str, shape), path, '--census'], capture_output=True, text=True, timeout=600).stdout
        res = []; d = None; heads = 0
        for line in out.splitlines():
            h = HEAD.search(line)
            if h:
                d = int(h.group(1)); heads += 1
                continue
            e = EXTRA.match(line)
            if e:
                J = [int(x) for x in e.group(2).split(',')]
                a, b = RC[d]
                flip = len(set(F[a][t] for t in J)) == 1 or len(set(F[b][t] for t in J)) == 1
                c = max(collections.Counter(F[d][t] for t in J).values())
                res.append((d, len(J), flip, c, J))
        if heads != 3: return (path, None, 'census output: ' + out[:200])
        return (path, r, res)
    except Exception as e:
        return (path, None, repr(e))

def init(): os.nice(15)

if __name__ == '__main__':
    args = sys.argv[1:]
    shape = tuple(map(int, args[0].split(','))); n, m, p = shape
    W = (n * m, m * p, p * n); kres = args[1]
    workers = 2; out = None; want = None; paths = []; i = 2
    while i < len(args):
        if args[i] == '--workers': workers = int(args[i + 1]); i += 2
        elif args[i] == '--out': out = args[i + 1]; i += 2
        elif args[i] == '--rank': want = int(args[i + 1]); i += 2
        else: paths.append(args[i]); i += 1
    files = []
    for q in paths:
        if os.path.isdir(q):
            for root, _, fs in os.walk(q):
                files += [os.path.join(root, f) for f in fs if f.endswith('.bits')]
        else: files.append(q)
    files.sort()
    hist = collections.Counter(); nonflip = collections.Counter(); per = collections.Counter()
    done = skipped = nred = 0
    of = open(out, 'w') if out else None
    with Pool(workers, initializer=init) as pool:
        for path, r, res in pool.imap_unordered(work, [(f, shape, W, kres, want) for f in files], chunksize=32):
            if r is None:
                skipped += 1
                if res not in ('length', 'rank'): print('ERROR', path, res, flush=True)
                continue
            done += 1
            nf = 0
            for d, j, flip, c, J in res:
                hist[(r, 'flip' if flip else 'non-flip', j)] += 1
                if not flip:
                    nf += 1; nonflip[(r, d, j, c)] += 1
                    if of: of.write(f'{path} d={d} |J|={j} c={c} J={J}\n')
                if c >= 2 and not (flip and j == 2 and False):
                    nred += 1
                    line = f'REDUCING {path}: r = {r}, direction {d}, |J| = {j}, {c} products of J share the slot factor -> {r + 1 - c} products ({"flip-type" if flip else "NON-FLIP"}) J={J}'
                    if nred <= 60 or not flip: print(line, flush=True)
            per[(r, nf)] += 1
            if done % 5000 == 0: print(f'  .. {done} schemes', flush=True)
    print(f'shape {n}x{m}x{p}: {done} schemes, {skipped} skipped; {nred} reducing elements')
    print('  rank-one elements beyond the products, by (rank, type, |J|):')
    for k, c in sorted(hist.items()): print(f'    {k}: {c}')
    print('  non-flip elements by (rank, direction, |J|, products sharing the slot factor):')
    for k, c in sorted(nonflip.items()): print(f'    {k}: {c}')
    print('  schemes by (rank, number of non-flip elements):')
    for k, c in sorted(per.items()): print(f'    {k}: {c}')
