#!/usr/bin/env python3
"""Kronecker-span rank scan of F2 scheme stores in the flip engine's .bits format.
(Prior art: this is the 2-reducibility test of LITA -- K. Khoruzhii, L. Serafin, P. Gelss, S. Pokutta, "Local
Improvements to Trilinear Aggregation", github.com/khoruzhii/lita, src/reduce.h -- a strict generalization of the
Kauers-Moosbauer reduction; nothing here is a new test.)

A scheme with r products needs at most dim span{f_t (x) g_t} products for any two of its three slots
(keep a basis of the span, fold the other products into the third slot).  The flip engine's reduction is
the special case in which the dependent products share a factor; this test sees every dependency.
usage: kron_bits_scan.py N,M,P [--workers W] [--out FILE] DIR_OR_FILE ...
Per file: the rank r, the three Kronecker ranks, and for every deficit whether the flip graph would see it
(some dependent set shares a factor in one of the two slots).  Files whose length does not fit the shape
are counted as skipped.
"""
import sys, os, collections
from multiprocessing import Pool

RC = [(1, 2), (0, 2), (0, 1)]

def rank2(rows):
    piv = {}
    for v in rows:
        while v:
            l = v.bit_length() - 1
            if l in piv: v ^= piv[l]
            else: piv[l] = v; break
    return len(piv)

def load(path, W):
    bits = open(path).read().split()[-1]
    tot = sum(W)
    if len(bits) % tot or set(bits) - {'0', '1'}: return None
    r = len(bits) // tot
    F = []; off = 0
    for w in W:
        F.append([int(bits[off + m * w: off + (m + 1) * w][::-1], 2) for m in range(r)])
        off += r * w
    return F

def kron(a, b, wb):
    k = 0; i = 0
    while a:
        if a & 1: k |= b << (i * wb)
        a >>= 1; i += 1
    return k

def visible(F, r, c):
    for s, o in ((r, c), (c, r)):
        groups = collections.defaultdict(list)
        for t in range(len(F[0])): groups[F[s][t]].append(F[o][t])
        for g in groups.values():
            if len(g) >= 2 and rank2(g) < len(g): return (s, len(g))
    return None

def scan(arg):
    path, W = arg
    try:
        F = load(path, W)
        if F is None: return (path, None, None, None)
        r = len(F[0])
        if any(0 in f for f in F): return (path, r, 'zero factor', None)
        rk = [rank2([kron(F[a][t], F[b][t], W[b]) for t in range(r)]) for a, b in RC]
        vis = None
        if min(rk) < r:
            vis = [(d, visible(F, *RC[d])) for d in range(3) if rk[d] < r]
        return (path, r, rk, vis)
    except Exception as e:
        return (path, None, repr(e), None)

def init(): os.nice(15)

if __name__ == '__main__':
    args = sys.argv[1:]
    n, m, p = map(int, args[0].split(','))
    W = (n * m, m * p, p * n)
    workers = 2; out = None; paths = []; i = 1
    while i < len(args):
        if args[i] == '--workers': workers = int(args[i + 1]); i += 2
        elif args[i] == '--out': out = args[i + 1]; i += 2
        else: paths.append(args[i]); i += 1
    files = []
    for q in paths:
        if os.path.isdir(q):
            for root, _, fs in os.walk(q):
                files += [os.path.join(root, f) for f in fs if f.endswith('.bits')]
        else: files.append(q)
    files.sort()
    hist = collections.Counter(); skipped = 0; nflag = 0; ninv = 0
    of = open(out, 'w') if out else None
    with Pool(workers, initializer=init) as pool:
        for path, r, rk, vis in pool.imap_unordered(scan, [(f, W) for f in files], chunksize=256):
            if r is None:
                skipped += 1
                if rk: print('ERROR', path, rk, flush=True)
                continue
            if rk == 'zero factor':
                hist[(r, 'zero factor')] += 1; continue
            hist[(r, tuple(rk))] += 1
            if min(rk) < r:
                nflag += 1
                inv = [d for d, v in vis if v is None]
                if inv: ninv += 1
                line = f'DEFICIT {path}: r = {r}, Kronecker ranks {rk} -> at most {min(rk)} products; ' + '; '.join(
                    f'd={d} ' + ('NOT flip-visible' if v is None else f'flip-visible (slot {v[0]} shared by {v[1]})') for d, v in vis)
                if of: of.write(line + '\n'); of.flush()
                if nflag <= 40 or inv: print(line, flush=True)
    print(f'shape {n}x{m}x{p}: {len(files)} files, {skipped} skipped (length does not fit), {nflag} with a deficit, {ninv} with a deficit the flip graph does not see')
    for (r, rk), c in sorted(hist.items(), key=lambda kv: (kv[0][0], str(kv[0][1]))):
        print(f'  r = {r}, Kronecker ranks {rk}: {c}')
