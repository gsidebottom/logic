#!/usr/bin/env python3
"""Strict-target C-cover orbit sweep for the counting-open thin-new
classes (reuses sweep48.job — identical machinery, thin inputs)."""
import glob, os, re, sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, f'{ROOT}/matmul')
sys.path.insert(0, HERE)
from cfloor import slot_masks
from sweep48 import job
import multiprocessing as mp

if __name__ == '__main__':
    floors = {}
    for ln in open(f'{HERE}/floors_thin.log'):
        m = re.match(r'^(d\d+-\d+) FLOOR (\d+)', ln)
        if m:
            floors[m.group(1)] = int(m.group(2))
    items = []
    for p in sorted(glob.glob(f'{HERE}/bits_d*/d*.bits')):
        name = p.split('/')[-1].replace('.bits', '')
        bits = [int(c) for c in open(p).read().strip()]
        mind = min(len({w for w in fam if w}) for fam in slot_masks(bits))
        if floors[name] + mind + 5 <= 55:
            items.append((name, floors[name], bits))
    print(f'sweeping {len(items)} counting-open thin classes', flush=True)
    with mp.Pool(7) as pool:
        for r in pool.imap_unordered(job, items):
            print(r, flush=True)
    print('sweep done', flush=True)
