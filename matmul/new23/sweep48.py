#!/usr/bin/env python3
"""Targeted C-cover orbit sweep for the 48 storm-new classes.

Uses cfloor's own slot_masks/TENSOR/IDDFS machinery throughout (the
authoritative mask conventions).  Per class with side-floor f:
a 54-add scheme needs some slot's orbit-min XOR cover <= 54 - f - 14,
a 55 needs <= 55 - f - 14.  Counting bound: cover >= d - 9.
"""
import sys, re, os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from cfloor import slot_masks, s3_coset_reps, TENSOR, POPC
from gf2min import gf2_min_cover
import multiprocessing as mp

HERE = os.path.dirname(os.path.abspath(__file__))

def load():
    floors = {}
    for ln in open(f'{HERE}/floors_new48.log'):
        m = re.match(r'^(new23-\d+) FLOOR (\d+)', ln)
        if m:
            floors[m.group(1)] = int(m.group(2))
    items = []
    for ln in open(f'{HERE}/all_new48.txt'):
        name, bits = ln.split()
        # slot_masks expects a bit LIST — a raw '0'/'1' string is all-truthy
        items.append((name, floors[name], [int(c) for c in bits]))
    return items

def job(item):
    name, fl, bits = item
    t54, t55 = 54 - fl - 14, 55 - fl - 14
    reps = s3_coset_reps()
    best = None
    for si, fam in enumerate(slot_masks(bits)):
        nz = [w for w in fam if w]
        if len(set(nz)) - 9 > t55:
            continue
        bl_ = [[i for i in range(9) if (w >> i) & 1] for w in nz]
        for X in reps:
            for Y in reps:
                b = [TENSOR[X[p]][Y[q]] for p in range(3) for q in range(3)]
                img = []
                for bl in bl_:
                    v = 0
                    for i in bl:
                        v ^= b[i]
                    img.append(v)
                nt = len({w for w in img if POPC[w] >= 2})
                if nt > t55:
                    continue
                res = gf2_min_cover(img, 9, max_slack=t55 - nt,
                                    node_cap=5_000_000)
                if res["status"] != "exact" or res["adds"] > t55:
                    continue
                c = res["adds"]
                if best is None or c < best:
                    best = c
                if c <= t54:
                    return (name, fl, "ALARM-54-CAPABLE", si, c)
    if best is not None:
        return (name, fl, "55-capable-C", None, best)
    return (name, fl, "closed->=56", None, None)

if __name__ == "__main__":
    items = load()
    # gate: d-vector of new23-40 must match the census printout
    for name, fl, bits in items:
        if name == 'new23-40':
            ds = [len({w for w in fam if w}) for fam in slot_masks(bits)]
            assert ds == [23, 20, 23], f"slot_masks gate failed: {ds}"
            print(f"gate: new23-40 d={ds} matches census", flush=True)
    # authoritative lower-bound table via slot_masks
    open_items = []
    from collections import Counter
    hist = Counter()
    for name, fl, bits in items:
        mind = min(len({w for w in fam if w}) for fam in slot_masks(bits))
        lb = fl + mind + 5
        hist[lb] += 1
        if lb <= 55:
            open_items.append((name, fl, bits))
    print("lb histogram (floor + min-d + 5):", dict(sorted(hist.items())),
          flush=True)
    print(f"sweeping {len(open_items)} open classes", flush=True)
    with mp.Pool(7) as pool:
        for r in pool.imap_unordered(job, open_items):
            print(r, flush=True)
    print("sweep done", flush=True)
