#!/usr/bin/env python3
"""Apply kres verdict lines ("RED ..." / "ALT ..." with new=a/b/c,... bit strings) to a scheme: drop the idx= products,
add the new ones, cancel duplicates, check the tensor, write each distinct result as .bits and print its rank.
usage: kres_apply.py N1 N2 N3 scheme.bits verdicts.txt --out DIR [--tag T]
"""
import sys, os, re, argparse
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
from project_f2 import load_bits, check, to_bits


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('n1', type=int); ap.add_argument('n2', type=int); ap.add_argument('n3', type=int)
    ap.add_argument('bits'); ap.add_argument('lines'); ap.add_argument('--out', required=True); ap.add_argument('--tag', default='k')
    a = ap.parse_args()
    n1, n2, n3 = a.n1, a.n2, a.n3; wa, wb, wc = n1 * n2, n2 * n3, n1 * n3
    al, be, ga = load_bits(a.bits, n1, n2, n3); r = al.shape[0]
    assert check(al, be, ga, n1, n2, n3), 'input fails the tensor check'
    prods = [(tuple(al[t].reshape(-1)), tuple(be[t].reshape(-1)), tuple(ga[t].reshape(-1))) for t in range(r)]
    os.makedirs(a.out, exist_ok=True)
    found = {}; orig = tuple(sorted(prods)); n_lines = 0; best = r
    for line in open(a.lines):
        m = re.match(r'(RED|ALT) k=(\d+) dims=\S+ idx=([\d,]+) new=(\S+) verified=(\d)', line)
        if not m:
            continue
        n_lines += 1
        idx = set(int(x) for x in m.group(3).split(','))
        new = []
        for trip in m.group(4).split(','):
            sa, sb, sc = trip.split('/')
            assert len(sa) == wa and len(sb) == wb and len(sc) == wc, 'bit string lengths'
            new.append((tuple(int(ch) for ch in sa), tuple(int(ch) for ch in sb), tuple(int(ch) for ch in sc)))
        ps = [p for t, p in enumerate(prods) if t not in idx] + new
        cnt = {}
        for p in ps:
            cnt[p] = cnt.get(p, 0) + 1
        ps = [p for p, c in cnt.items() if c % 2 == 1 and any(p[0]) and any(p[1]) and any(p[2])]
        rk = len(ps)
        al2 = np.array([p[0] for p in ps], dtype=np.uint8).reshape(rk, n1, n2)
        be2 = np.array([p[1] for p in ps], dtype=np.uint8).reshape(rk, n2, n3)
        ga2 = np.array([p[2] for p in ps], dtype=np.uint8).reshape(rk, n1, n3)
        ok = check(al2, be2, ga2, n1, n2, n3)
        key = tuple(sorted(ps))
        if not ok:
            status = 'FAILS the tensor check'
        elif key == orig:
            status = 'the input scheme itself'
        elif key in found:
            status = f'duplicate of {found[key]}'
        else:
            name = f'{a.tag}_{m.group(1)}_r{rk}_{len(found):05d}.bits'
            open(os.path.join(a.out, name), 'w').write(to_bits(al2, be2, ga2) + '\n'); found[key] = name
            status = f'new: {name}'
        if ok:
            best = min(best, rk)
        print(f'{m.group(1)} k={m.group(2)} idx={m.group(3)} -> rank {rk}, {status}' + (f'   RANK {rk} < {r}' if ok and rk < r else ''))
    print(f'{n_lines} verdict lines, {len(found)} distinct schemes written to {a.out}, best rank {best} (input {r})')


if __name__ == '__main__':
    main()
