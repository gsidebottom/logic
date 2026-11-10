#!/usr/bin/env python3
"""K random flips on an F2 matrix-multiplication scheme of format <n1,n2,n3>.  A flip (Kauers-Moosbauer) takes two
products sharing a factor in one slot and moves the difference across the other two:
  a (x) b_i (x) c_i + a (x) b_j (x) c_j = a (x) (b_i + b_j) (x) c_i + a (x) b_j (x) (c_i + c_j),
either orientation, any slot.  A product whose new factor vanishes is dropped (a reduction; reported).  The result is
checked against the tensor and written in the repository's .bits layout.  Mutation operator at a controlled flip
distance for the parent-space experiments (which <4,4,5> schemes project to 47-adjacent 4x4 pools?); the walk mode of
the flip engine only returns excursion landings, which are far from the start.
usage: flipk_f2.py N1 N2 N3 in.bits K out.bits [--seed S] [--quiet]"""
import sys, os, random
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
from project_f2 import load_bits, check, to_bits


def flip_pairs(F):
    """(slot, i, j) for every pair of products with equal factors in that slot."""
    out = []
    for s in range(3):
        groups = {}
        for i, row in enumerate(F[s]):
            groups.setdefault(row.tobytes(), []).append(i)
        for g in groups.values():
            for x in range(len(g)):
                for y in range(x + 1, len(g)):
                    out.append((s, g[x], g[y]))
    return out


def main():
    n1, n2, n3 = map(int, sys.argv[1:4]); src = sys.argv[4]; K = int(sys.argv[5]); dst = sys.argv[6]
    seed = int(sys.argv[sys.argv.index('--seed') + 1]) if '--seed' in sys.argv else 1
    quiet = '--quiet' in sys.argv
    rng = random.Random(seed)
    al, be, ga = load_bits(src, n1, n2, n3)
    r0 = al.shape[0]
    assert check(al, be, ga, n1, n2, n3), 'input fails the tensor check'
    F = [al.reshape(r0, -1).copy(), be.reshape(r0, -1).copy(), ga.reshape(r0, -1).copy()]
    npairs0 = None; drops = 0; done = 0
    for step in range(K):
        pairs = flip_pairs(F)
        if npairs0 is None:
            npairs0 = len(pairs)
        if not pairs:
            print(f'flip-isolated after {step} flips', file=sys.stderr)
            break
        s, i, j = rng.choice(pairs)
        u, v = [t for t in range(3) if t != s]
        if rng.random() < 0.5:
            u, v = v, u
        F[u][i] = (F[u][i] + F[u][j]) % 2       # product i takes j's u-factor
        F[v][j] = (F[v][j] + F[v][i]) % 2       # product j takes i's (unchanged) v-factor
        done += 1
        keep = [t for t in range(F[0].shape[0]) if all(F[q][t].any() for q in range(3))]
        if len(keep) < F[0].shape[0]:
            drops += F[0].shape[0] - len(keep)
            F = [f[keep] for f in F]
    r = F[0].shape[0]
    al, be, ga = F[0].reshape(r, n1, n2), F[1].reshape(r, n2, n3), F[2].reshape(r, n1, n3)
    assert check(al, be, ga, n1, n2, n3), 'flipped scheme fails the tensor check'
    open(dst, 'w').write(to_bits(al, be, ga) + '\n')
    if not quiet:
        print(f'{done} flips from rank {r0}: {npairs0} flippable pairs at the start, {drops} products dropped, rank {r} -> {dst}')


if __name__ == '__main__':
    main()
