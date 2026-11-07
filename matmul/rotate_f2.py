#!/usr/bin/env python3
"""Cyclic format rotation of an F2 scheme: <n1,n2,n3> -> <n2,n3,n1>.

trace(A B C^T) = trace(B C^T A), so the rotated scheme has a' = b, b' = c^T,
c' = a^T (bits layout as in project_f2.py: a is n1 x n2, b is n2 x n3, c is
n1 x n3, all row-major).  The result is checked against the rotated format's
tensor.  usage: rotate_f2.py N1 N2 N3 in.bits out.bits [--twice]"""
import sys, os
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from project_f2 import load_bits, check, to_bits

def rotate(alpha, beta, gamma):
    # alpha (r,n1,n2), beta (r,n2,n3), gamma (r,n1,n3) -> a' (r,n2,n3), b' (r,n3,n1), c' (r,n2,n1)
    return beta.copy(), np.transpose(gamma, (0, 2, 1)).copy(), np.transpose(alpha, (0, 2, 1)).copy()

if __name__ == '__main__':
    n1, n2, n3 = map(int, sys.argv[1:4]); src, dst = sys.argv[4], sys.argv[5]
    twice = '--twice' in sys.argv
    al, be, ga = load_bits(src, n1, n2, n3)
    assert check(al, be, ga, n1, n2, n3), 'input fails the tensor check'
    al, be, ga = rotate(al, be, ga); n1, n2, n3 = n2, n3, n1
    if twice:
        al, be, ga = rotate(al, be, ga); n1, n2, n3 = n2, n3, n1
    assert check(al, be, ga, n1, n2, n3), 'rotated scheme fails the tensor check'
    open(dst, 'w').write(to_bits(al, be, ga) + '\n')
    print(f'{dst}: <{n1},{n2},{n3}> rank {al.shape[0]}, tensor check OK')
