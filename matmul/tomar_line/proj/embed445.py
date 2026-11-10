#!/usr/bin/env python3
"""Embed a 4x4 scheme into <4,4,5>: the r products act on the first four columns of B and C, and the fifth column is
computed by the 16 trivial products a_ik (x) b_k5 (x) c_i5, giving a <4,4,5> scheme of rank r + 16 (AlphaTensor's
<4,4,5>:63 has this shape over a rank-47 scheme).  Checked against the <4,4,5> tensor and written in the .bits layout.
Parents of our own for the Tomar-line projection pools: one per rank-47 class, to be descended in <4,4,5> first.
usage: embed445.py in444.bits out445.bits"""
import sys, os
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
from project_f2 import load_bits, check, to_bits
src, dst = sys.argv[1], sys.argv[2]
al, be, ga = load_bits(src, 4, 4, 4)
r = al.shape[0]
assert check(al, be, ga, 4, 4, 4), 'input fails the 4x4 tensor check'
A = np.zeros((r + 16, 4, 4), dtype=np.uint8); B = np.zeros((r + 16, 4, 5), dtype=np.uint8); C = np.zeros((r + 16, 4, 5), dtype=np.uint8)
A[:r] = al; B[:r, :, :4] = be; C[:r, :, :4] = ga
t = r
for i in range(4):
    for k in range(4):
        A[t, i, k] = 1; B[t, k, 4] = 1; C[t, i, 4] = 1; t += 1
assert check(A, B, C, 4, 4, 5), 'embedding fails the <4,4,5> tensor check'
open(dst, 'w').write(to_bits(A, B, C) + '\n')
print(f'{src}: rank {r} -> <4,4,5> rank {r + 16} -> {dst}')
