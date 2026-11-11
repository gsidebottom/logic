#!/usr/bin/env python3
"""Count the scalings of PLinOpt straight-line programs by kind: divisions by a constant (a '/' operator, or a
'*' by a non-integer a/b) versus multiplications by an integer constant, and how many divisors are powers of two.
PLinOpt's OpCount.sh counts both kinds together as "scalings (mul/div)".
usage: slp_div_count.py PROGRAM.slp ...
"""
import sys, re
from fractions import Fraction

TOK = re.compile(r'([*/])\s*(\d+)(?:\s*/\s*(\d+))?')

def pow2(n):
    return n > 0 and n & (n - 1) == 0

for path in sys.argv[1:]:
    div = div2 = mul = 0
    dens = set()
    for ln in open(path):
        ln = ln.split('#')[0]
        if ':=' not in ln:
            continue
        rhs = ln.split(':=', 1)[1]
        for op, a, b in TOK.findall(rhs):
            c = Fraction(int(a), int(b)) if b else Fraction(int(a))
            if op == '/':
                c = 1 / c
            if c.denominator != 1:
                div += 1; dens.add(c.denominator)
                if pow2(c.denominator): div2 += 1
            elif abs(c) != 1:
                mul += 1
    print(f'{path.split("/")[-1]}: {div} divisions by a constant ({div2} by a power of two), '
          f'{mul} multiplications by an integer constant; {len(dens)} distinct divisors')
