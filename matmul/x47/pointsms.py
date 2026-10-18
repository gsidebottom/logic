#!/usr/bin/env python3
"""Write the sms triplet of an orbit point (sigma, X, Y, Z as u16 hex,
the xor47 log convention) of a base scheme.
Usage: pointsms.py BASE_PREFIX SIGMA X Y Z OUT_PREFIX"""
import sys
sys.path.insert(0, __file__.rsplit("/", 1)[0] or ".")
from scheme47 import load_sms, brent_ok, write_sms

def mul(a, b):
    out = 0
    for i in range(4):
        r = 0
        for j in range(4):
            if (a >> (4 * i + j)) & 1:
                r ^= (b >> (4 * j)) & 0xF
        out |= r << (4 * i)
    return out

def tr(a):
    return sum(((a >> (4 * i + j)) & 1) << (4 * j + i) for i in range(4) for j in range(4))

def inv(a):
    for b in range(1 << 16):
        if mul(a, b) == 0x8421:
            return b
    raise ValueError("singular")

base, sg, xs, ys, zs, out = sys.argv[1:7]
U, V, W = load_sms(base)
T = lambda M: [tr(m) for m in M]
U, V, W = [(U, V, W), (V, T(W), T(U)), (T(W), U, T(V)), (T(V), T(U), T(W)), (W, T(V), U), (T(U), W, V)][int(sg)]
X, Y, Z = (int(s, 16) for s in (xs, ys, zs))
Xi, Yi, Zi = inv(X), inv(Y), inv(Z)
U2 = [mul(mul(tr(X), u), tr(Yi)) for u in U]
V2 = [mul(mul(tr(Y), v), tr(Zi)) for v in V]
W2 = [mul(mul(Xi, w), Z) for w in W]
assert brent_ok(U2, V2, W2), "point fails Brent"
write_sms(U2, V2, W2, out)
print(f"wrote {out}_{{L,R,P}}.sms")
