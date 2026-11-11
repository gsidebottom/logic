#!/usr/bin/env python3
"""Global rank-one census of a scheme (quotient method, independent of kres.rs).
(Prior art: the move is the block flip of LITA -- K. Khoruzhii, L. Serafin, P. Gelss, S. Pokutta, "Local
Improvements to Trilinear Aggregation", github.com/khoruzhii/lita: a rank-one element u' (x) v' of the span of the
pair factors X_t = u_t (x) v_t replaces one of them.  "All-sum" is the case where it is the sum of all X_t.)

Direction d: G_d = span of the Kronecker products of the other two slots' factors over all
products.  Lists every rank-one x (x) y in G_d with the index set J of the products summing
to it.  x (x) y in G_d  <=>  sum_j y_j q_j(x) = 0 with q_j(x) = (x (x) e_j) mod G_d, linear in x.
usage: kron_census.py N scheme.bits [--selftest]
"""
import sys

def load(path, w):
    bits = open(path).read().split()[-1]
    per = 3 * w
    assert len(bits) % per == 0
    r = len(bits) // per
    out = []
    for m in range(r):
        p = []
        for s in range(3):
            v = 0
            for k in range(w):
                if bits[s * r * w + m * w + k] == '1':
                    v |= 1 << k
            p.append(v)
        out.append(p)
    return out

def kron(x, y, w):
    m = 0
    for i in range(w):
        if (x >> i) & 1:
            m |= y << (i * w)
    return m

def census(prods, d, w):
    r, c = [(1, 2), (0, 2), (0, 1)][d]
    kr = [kron(p[r], p[c], w) for p in prods]
    # echelon basis with coordinates over the products: lead bit -> (vector, mask)
    ech = {}
    deps = []
    for t, v in enumerate(kr):
        x, m = v, 1 << t
        while x:
            l = x.bit_length() - 1
            if l in ech:
                x ^= ech[l][0]; m ^= ech[l][1]
            else:
                ech[l] = (x, m); break
        if x == 0:
            deps.append(m)
    def red(v):
        m = 0
        while v:
            l = v.bit_length() - 1
            if l not in ech:
                # strip the leading bit into the remainder
                return None
            v ^= ech[l][0]; m ^= ech[l][1]
        return m
    def redq(v):
        # remainder modulo G (canonical: no bit at a pivot position)
        out = 0
        while v:
            l = v.bit_length() - 1
            if l in ech:
                v ^= ech[l][0]
            else:
                out |= 1 << l; v ^= 1 << l
        return out
    R = [[redq(1 << (i * w + j)) for j in range(w)] for i in range(w)]
    q = [0] * w
    found = []
    prev = 0
    for g in range(1, 1 << w):
        x = g ^ (g >> 1)
        b = (x ^ prev).bit_length() - 1
        prev = x
        Rb = R[b]
        for j in range(w):
            q[j] ^= Rb[j]
        # kernel of y -> sum_j y_j q_j
        piv = {}
        kern = []
        for j in range(w):
            v, m = q[j], 1 << j
            while v:
                l = v.bit_length() - 1
                if l in piv:
                    v ^= piv[l][0]; m ^= piv[l][1]
                else:
                    piv[l] = (v, m); break
            if v == 0:
                kern.append(m)
        if kern:
            for cmb in range(1, 1 << len(kern)):
                y = 0
                for i, kv in enumerate(kern):
                    if (cmb >> i) & 1:
                        y ^= kv
                J = red(kron(x, y, w))
                assert J is not None
                found.append((x, y, J))
    return len(ech), deps, kr, found

def report(prods, w, label):
    clean_all = True
    for d in range(3):
        dim, deps, kr, found = census(prods, d, w)
        orig = sum(1 for (x, y, J) in found if bin(J).count('1') == 1)
        extra = [(x, y, J) for (x, y, J) in found if bin(J).count('1') != 1]
        clean = (dim == len(prods) and not extra and orig == len(prods))
        clean_all &= clean
        print(f"{label} d={d}: products {len(prods)}, dim G {dim}, dependencies {len(deps)}, rank-one elements {len(found)} "
              f"(originals {orig}, extra {len(extra)}) -> {'CLEAN' if clean else 'NOT CLEAN'}")
        for m in deps:
            print(f"   DEPENDENCY J={[t for t in range(len(prods)) if (m >> t) & 1]}")
        for (x, y, J) in sorted(extra, key=lambda e: bin(e[2]).count('1'))[:40]:
            print(f"   EXTRA |J|={bin(J).count('1')} x={x:0{w}b} y={y:0{w}b} J={[t for t in range(len(prods)) if (J >> t) & 1]}")
        if len(extra) > 40:
            sizes = {}
            for (_, _, J) in extra:
                sizes[bin(J).count('1')] = sizes.get(bin(J).count('1'), 0) + 1
            print(f"   ... {len(extra)} extras, sizes {sorted(sizes.items())}")
    return clean_all

if __name__ == '__main__':
    n = int(sys.argv[1]); w = n * n
    if '--selftest' in sys.argv:
        # six of the seven nonzero vectors u of a 3-dim space with (b, c) = (u, u): their Kronecker products sum to
        # u0 (x) u0 for the seventh, with no shared factor; all seven are dependent
        us = [0b0001, 0b0010, 0b0100, 0b0011, 0b0101, 0b0110, 0b0111]
        us = [u << 5 for u in us]
        six = [[(1 << t) | (1 << (t + 7)), us[t], us[t]] for t in range(6)]
        seven = [[(1 << t) | (1 << (t + 7)), us[t], us[t]] for t in range(7)]
        report(six, w, 'selftest-six')
        report(seven, w, 'selftest-seven')
        sys.exit(0)
    prods = load(sys.argv[2], w)
    ok = report(prods, w, sys.argv[2].split('/')[-1])
    print(f"{sys.argv[2].split('/')[-1]}: {'CLEAN in all three directions' if ok else 'NOT CLEAN'}")
