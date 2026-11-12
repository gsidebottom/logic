"""Stored from the session scratch directory (kres/deep/d4/plant.py), 2026-11-12.  Planted controls for kres alt at delta 3 and 4: k random products of <4,4,4> shape (16-bit factors) whose factors
span exactly 7 dimensions in each slot, two of them sharing their c-factor, so the decomposition has a known
alternative (the flip a(x)b(x)c + a'(x)b'(x)c = a(x)(b+b')(x)c + (a+a')(x)b'(x)c).  Writes the scheme as .bits
(kres layout: all a factors, then all b, then all c, 16 bits each, bit k = coordinate k) and the flipped products
for checking.  usage: plant.py K SEED OUT_PREFIX"""
import sys, random
K, seed, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
rng = random.Random(seed)
def rank(vs):
    b = []
    for v in vs:
        for x in b:
            v = min(v, v ^ x)
        if v:
            b.append(v)
    return len(b)
while True:
    bases = []
    for _ in range(3):
        while True:
            bb = [rng.randrange(1, 1 << 16) for _ in range(7)]
            if rank(bb) == 7:
                break
        bases.append(bb)
    def comb(slot, coef):
        v = 0
        for j in range(7):
            if (coef >> j) & 1:
                v ^= bases[slot][j]
        return v
    prods = [[comb(s, rng.randrange(1, 128)) for s in range(3)] for _ in range(K)]
    prods[K - 1][2] = prods[K - 2][2]                     # the shared c-factor
    a, a2 = prods[K - 2][0], prods[K - 1][0]
    b, b2 = prods[K - 2][1], prods[K - 1][1]
    if a == a2 or b == b2 or any(rank([p[s] for p in prods]) != 7 for s in range(3)):
        continue
    if len({tuple(p) for p in prods}) < K:
        continue
    break
def tensor(ps):
    t = set()
    for p in ps:
        for i in range(16):
            if not (p[0] >> i) & 1: continue
            for j in range(16):
                if not (p[1] >> j) & 1: continue
                for k in range(16):
                    if (p[2] >> k) & 1:
                        t ^= {(i, j, k)}
    return t
c = prods[K - 1][2]
flipped = prods[:K - 2] + [[a, b ^ b2, c], [a ^ a2, b2, c]]
assert tensor(prods) == tensor(flipped), "the flip identity failed"
assert {tuple(p) for p in flipped} != {tuple(p) for p in prods}
bits = ''.join(format(p[0], '016b')[::-1] for p in prods) + ''.join(format(p[1], '016b')[::-1] for p in prods) + ''.join(format(p[2], '016b')[::-1] for p in prods)
open(out + '.bits', 'w').write(bits + '\n')
open(out + '.lines', 'w').write('A k=%d dims=7,7,7 idx=%s\n' % (K, ','.join(map(str, range(K)))))
print('planted K=%d seed=%d: factor spans 7,7,7; products %d,%d share the c-factor; flip verified on the tensor' % (K, seed, K - 2, K - 1))
