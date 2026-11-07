#!/usr/bin/env python3
"""Exact de Groote equivalence of rank-r schemes of <n,n,n> over F2.

Two schemes are equivalent when a slot symmetry (S3 with transposes), a
term permutation and invertible sandwiches carry one onto the other.  The
test is exact both ways:
  EQUIVALENT      comes with a certificate (the symmetry variant of B, the
                  term bijection, the three slot maps M -> P M Q), re-verified
                  by applying it term by term;
  NOT EQUIVALENT  means the exhaustive search over term bijections consistent
                  with the term signatures (rank triple and the ranks of the
                  pairwise factor sums, both preserved by sandwiching), the
                  pair ranks and F2-linearity found none for any symmetry
                  variant of B.
Why slot-wise Kronecker maps suffice: three linear maps M -> P_k M Q_k on
the slots that carry the summands of A onto those of B fix the tensor, so
they lie in its isotropy group, which (de Groote) is the sandwich group;
the slot permutations are covered by trying every valid symmetry variant of
B (the images of B under the 48 slot permutation / transposition patterns
that are schemes of the tensor again).

usage: scheme_iso.py N A.bits B.bits [B2.bits ...]   test A against each B
       scheme_iso.py N --classes DIR...               de Groote classes of all
                                                      .bits schemes in DIRs
       scheme_iso.py N --selftest A.bits              controls: A against a
                                                      random sandwich of itself
                                                      with shuffled terms, and
                                                      against its variants
"""
import sys, os, glob, itertools, random
from collections import Counter

NODE_CAP = 5_000_000

def parse(path, n):
    b = open(path).read().split()[-1]
    w = 3 * n * n
    r = len(b) // w
    assert r * w == len(b), path
    def mat(off):
        return tuple(int(b[off + i * n: off + (i + 1) * n], 2) for i in range(n))
    sa, sb = r * n * n, 2 * r * n * n
    return [(mat(s * n * n), mat(sa + s * n * n), mat(sb + s * n * n)) for s in range(r)]

# a matrix is a tuple of n row ints; entry (i, j) = (M[i] >> (n-1-j)) & 1
def bit(M, i, j, n):
    return (M[i] >> (n - 1 - j)) & 1
def transpose(M, n):
    return tuple(sum(bit(M, i, j, n) << (n - 1 - i) for i in range(n)) for j in range(n))
def mul(P, M, n):
    out = []
    for i in range(n):
        v = 0
        for k in range(n):
            if bit(P, i, k, n):
                v ^= M[k]
        out.append(v)
    return tuple(out)
def xor(M, N):
    return tuple(a ^ b for a, b in zip(M, N))
def rank(M):
    rows = [x for x in M if x]
    r = 0
    while rows:
        piv = rows.pop()
        r += 1
        low = piv & -piv
        rows = [x ^ piv if x & low else x for x in rows]
        rows = [x for x in rows if x]
    return r
def inverse(M, n):
    rows = [(M[i] << n) | (1 << (n - 1 - i)) for i in range(n)]
    for col in range(n):
        pb = 2 * n - 1 - col
        piv = next((k for k in range(col, n) if (rows[k] >> pb) & 1), None)
        if piv is None:
            return None
        rows[col], rows[piv] = rows[piv], rows[col]
        for k in range(n):
            if k != col and (rows[k] >> pb) & 1:
                rows[k] ^= rows[col]
    return tuple(r & ((1 << n) - 1) for r in rows)
def unit(i, j, n):
    return tuple((1 << (n - 1 - j)) if r == i else 0 for r in range(n))
def pack(M, n):
    v = 0
    for row in M:
        v = (v << n) | row
    return v
def unpack(v, n):
    mask = (1 << n) - 1
    return tuple((v >> (n * (n - 1 - i))) & mask for i in range(n))
def fmt(M, n):
    return '/'.join(format(row, f'0{n}b') for row in M)

def valid(terms, n, conv):
    """conv 0: sum_s a_s[i,j] b_s[k,l] c_s = [j==k] E_il (c stores C = AB);
       conv 1: ... = [j==k] E_li (c stores C^T)."""
    pc = [pack(C, n) for _, _, C in terms]
    for i in range(n):
        for j in range(n):
            for k in range(n):
                for l in range(n):
                    acc = 0
                    for s, (A, B, _) in enumerate(terms):
                        if bit(A, i, j, n) and bit(B, k, l, n):
                            acc ^= pc[s]
                    want = 0
                    if j == k:
                        want = pack(unit(i, l, n) if conv == 0 else unit(l, i, n), n)
                    if acc != want:
                        return False
    return True

def convention(terms, n):
    for conv in (0, 1):
        if valid(terms, n, conv):
            return conv
    raise SystemExit("not a scheme of the matrix multiplication tensor in either convention")

def variants(terms, n, conv):
    """the distinct images of the scheme under the slot permutations and
    transposition patterns that are schemes again (the S3 symmetries)"""
    out, seen = [], set()
    for perm in itertools.permutations(range(3)):
        for tmask in range(8):
            new = []
            for t in terms:
                m = [t[perm[0]], t[perm[1]], t[perm[2]]]
                m = [transpose(m[k], n) if (tmask >> k) & 1 else m[k] for k in range(3)]
                new.append(tuple(m))
            key = tuple(sorted(new))
            if key in seen:
                continue
            if valid(new, n, conv):
                seen.add(key)
                out.append(((perm, tmask), new))
    return out

def signatures(terms):
    r = len(terms)
    rk = [tuple(rank(M) for M in t) for t in terms]
    pair = [[None] * r for _ in range(r)]
    for s in range(r):
        for t in range(s + 1, r):
            v = tuple(rank(xor(terms[s][k], terms[t][k])) for k in range(3))
            pair[s][t] = pair[t][s] = v
    sig = [(rk[s], tuple(sorted(pair[s][t] for t in range(r) if t != s))) for s in range(r)]
    return sig, pair

class Lin:
    """F2-linear consistency of a partial map src -> img on nbits-bit vectors:
    an echelon basis of (src | img) pairs pivoting on source bits."""
    def __init__(self, nbits):
        self.nbits = nbits
        self.basis = {}
    def copy(self):
        c = Lin(self.nbits)
        c.basis = dict(self.basis)
        return c
    def add(self, src, img):
        v = (src << self.nbits) | img
        mask = (1 << self.nbits) - 1
        while True:
            s = v >> self.nbits
            if s == 0:
                return (v & mask) == 0
            p = s.bit_length() - 1
            if p in self.basis:
                v ^= self.basis[p]
            else:
                self.basis[p] = v
                return True
    def image(self, src):
        v = src << self.nbits
        mask = (1 << self.nbits) - 1
        while True:
            s = v >> self.nbits
            if s == 0:
                return v & mask
            p = s.bit_length() - 1
            if p not in self.basis:
                return None
            v ^= self.basis[p]

class NodeCap(Exception):
    pass

def bijections(A, B, n, nodes):
    """yield (perm, lins) for every term bijection A -> B that respects the
    signatures, the pair ranks and F2-linearity on each slot"""
    r = len(A)
    sigA, pairA = signatures(A)
    sigB, pairB = signatures(B)
    if Counter(sigA) != Counter(sigB):
        return
    cands = {s: [t for t in range(r) if sigB[t] == sigA[s]] for s in range(r)}
    order = sorted(range(r), key=lambda s: len(cands[s]))
    perm = [None] * r
    used = set()
    nb = n * n
    pA = [[pack(M, n) for M in t] for t in A]
    pB = [[pack(M, n) for M in t] for t in B]
    def rec(idx, lins):
        if idx == r:
            yield list(perm), lins
            return
        s = order[idx]
        for t in cands[s]:
            if t in used:
                continue
            if any(pairA[s][s0] != pairB[t][perm[s0]] for s0 in order[:idx]):
                continue
            new = [l.copy() for l in lins]
            if not all(new[k].add(pA[s][k], pB[t][k]) for k in range(3)):
                continue
            nodes[0] += 1
            if nodes[0] > NODE_CAP:
                raise NodeCap()
            perm[s] = t
            used.add(t)
            yield from rec(idx + 1, new)
            perm[s] = None
            used.discard(t)
    yield from rec(0, [Lin(nb) for _ in range(3)])

def kron(lin, n):
    """(P, Q) with P M Q = image(M) on the whole space, 'span' if the source
    span is a proper subspace, None if the map is not of Kronecker form"""
    nb = n * n
    if len(lin.basis) < nb:
        return 'span'
    img = {}
    for i in range(n):
        for j in range(n):
            img[(i, j)] = unpack(lin.image(pack(unit(i, j, n), n)), n)
    QT = None
    P = [0] * n
    for ip in range(n):
        for i in range(n):
            blk = tuple(sum(bit(img[(i, j)], ip, jp, n) << (n - 1 - j) for j in range(n)) for jp in range(n))
            if any(blk):
                if QT is None:
                    QT = blk
                elif blk != QT:
                    return None
                P[ip] |= 1 << (n - 1 - i)
    if QT is None:
        return None
    return tuple(P), transpose(QT, n)

def gl(n):
    return [unpack(v, n) for v in range(1 << (n * n)) if rank(unpack(v, n)) == n]

_GL = {}
def kron_enum(pairs, n):
    """fallback when the slot's factors do not span: enumerate Q over GL(n,2)
    and solve P M Q = N column by column"""
    if n not in _GL:
        _GL[n] = gl(n)
    for Q in _GL[n]:
        lin = Lin(n)
        ok = True
        for M, N in pairs:
            MQ = mul(M, Q, n)
            for k in range(n):
                src = sum(bit(MQ, i, k, n) << (n - 1 - i) for i in range(n))
                img = sum(bit(N, i, k, n) << (n - 1 - i) for i in range(n))
                if not lin.add(src, img):
                    ok = False
                    break
            if not ok:
                break
        if not ok or len(lin.basis) < n:
            continue
        P = [0] * n
        for k in range(n):
            v = lin.image(1 << (n - 1 - k))
            for i in range(n):
                if (v >> (n - 1 - i)) & 1:
                    P[i] |= 1 << (n - 1 - k)
        P = tuple(P)
        if rank(P) == n:
            return P, Q
    return None

def equivalent(A, B, n, conv):
    """None if not equivalent, else a certificate dict (exact both ways)"""
    nodes = [0]
    for vid, Bv in variants(B, n, conv):
        try:
            for perm, lins in bijections(A, Bv, n, nodes):
                maps = []
                for k in range(3):
                    pq = kron(lins[k], n)
                    if pq == 'span':
                        pq = kron_enum([(A[s][k], Bv[perm[s]][k]) for s in range(len(A))], n)
                    if pq is None:
                        break
                    maps.append(pq)
                if len(maps) < 3:
                    continue
                # re-verify the certificate term by term
                for s in range(len(A)):
                    for k in range(3):
                        P, Q = maps[k]
                        assert mul(mul(P, A[s][k], n), Q, n) == Bv[perm[s]][k], "certificate fails"
                for P, Q in maps:
                    assert rank(P) == n and rank(Q) == n
                return {'variant': vid, 'perm': perm, 'maps': maps, 'nodes': nodes[0]}
        except NodeCap:
            return 'undecided'
    return None

def describe(cert, n):
    if cert == 'undecided':
        return f"UNDECIDED (node cap {NODE_CAP})"
    if cert is None:
        return "NOT EQUIVALENT"
    perm, tmask = cert['variant']
    maps = ' '.join(f"slot{k}: P {fmt(P, n)} Q {fmt(Q, n)}" for k, (P, Q) in enumerate(cert['maps']))
    return f"EQUIVALENT via variant perm {perm} transposes {tmask:03b}, {cert['nodes']} nodes; {maps}"

def random_sandwich(terms, n, conv, rng):
    def rand_gl():
        while True:
            M = tuple(rng.randrange(1 << n) for _ in range(n))
            if rank(M) == n:
                return M
    X, Y, Z = rand_gl(), rand_gl(), rand_gl()
    Yi, Zi, Xi = inverse(Y, n), inverse(Z, n), inverse(X, n)
    if conv == 1:
        new = [(mul(mul(X, a, n), Yi, n), mul(mul(Y, b, n), Zi, n), mul(mul(Z, c, n), transpose(Xi, n), n)) for a, b, c in terms]
    else:
        new = [(mul(mul(X, a, n), Yi, n), mul(mul(Y, b, n), Zi, n), mul(mul(transpose(Xi, n), c, n), transpose(Z, n), n)) for a, b, c in terms]
    assert valid(new, n, conv), "sandwich pattern wrong for this convention"
    rng.shuffle(new)
    return new

def main():
    n = int(sys.argv[1])
    args = sys.argv[2:]
    if args[0] == '--selftest':
        A = parse(args[1], n)
        conv = convention(A, n)
        vs = variants(A, n, conv)
        print(f"{args[1]}: rank {len(A)}, convention {conv} ({'c = C' if conv == 0 else 'c = C^T'}), {len(vs)} symmetry variants")
        rng = random.Random(1)
        for trial in range(3):
            B = random_sandwich(A, n, conv, rng)
            print(f"  random sandwich {trial}: {describe(equivalent(A, B, n, conv), n)}")
        for vid, Bv in vs[1:3]:
            print(f"  variant {vid}: {describe(equivalent(A, Bv, n, conv), n)}")
        return
    if args[0] == '--classes':
        files = []
        for d in args[1:]:
            files += sorted(glob.glob(os.path.join(d, '*.bits')))
        schemes = [(f, parse(f, n)) for f in files]
        conv = convention(schemes[0][1], n)
        # cheap first: group by rank-triple type (sorted triples: invariant under the variants)
        def typ(terms):
            return tuple(sorted(tuple(sorted(rank(M) for M in t)) for t in terms))
        groups = {}
        for f, t in schemes:
            groups.setdefault((len(t), typ(t)), []).append((f, t))
        classes = []   # (representative file, members)
        for key in sorted(groups, key=lambda k: (k[0], str(k[1]))):
            reps = []
            for f, t in groups[key]:
                for rep in reps:
                    cert = equivalent(rep[1], t, n, conv)
                    if cert == 'undecided':
                        print(f"  {f} vs {rep[0]}: UNDECIDED")
                        continue
                    if cert is not None:
                        rep[2].append(f)
                        print(f"  {f}: same class as {rep[0]} ({cert['nodes']} nodes)")
                        break
                else:
                    reps.append((f, t, [f]))
                    print(f"  {f}: new class representative")
            classes += [(r[0], r[2]) for r in reps]
        print(f"\n{len(schemes)} schemes, {len(groups)} rank-triple types, {len(classes)} de Groote classes:")
        for rep, members in classes:
            print(f"  {rep}: {len(members)} scheme(s): {' '.join(os.path.basename(m) for m in members)}")
        return
    A = parse(args[0], n)
    conv = convention(A, n)
    for f in args[1:]:
        B = parse(f, n)
        assert convention(B, n) == conv
        print(f"{args[0]} vs {f}: {describe(equivalent(A, B, n, conv), n)}")

if __name__ == '__main__':
    main()
