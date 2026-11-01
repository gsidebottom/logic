#!/usr/bin/env python3
"""Gates on iso_between.py's output, from the raw .sms files and independent of its transport.
  A. Every isotropy and every stabilizer element, applied to [L; R; P] as RFC 2610 writes it (a map, then Lemma 2.1),
     gives the target's rank-one terms exactly; the chosen image multiplies matrices (16^3 equations read directly).
  B. Sedoglavic's recipe: g s g^-1 runs over the target's stabilizer, one to one, as s runs over the source's.
  C. By DPS's uniqueness, every isotropy between the two gamma_2 minimizers must be orthogonal.
Then the target's signed-permutation subgroup, and the text for him.

  iso_gate.py DATA_DIR WORK_DIR REPORT.txt
"""
import itertools, json, random, sys
from collections import Counter
from fractions import Fraction as Fr
data, work, report = sys.argv[1:4]
N = range(4)

def read_sms(path):
    M = None
    for ln in open(path):
        p = ln.split()
        if M is None:
            if len(p) >= 2 and p[0].isdigit() and p[1].isdigit():
                M = [[Fr(0)] * int(p[1]) for _ in range(int(p[0]))]
            continue
        if len(p) < 3 or (p[0] == "0" and p[1] == "0"):
            break
        M[int(p[0]) - 1][int(p[1]) - 1] = Fr(p[2])
    return M
def lrp(name): return tuple(read_sms(f"{data}/4x4x4_48_{name}_{s}.sms") for s in "LRP")
def mm(A, B): return [[sum(a * b for a, b in zip(r, c)) for c in zip(*B)] for r in A]
def tr(A): return [list(r) for r in zip(*A)]
def kron(A, B): return [[a * b for a in ra for b in rb] for ra in A for rb in B]
def inv(M):
    n = len(M)
    A = [[Fr(x) for x in r] + [Fr(int(i == j)) for j in range(n)] for i, r in enumerate(M)]
    for c in range(n):
        p = next(i for i in range(c, n) if A[i][c] != 0)
        A[c], A[p] = A[p], A[c]
        A[c] = [x / A[c][c] for x in A[c]]
        for i in range(n):
            if i != c and A[i][c] != 0:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[c])]
    return [r[n:] for r in A]
K = [[Fr(0)] * 16 for _ in range(16)]
for a, b in itertools.product(N, repeat=2): K[b * 4 + a][a * 4 + b] = Fr(1)
ACT = {"[L; R; P]": lambda L, R, P: (L, R, P),
       "[R K; L K; K P]": lambda L, R, P: (mm(R, K), mm(L, K), mm(K, P)),
       "[R; P^T K; K L^T]": lambda L, R, P: (R, mm(tr(P), K), mm(K, tr(L))),
       "[L K; P^T; R^T]": lambda L, R, P: (mm(L, K), tr(P), tr(R)),
       "[P^T K; L; K R^T]": lambda L, R, P: (mm(tr(P), K), L, mm(K, tr(R))),
       "[P^T; R K; L^T]": lambda L, R, P: (tr(P), mm(R, K), tr(L))}
def lemma21(L, R, P, U, V, W):
    "Lemma 2.1 of the note: L (U^-1 o V^T), R (V^-1 o W^T), (U o W^-T) P"
    Ui, Vi, Wi = inv(U), inv(V), inv(W)
    return mm(L, kron(Ui, tr(V))), mm(R, kron(Vi, tr(W))), mm(kron(U, tr(Wi)), P)
def computes(L, R, P):
    "vec(AB) = P (L vec A * R vec B), all 16^3 equations"
    bad = 0
    for i, j, l in itertools.product(range(16), repeat=3):
        v = sum(L[k][i] * R[k][j] * P[l][k] for k in range(48))
        a, b, c, d = i // 4, i % 4, j // 4, j % 4
        bad += v != (1 if b == c and l == a * 4 + d else 0)
    return bad
def scalar(a, b):
    "s with a = s b, or None"
    s = None
    for x, y in zip(a, b):
        if y == 0:
            if x != 0: return None
        elif s is None: s = x / y
        elif x != s * y: return None
    return s
def chk_image(img, tgt, pi):
    L, R, P = img; L2, R2, P2 = tgt
    Pt, Pt2 = tr(P), tr(P2)
    sc = []
    for k in range(48):
        t = pi[k]
        a, b, c = scalar(L[k], L2[t]), scalar(R[k], R2[t]), scalar(Pt[k], Pt2[t])
        if None in (a, b, c) or a * b * c != 1: return None
        sc.append((a, b, c))
    return sc

# triples: the same action as lwh_transport, written again here on single triples
def slotmap(name, t):
    A, B, C = t
    b = {"id": (A, B, C), "cyc": (B, C, A), "cyc2": (C, A, B)}[name.split("+")[0]]
    return (tr(b[2]), tr(b[1]), tr(b[0])) if name.endswith("+rev") else b
NAMES = ["id", "cyc", "cyc2", "id+rev", "cyc+rev", "cyc2+rev"]
rng = random.Random(20261101)
def rnd(): return [[Fr(rng.randint(-99, 99), rng.randint(1, 9)) for _ in N] for _ in N]
gen = tuple(rnd() for _ in range(3))
INV = {n: next(m for m in NAMES if slotmap(m, slotmap(n, gen)) == gen) for n in NAMES}
class El:
    def __init__(s, d):
        s.d = d; s.slot = d["slot"]
        s.X, s.Y, s.Z = ([[Fr(x) for x in r] for r in d[k]] for k in "XYZ")
        s.Xi, s.Yi, s.Zi = inv(s.X), inv(s.Y), inv(s.Z)
    def __call__(s, t):
        a, b, c = slotmap(s.slot, t)
        return mm(mm(s.X, a), s.Yi), mm(mm(s.Y, b), s.Zi), mm(mm(s.Z, c), s.Xi)
    def inverse(s, t):
        A, B, C = t
        return slotmap(INV[s.slot], (mm(mm(s.Xi, A), s.Y), mm(mm(s.Yi, B), s.Z), mm(mm(s.Zi, C), s.X)))
def key(t):
    "a triple up to scalars on its legs, with the product of those scalars"
    out, p = [], Fr(1)
    for M in t:
        f = next(x for r in M for x in r if x)
        out.append(tuple(x / f for r in M for x in r)); p *= f
    return tuple(out), p
def load(n): return [El(d) for d in json.load(open(f"{work}/{n}.json"))]
def show(M): return "\n".join("    " + " ".join(f"{x:>4d}" for x in r) for r in M)
def height(d): return max(abs(x) for m in "UVW" for r in d[m] for x in r), sum(1 for m in "UVW" for r in d[m] for x in r if x)

rat, acc, a262 = lrp("rational"), lrp("accurate"), lrp("accurate_262")
G, GA, GO, Sr, St = load("rat_262"), load("rat_acc"), load("acc_262"), load("rat_rat"), load("s262")
print("sizes: rational -> 262", len(G), " rational -> accurate", len(GA), " accurate -> 262", len(GO), " stabilizers", len(Sr), len(St))
print("slot maps of rational -> 262:", dict(Counter(e.d["act"] for e in G)))
print("slot maps of rational's stabilizer:", dict(Counter(e.d["act"] for e in Sr)), " of 262's:", dict(Counter(e.d["act"] for e in St)))

# A
LABEL = {"[L; R; P]": "1", "[R K; L K; K P]": "3", "[R; P^T K; K L^T]": "5", "[L K; P^T; R^T]": "6"}
def pick(L): return min(L, key=lambda e: (e.d["act"] not in LABEL, height(e.d)))
def image(e, src): return lemma21(*ACT[e.d["act"]](*src), e.d["U"], e.d["V"], e.d["W"])
for n, L, src, tgt in (("rational -> 262", G, rat, a262), ("rational -> accurate", GA, rat, acc), ("accurate -> 262", GO, acc, a262),
                       ("stabilizer of rational", Sr, rat, rat), ("stabilizer of 262", St, a262, a262)):
    print(f"A {n}: terms equal on all 48 in", sum(chk_image(image(e, src), tgt, e.d["pi"]) is not None for e in L), "of", len(L))
g, ga, gh = pick(G), pick(GA), pick(GO)
img = image(g, rat)
scg = chk_image(img, a262, g.d["pi"])
print(f"A chosen rational -> 262: {g.d['act']}, image fails {computes(*img)} of 4096 equations")
img = image(ga, rat)
print(f"A chosen rational -> accurate: {ga.d['act']}, image fails {computes(*img)} of 4096 equations")

# B
T = [tuple(rnd() for _ in range(3)) for _ in range(2)]
tab = {tuple(key(e(t))[0] for t in T): i for i, e in enumerate(St)}
assert len(tab) == len(St)
hit = [tab.get(tuple(key(g(s(g.inverse(t))))[0] for t in T)) for s in Sr]
print(f"B g s g^-1 in 262's stabilizer: {sum(h is not None for h in hit)} of {len(Sr)}, distinct images {len(set(hit))}")
sb = Counter((Sr[i].d["act"], St[h].d["act"]) for i, h in enumerate(hit) if h is not None)
print("  slot map of s -> slot map of g s g^-1:", dict(sb))
t3 = tuple(rnd() for _ in range(3))
print("  on a fresh triple, up to leg scalars with product 1:", sum(key(g(s(g.inverse(t3)))) == key(St[h](t3)) for s, h in zip(Sr, hit) if h is not None))

# C
def orth(M):
    P = mm(M, tr(M))
    return all(P[i][j] == 0 for i in N for j in N if i != j) and len({P[i][i] for i in N}) == 1
print("C accurate -> 262, orthogonal up to scale in all three modes:", sum(all(orth(m) for m in (e.X, e.Y, e.Z)) for e in GO), "of", len(GO))
ents = Counter(abs(x) for e in GO for m in "UVW" for r in e.d[m] for x in r)
print("  |entries| of the primitive U, V, W:", dict(sorted(ents.items())))
print("  chosen:", gh.d["act"]); [print(m, "=\n" + show(gh.d[m])) for m in "UVW"]

# the signed permutations
M8 = [e for e in St if all(e.d["mono"])]
print(f"signed permutations in all three modes at 262: {len(M8)}")
ids = [e for e in M8 if e.d["ct"] == [1] * 48]
print("  by map and cycle type:", dict(Counter((e.d["act"], tuple(sorted(Counter(e.d["ct"]).items()))) for e in M8)))
tb = {tuple(key(e(t))[0] for t in T): i for i, e in enumerate(M8)}
prod = [[tb.get(tuple(key(a(b(t)))[0] for t in T)) for b in M8] for a in M8]
print("  closed under composition:", all(x is not None for r in prod for x in r))
e0 = next(i for i, e in enumerate(M8) if e.d["ct"] == [1] * 48 and e.d["slot"] == "id")
def order(i):
    o, j = 1, i
    while j != e0: j, o = prod[j][i], o + 1
    return o
print("  orders:", sorted(order(i) for i in range(len(M8))), " abelian:", all(prod[a][b] == prod[b][a] for a in range(8) for b in range(8)))
print("  order 4, trivial slot map, in the 8:", sum(order(i) == 4 and M8[i].slot == "id" for i in range(len(M8))))
print("  per mode at 262, signed permutation in:", [sum(e.d["mono"][i] for e in St) for i in range(3)], "of", len(St))

# what he needs, as text
with open(report, "w") as f:
    w = lambda s="": f.write(s + "\n")
    w("Isotropies between the original rational <4x4x4:48|315>, accurate and accurate_262, and the stabilizer of accurate_262.")
    w("Points: PLinOpt data/4x4x4_48_rational_*, 4x4x4_48_accurate_*, 4x4x4_48_accurate_262_*.")
    w("Notation of RFC 2610: apply the map to [L; R; P], then Lemma 2.1:")
    w("  L -> L (U^-1 o V^T),  R -> R (V^-1 o W^T),  P -> (U o W^-T) P.  K is the 16 x 16 commutation matrix.")
    w("U, V, W are primitive integer matrices, each defined up to a scalar.  Each isotropy below is one of 64, a coset of the stabilizer.")
    for ttl, e in (("rational -> accurate_262", g), ("rational -> accurate", ga), ("accurate -> accurate_262", gh)):
        w(); w(f"== {ttl}"); w(f"Map: {e.d['act']}"); [w(f"{m} =\n{show(e.d[m])}") for m in "UVW"]
    w()
    w("== rational -> accurate_262, term by term.  Numbered from 0.  Row k of the image's L is a(k) times row pi(k) of accurate_262's L,")
    w("row k of its R is b(k) times row pi(k) of the target's R, column k of its P is c(k) times column pi(k) of the target's P, and a b c = 1.")
    w("  " + "k: pi(k) a(k) b(k) c(k)")
    for k, (a, b, c) in enumerate(scg): w(f"  {k:2d}: {g.d['pi'][k]:2d}  {a}  {b}  {c}")
    w()
    w(f"== Stabilizer of accurate_262, all {len(St)} elements.  The {len(M8)} marked * are signed permutations in all three modes.")
    w("Each acts on accurate_262's [L; R; P] as above, up to the same per-term scalars; pi is the permutation of the 48 terms.")
    for i, e in enumerate(sorted(St, key=lambda e: (not all(e.d['mono']), NAMES.index(e.slot), height(e.d)))):
        w(); w(f"{i + 1}{' *' if all(e.d['mono']) else ''}  map {e.d['act']}, permutation of the terms {e.d['pi']}")
        [w(f"{m} =\n{show(e.d[m])}") for m in "UVW"]
print("wrote", report)
