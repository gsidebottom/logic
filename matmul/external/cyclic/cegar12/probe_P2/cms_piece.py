"""Build a CryptoMiniSat instance for one piece of the cyclic-50 split:
Brent equations as native XOR constraints ("x" lines) over AND-gate
monomials, plus the same side constraints symcegar uses (indicators,
counter, lex on chosen orbits + fixed, pins, block equalities, and every
core in a cores file blocked with its 336 images).

usage: cms_piece.py map pin|- equal|- lexorbits|- cores|- dmax out.cnf
"""
import sys
sys.path.insert(0, "/Users/greg/projects/logic/matmul")
argv = sys.argv[1:]
sys.argv = ["x", "BIN", "CNF", "MAP", "/tmp/unused", "FBMIN"]
exec(open("/Users/greg/projects/logic/matmul/symcegar.py").read().split("# --- schemes")[0])
MAPF, PIN, EQUAL, LEXO, CORES, DMAX, OUT = argv[0], argv[1], argv[2], argv[3], argv[4], int(argv[5]), argv[6]
from brent import brent_equations

rep = {}
for ln in open(MAPF):
    v, r = ln.split()
    rep[int(v)] = int(r)
clauses, xors = [], []
nv = 621
monvar = {}


def new():
    global nv
    nv += 1
    return nv


def var_of(q):
    if q not in monvar:
        t = new()
        monvar[q] = t
        lits = sorted({m + 1 for m in q})
        for x in lits:
            clauses.append([-t, x])
        clauses.append([t] + [-x for x in lits])
    return monvar[q]


for mons, rhs in brent_equations(3, 3, 3, 23):
    seen = {}
    for m in mons:
        q = tuple(sorted(rep[v] for v in m))
        seen[q] = seen.get(q, 0) + 1
    lits = [var_of(q) for q, c in seen.items() if c % 2]
    if not lits:
        assert rhs == 0
        continue
    if rhs == 0:
        lits[0] = -lits[0]
    xors.append(lits)


def avar(m, k):
    return rep[9 * m + k] + 1


def block(m):
    return [avar(m, k) for k in range(9)]


def lex_le(x, y):
    eq = None
    for i in range(len(x)):
        a, b = x[i], y[i]
        clauses.append([-a, b] + ([-eq] if eq else []))
        if i + 1 < len(x):
            e2 = new()
            clauses.append([-a, -b, e2] + ([-eq] if eq else []))
            clauses.append([a, b, e2] + ([-eq] if eq else []))
            eq = e2


orbits = [(3 * j, 3 * j + 1, 3 * j + 2) for j in range(7)]
if LEXO != "-":
    chosen = [orbits[int(i)] for i in LEXO.split(",")]
    for o in chosen:
        lex_le(block(o[0]), block(o[1]))
        lex_le(block(o[0]), block(o[2]))
    cat = lambda o: [x for m in o for x in block(m)]
    for a, b in zip(chosen, chosen[1:]):
        lex_le(cat(a), cat(b))
    lex_le(block(21), block(22))
if PIN != "-":
    pat = open(PIN).read().strip()
    for p, ch in enumerate(pat):
        if ch in "01":
            lit = avar(p // 9, p % 9)
            clauses.append([lit] if ch == "1" else [-lit])
if EQUAL != "-":
    for pair in EQUAL.split(","):
        a, b = map(int, pair.split("="))
        for k in range(9):
            clauses.append([-avar(a, k), avar(b, k)])
            clauses.append([avar(a, k), -avar(b, k)])
ybase = nv
nv += 511
y = lambda v: ybase + v
for m in range(23):
    for v in range(1, 512):
        clauses.append([(-avar(m, k) if (v >> (8 - k)) & 1 else avar(m, k)) for k in range(9)] + [y(v)])
xs = [y(v) for v in range(1, 512)]
n, k = len(xs), DMAX
r = [[new() for _ in range(k)] for _ in range(n - 1)]
clauses.append([-xs[0], r[0][0]])
for j in range(1, k):
    clauses.append([-r[0][j]])
for i in range(1, n - 1):
    clauses.append([-xs[i], r[i][0]])
    clauses.append([-r[i - 1][0], r[i][0]])
    for j in range(1, k):
        clauses.append([-xs[i], -r[i - 1][j - 1], r[i][j]])
        clauses.append([-r[i - 1][j], r[i][j]])
    clauses.append([-xs[i], -r[i - 1][k - 1]])
clauses.append([-xs[n - 1], -r[n - 2][k - 1]])
nblock = 0
if CORES != "-":
    blocked = set()
    for ln in open(CORES):
        if ln.startswith("core "):
            core = tuple(int(t) for t in ln.split("|")[0].split()[1:])
            for img in images(core):
                if img not in blocked:
                    blocked.add(img)
                    clauses.append([-y(v) for v in range(512) if img >> v & 1])
    nblock = len(blocked)
with open(OUT, "w") as f:
    f.write(f"p cnf {nv} {len(clauses) + len(xors)}\n")
    for c in clauses:
        f.write(" ".join(map(str, c)) + " 0\n")
    for x in xors:
        f.write("x" + " ".join(map(str, x)) + " 0\n")
print(f"{OUT}: {nv} vars, {len(clauses)} clauses + {len(xors)} native XORs, {nblock} blocks")
