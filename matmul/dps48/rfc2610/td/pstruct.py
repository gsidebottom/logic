import json, sys
src = open('/Users/greg/projects/logic/matmul/dps48/rfc2610/canon_enum.py').read()
pre, pcl = sys.argv[1], sys.argv[2]
sys.argv = ['x', pre, '/dev/null']
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()): exec(src[:src.index('t = time.time()')])
rows_ = json.load(open(f"{pcl}/pside.json"))
pc = json.load(open("/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad/td/canon_pclasses.json"))
# classes.json order follows sorted (-cP, nnz) of the canon list
order = sorted(pc, key=lambda r: (-r[0], r[1]))
bits = lambda m: tuple(i for i in range(8) if (m >> i) & 1)
deep = {"c10_n260_1": 88, "c10_n260_2": 88, "c10_n264_4": 88, "c10_n248_0": 89, "c10_n260_3": 89}
items = []
for i, (r, (cP, nz, pairs)) in enumerate(zip(rows_, order)):
    cost = min(r["P"] + ([deep[r["tag"]]] if r["tag"] in deep else []))
    if cost > 90: continue
    As = sorted({sel["X"][x][1] for z, x in pairs}); Cs = sorted({sel["Z"][z][0] for z, x in pairs})
    items.append((cost, r["tag"], len(pairs), As, Cs))
print(f"{len(items)} P classes with cost <= 90")
allA = set(); allC = set()
for c, t, n, As, Cs in sorted(items):
    print(f"  P {c}  {t:14s} {n:3d} pairs, {len(As)} distinct A, {len(Cs)} distinct C"); allA |= set(As); allC |= set(Cs)
print("distinct A overall", len(allA), " distinct C overall", len(allC))
ind = lambda c, L: np.linalg.matrix_rank(np.array([L[i] for i in c], float)) == 4
print("all 4-subsets of row lines X that are bases:", sum(ind(c, row["X"]) for c in itertools.combinations(range(8), 4)), "; col lines Z:", sum(ind(c, col["Z"]) for c in itertools.combinations(range(8), 4)))
print("row lines X:", row["X"]); print("col lines Y:", col["Y"]); print("row lines Y:", row["Y"])
