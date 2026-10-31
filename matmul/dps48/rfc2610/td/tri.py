import sys
src = open('/Users/greg/projects/logic/matmul/dps48/rfc2610/canon_enum.py').read()
pre = sys.argv[1]; sys.argv = ['x', pre, '/dev/null']
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()): exec(src[:src.index('t = time.time()')])
tri = Counter()
for x in range(len(sel["X"])):
    for y in range(len(sel["Y"])):
        c = Counter(zip(RT[y].tolist(), PT[:, x].tolist()))
        for (rr, pp), n in c.items(): tri[(int(LT[x, y]), rr, pp)] += n
for k in [(10,10,10),(8,8,10),(6,6,10),(6,4,10),(4,6,10),(10,10,6),(8,8,6),(6,6,6),(4,4,6),(8,6,10),(6,8,10),(10,6,10),(6,10,10)]:
    print(k, tri.get(k, 0))
print("(c,c,10) all:", sorted((k, v) for k, v in tri.items() if k[2] == 10 and k[0] == k[1]))
print("best c_L + c_R by c_P:", {p: max(k[0] + k[1] for k in tri if k[2] == p) for p in sorted({k[2] for k in tri}, reverse=True)})
