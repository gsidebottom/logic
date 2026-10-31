import sys
src = open('/Users/greg/projects/logic/matmul/dps48/rfc2610/canon_enum.py').read()
pre = sys.argv[1]; sys.argv = ['x', pre, '/dev/null']
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()): exec(src[:src.index('t = time.time()')])
Wn = np.array([[[float(x) for x in r] for r in w] for w in W])
pn = {}
def pnnz(z, x):
    if (z, x) in pn: return pn[(z, x)]
    sz, qx = sel["Z"][z][0], sel["X"][x][1]
    S = [col["Z"][i] for i in range(8) if (sz >> i) & 1]; Q = [row["X"][i] for i in range(8) if (qx >> i) & 1]
    if len(S) != 4 or len(Q) != 4: pn[(z, x)] = (-len(S), -len(Q)); return pn[(z, x)]
    Wp = np.linalg.inv(np.array(S, float).T) @ Wn @ np.linalg.inv(np.array(Q, float))
    pn[(z, x)] = int(np.count_nonzero(np.abs(Wp) > 1e-9)); return pn[(z, x)]
sz = lambda s: (bin(s[0]).count('1'), bin(s[1]).count('1'))
c = Counter(); ex = {}
for x in range(len(sel["X"])):
    for z in np.flatnonzero(PT[:, x] == 10):
        for y in np.flatnonzero((LT[x] == 6) & (RT[:, z] == 6)):
            k = (pnnz(int(z), x), sz(sel["Y"][y]), sz(sel["X"][x]), sz(sel["Z"][z]))
            c[k] += 1; ex.setdefault(k, (x, int(y), int(z)))
print("(6,6,10) triples by P nnz, sizes of the Y, X, Z selections (|S|,|Q|), and a representative (x, y, z):")
for k, v in sorted(c.items(), key=lambda kv: str(kv[0])): print("  ", k, v, ex[k])
json.dump([[list(map(str, k)), v, ex[k]] for k, v in c.items()], open(sys.argv[0] + '.json', 'w')) if False else None
