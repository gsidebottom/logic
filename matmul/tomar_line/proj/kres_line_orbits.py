"""Orbits of kres lines (index sets of products) under a scheme's slot-symmetry stabilizer.

For each non-identity slot variant v(A) of the F2 scheme A (S3 x transposes, scheme_iso.variants) that is
equivalent to A, scheme_iso.bijections gives a term bijection perm and Kronecker slot maps g with
g(A[s]) = v(A)[perm[s]] for every term s (asserted below).  Then phi = v^-1 g is a rank-one-preserving linear
isomorphism of the tensor space (a slot permutation with transposes and a sandwich in each slot) that maps
the scheme onto itself, sending term s to term perm[s]; it maps the sum of the terms of an index set I to the
sum over perm(I), so the two residuals have the same rank and the same number of decompositions: a kres
verdict (refuted / unique / alternative) is constant on the orbit.  Prints the image of every line.
usage: kres_line_orbits.py N SCHEME.bits LINES.txt   (lines with idx=i,j,...; duplicates are merged)"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(sys.argv[0])))
import scheme_iso as si
n = int(sys.argv[1])
A = si.parse(sys.argv[2], n); conv = si.convention(A, n)
lines = sorted({tuple(sorted(int(x) for x in l.split('idx=')[1].split()[0].split(','))) for l in open(sys.argv[3]) if 'idx=' in l})
print(f"{os.path.basename(sys.argv[2])}: {len(A)} terms; {len(lines)} distinct lines")
images = {I: {I} for I in lines}
for (vid, Av) in si.variants(A, n, conv):
    if vid == ((0, 1, 2), 0):
        continue
    nodes = [0]
    for perm, lins in si.bijections(A, Av, n, nodes):
        maps = []
        for k in range(3):
            pq = si.kron(lins[k], n)
            if pq == 'span':
                pq = si.kron_enum([(A[s][k], Av[perm[s]][k]) for s in range(len(A))], n)
            if pq is None:
                break
            maps.append(pq)
        if len(maps) < 3:
            continue
        for s in range(len(A)):
            for k in range(3):
                Pm, Qm = maps[k]
                assert si.mul(si.mul(Pm, A[s][k], n), Qm, n) == Av[perm[s]][k]
        print(f"slot variant perm {vid[0]} transposes {vid[1]:03b}: in the stabilizer, term permutation with "
              f"{sum(1 for s in range(len(A)) if perm[s] == s)} fixed terms")
        for I in lines:
            J = tuple(sorted(perm[s] for s in I))
            tag = "itself" if J == I else ("another line of the file" if J in images else "NOT a line of the file")
            print(f"  {','.join(map(str, I))} -> {','.join(map(str, J))}  ({tag})")
            if J in images:
                images[I] |= images[J]; images[J] = images[I]
        break
orbits = {frozenset(v) for v in images.values()}
print(f"{len(orbits)} orbits under the slot-symmetry elements found: sizes {sorted(len(o) for o in orbits)}")
