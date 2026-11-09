"""Which slot symmetries (S3 x transposes) stabilize a rank-r F2 scheme's de Groote class, and whether
the realizing sandwich can be read off as permutation matrices.  For each non-identity variant v(A)
of A, search a sandwich g with g.v(A) = A (term bijection + Kronecker slot maps, exactly as
scheme_iso.equivalent does for one fixed variant).  usage: stab_slots.py N A.bits [B.bits ...]"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(sys.argv[0])))
import scheme_iso as si
n = int(sys.argv[1])
def is_perm(M):
    rows = [si.bit(M, i, j, n) for i in range(n) for j in range(n)]
    return all(sum(si.bit(M, i, j, n) for j in range(n)) == 1 for i in range(n)) and all(sum(si.bit(M, i, j, n) for i in range(n)) == 1 for j in range(n))
for path in sys.argv[2:]:
    A = si.parse(path, n); conv = si.convention(A, n)
    print(f"{os.path.basename(path)}: rank {len(A)}, {len(si.variants(A, n, conv))} valid slot variants")
    for (vid, Av) in si.variants(A, n, conv):
        if vid == ((0, 1, 2), 0):
            continue
        nodes = [0]; cert = None; status = "NOT in the stabilizer"
        try:
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
                cert = maps; break
        except si.NodeCap:
            status = "UNDECIDED (node cap)"
        if cert:
            perms = all(is_perm(Pm) and is_perm(Qm) for Pm, Qm in cert)
            status = "IN the stabilizer; certificate maps " + ("are all permutation matrices" if perms else "are not all permutations (one certificate; others may exist)")
        print(f"  slot symmetry perm {vid[0]} transposes {vid[1]:03b}: {status}  ({nodes[0]} nodes)")
