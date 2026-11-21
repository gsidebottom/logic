#!/usr/bin/env python3
"""Constructive screen of the serendipitous Kronecker product (Smith; generalised by Sedoglavic; used at scale by
Perminov, arXiv:2606.02480, whose "buds" are the groups of products sharing a factor), with a build plan for
every format it puts below the table.  The block form with two non-unit dimensions (the "grids" below) is in
Perminov's Section 2.6.4; none of the product is ours.

serendip_screen.py prices the product with the ranks of the published table, for which we hold no schemes in
general.  Here every rank that enters a formula is the rank of a scheme we can write down: the lowest-rank file
we hold for the format, or a scheme made from such files by sub-format, direct sum and Kronecker product (the
"held" table, with a recipe per format).  The bar stays the published table closed under the same operations.

usage: serendip_plan.py TABLE.json BUDS.json OUT_DIR SCHEME_DIR... [shape=rank ...]
  TABLE.json   Sedoglavic's table ({"entries": [{"format": [a,b,c], "rank": r}]})
  BUDS.json    bud_groups.py output: per catalog scheme the groups of products sharing a factor
  SCHEME_DIR   directories searched (recursively) for AxBxC_mR_*.json[.gz] scheme files
  shape=rank   further ranks that lower the bar only (no scheme needed)
Environment: GRID=0 leaves out the grids (blocks of products sharing factors in two slots, an image of <1,q,r>:
q r rank(a,b,c) products become one scheme of <a, q b, r c>), which is then Perminov's product alone; SUB=FILE
adds the subspace grids found by subspace_grids.py (four products whose factors lie in a plane in two slots); PROCS.
Writes OUT_DIR/plans/AxBxC_mR.plan.json (input of `kronexact build`) and OUT_DIR/plans.json (the list).
Arithmetic and plans only: a format counts when `kronexact build` has built the scheme and certified it."""
import itertools, json, os, re, sys
N = 32
table, budsf, out = sys.argv[1:4]
dirs = [a for a in sys.argv[4:] if '=' not in a]
extras = [a for a in sys.argv[4:] if '=' in a]
fmts = list(itertools.combinations_with_replacement(range(1, N + 1), 3))
key = lambda a, b, c: tuple(sorted((a, b, c)))


def base(f):
    if f[1] == 1: return f[2]
    if f[0] == 1: return f[1] * f[2]
    return None


def close(C, rec=None):
    """In place: sub-format, split and product, until nothing changes.  rec, when given, gets a recipe per format."""
    g = lambda a, b, c: C.get(key(a, b, c))
    ch = True
    while ch:
        ch = False
        for f in reversed(fmts):
            for i in range(3):
                h = list(f); h[i] += 1
                r = g(*h) if h[i] <= N else None
                if r is not None and (C[f] is None or r < C[f]):
                    C[f] = r; ch = True
                    if rec is not None: rec[f] = ('sub', tuple(h))
        for f in fmts:
            for i in range(3):
                for c1 in range(1, f[i] // 2 + 1):
                    h = list(f); k = list(f); h[i] = c1; k[i] = f[i] - c1
                    r1, r2 = g(*h), g(*k)
                    if r1 is not None and r2 is not None and (C[f] is None or r1 + r2 < C[f]):
                        C[f] = r1 + r2; ch = True
                        if rec is not None: rec[f] = ('sum', i, tuple(h), tuple(k))
        small = [f for f in fmts if C[f] is not None and f[2] <= N // 2 and f != (1, 1, 1)]
        for f1 in small:
            for f2 in small:
                if f1 > f2 or f1[2] * f2[0] > N: continue
                for p in set(itertools.permutations(f2)):
                    h = tuple(sorted(x * y for x, y in zip(f1, p)))
                    if h[2] <= N and (C[h] is None or C[f1] * C[f2] < C[h]):
                        C[h] = C[f1] * C[f2]; ch = True
                        if rec is not None: rec[h] = ('prod', f1, p)


# ---- held schemes: lowest rank per format among the files
held = {}
for d in dirs:
    for r, _, fs in os.walk(d):
        for f in fs:
            m = re.fullmatch(r'(\d+)x(\d+)x(\d+)_m(\d+)_[^.]*\.json(\.gz)?', f)
            if not m or f.endswith('_reduced.json'): continue
            k = key(*map(int, m.group(1, 2, 3))); rank = int(m.group(4))
            if k[2] <= N and rank < held.get(k, (10 ** 9,))[0]: held[k] = (rank, os.path.join(r, f))
H = {f: base(f) for f in fmts}; rec = {f: ('trivial',) for f in fmts if base(f) is not None}
for k, (rank, path) in held.items():
    if H[k] is None or rank < H[k]: H[k] = rank; rec[k] = ('file', path)
close(H, rec)

# ---- the bar: published table, the held files and the extra ranks, closed
tab = {tuple(e['format']): e['rank'] for e in json.load(open(table))['entries']}
B = {f: base(f) if base(f) is not None else tab.get(f) for f in fmts}
for k, (rank, _) in held.items():
    if B[k] is None or rank < B[k]: B[k] = rank
for a in extras:
    s, r = a.split('='); k = key(*map(int, s.split('x')))
    if B[k] is None or int(r) < B[k]: B[k] = int(r)
close(B)
print('formats: %d; held table defined on %d, equal to the bar on %d, above it on %d (by %d products in all)' % (
    len(fmts), sum(v is not None for v in H.values()), sum(H[f] == B[f] for f in fmts if H[f] is not None),
    sum(H[f] > B[f] for f in fmts if H[f] is not None), sum(H[f] - B[f] for f in fmts if H[f] is not None)), flush=True)
assert all(H[f] is None or (B[f] is not None and H[f] >= B[f]) for f in fmts)
hr = lambda a, b, c: H.get(key(a, b, c)) if max(a, b, c) <= N else None
f3 = lambda slot, h, s2: [(s2[0], s2[1], h * s2[2]), (h * s2[0], s2[1], s2[2]), (s2[0], h * s2[1], s2[2])][slot]


def split(slot, g, s2, r2):
    """Best partition of g products sharing a factor into replaced chunks: (saving, chunk sizes)."""
    best = [0] * (g + 1); choice = [0] * (g + 1)
    for t in range(2, g + 1):
        best[t] = best[t - 1]
        for h in range(2, t + 1):
            r3 = hr(*f3(slot, h, s2))
            if r3 is not None and best[t - h] + h * r2 - r3 > best[t]: best[t] = best[t - h] + h * r2 - r3; choice[t] = h
    sizes = []; t = g
    while t >= 2:
        if choice[t]: sizes.append(choice[t]); t -= choice[t]
        else: t -= 1
    return best[g], sizes


GRID = os.environ.get('GRID', '1') == '1'
SUBS = json.load(open(os.environ['SUB'])) if os.environ.get('SUB') else {}      # subspace_grids.py output
PAIRS = ((0, 2), (0, 1), (1, 2))                 # the two slots in which the products of a grid share factors


def grid_type(pair, q, r):
    """Block type (P, Q, R) of a q x r grid: q classes in the pair's first slot, r in its second."""
    return {(0, 2): (1, q, r), (0, 1): (q, 1, r), (1, 2): (r, q, 1)}[pair]


def grid_cell(pair, x, y):
    return {(0, 2): (0, x, y), (0, 1): (x, 0, y), (1, 2): (y, x, 0)}[pair]


def bicliques(cx, cy, cap=60):
    """Grids: sets X, Y of proportionality classes of two slots with a product in every (x, y).  Closures of
    pairs of classes on either side; the largest `cap` by area.  Returns [(X list, Y list, {(x, y): product})]."""
    adj = {}
    for t, x in cx.items():
        if t in cy: adj.setdefault(x, {}).setdefault(cy[t], t)
    radj = {}
    for x, d in adj.items():
        for y in d: radj.setdefault(y, set()).add(x)
    xs = [x for x in adj if len(adj[x]) >= 2]; ys = [y for y in radj if len(radj[y]) >= 2]
    sets = {x: set(adj[x]) for x in xs}
    found = set()
    for x1, x2 in itertools.combinations(xs, 2):
        Y = sets[x1] & sets[x2]
        if len(Y) >= 2: found.add((frozenset(x for x in xs if Y <= sets[x]), frozenset(Y)))
    for y1, y2 in itertools.combinations(ys, 2):
        X = radj[y1] & radj[y2]
        if len(X) >= 2: found.add((frozenset(X), frozenset(y for y in ys if X <= radj[y])))
    top = sorted(found, key=lambda c: (-len(c[0]) * len(c[1]), sorted(c[0]), sorted(c[1])))[:cap]
    return [(sorted(X), sorted(Y), adj) for X, Y in top]


def gsave(pair, q, r, s2, r2):
    """Saving of a q x r grid, and of its best sub-grid: (saving, q', r')."""
    best = (0, 0, 0)
    for qq in range(2, q + 1):
        for rr in range(2, r + 1):
            ty = grid_type(pair, qq, rr)
            r3 = hr(*(ty[i] * s2[i] for i in range(3)))
            if r3 is not None and qq * rr * r2 - r3 > best[0]: best = (qq * rr * r2 - r3, qq, rr)
    return best


def chunk_block(slot, prods):
    d = (slot + 2) % 3
    ty = [1, 1, 1]; ty[d] = len(prods)
    cells = []
    for i, t in enumerate(prods):
        c = [0, 0, 0]; c[d] = i; cells.append([t] + c)
    return tuple(ty), cells


def choose(grp, grids, subs, s2, r2):
    """Disjoint blocks, by decreasing saving, each restricted to the products still free: (saving, blocks)."""
    memo = {}; gmemo = {}
    def sp(slot, g):
        if (slot, g) not in memo: memo[slot, g] = split(slot, g, s2, r2)
        return memo[slot, g]
    def gs(pair, q, r):
        if (pair, q, r) not in gmemo: gmemo[pair, q, r] = gsave(pair, q, r, s2, r2)
        return gmemo[pair, q, r]
    cand = [(sp(slot, len(x))[0], 0, slot, x) for slot in range(3) for x in grp[slot]]
    cand += [(gs(pair, len(X), len(Y))[0], 1, pair, (X, Y, adj)) for pair, X, Y, adj in grids]
    cand += [(gs(pair, 2, 2)[0], 2, pair, S) for pair, S in subs if gs(pair, 2, 2)[1:] == (2, 2)]
    cand.sort(key=lambda t: (-t[0], t[1], str(t[2])))
    used = set(); total = 0; blocks = []
    for s0, kind, where, x in cand:
        if s0 <= 0: break
        if kind == 0:
            free = [i for i in x if i not in used]
            s, sizes = sp(where, len(free))
            if s <= 0: continue
            total += s; at = 0
            for h in sizes:
                blocks.append(chunk_block(where, free[at:at + h])); used.update(free[at:at + h]); at += h
        elif kind == 2:
            if used & set(x): continue
            total += s0; blocks.append((grid_type(where, 2, 2), ('sub', where, list(x)))); used.update(x)
        else:
            X, Y, adj = x
            Y = [y for y in Y if all(adj[xx][y] not in used for xx in X)]
            if len(Y) < 2:
                Y = x[1]; X = [xx for xx in X if all(adj[xx][y] not in used for y in Y)]
            if len(X) < 2 or len(Y) < 2: continue
            s, q, r = gs(where, len(X), len(Y))
            if s <= 0: continue
            X, Y = X[:q], Y[:r]
            cells = [[adj[xx][y]] + list(grid_cell(where, i, j)) for i, xx in enumerate(X) for j, y in enumerate(Y)]
            assert not used & {c[0] for c in cells}
            total += s; blocks.append((grid_type(where, q, r), cells)); used.update(c[0] for c in cells)
    return total, blocks


def one(item):
    path, n, m, grp = item
    res = {}
    if not isinstance(grp, list): return res
    gmax = [max((len(x) for x in grp[slot]), default=0) for slot in range(3)]
    grids = []
    if GRID:
        cls = [{t: ci for ci, g in enumerate(grp[s]) for t in g} for s in range(3)]
        grids = [(pair, X, Y, adj) for pair in PAIRS for X, Y, adj in bicliques(cls[pair[0]], cls[pair[1]])]
    sizes = {(pair, len(X), len(Y)) for pair, X, Y, _ in grids}
    subs = [((a, b), S) for a, b, S, _ in SUBS.get(path, []) if len(S) == 4]
    sizes |= {(pair, 2, 2) for pair, _ in subs}
    for s2 in itertools.product(range(1, N + 1), repeat=3):
        if any(n[i] * s2[i] > N for i in range(3)) or s2 == (1, 1, 1): continue
        r2 = hr(*s2)
        if r2 is None: continue
        f = key(*(n[i] * s2[i] for i in range(3)))
        if B[f] is None: continue
        if all(split(slot, gmax[slot], s2, r2)[0] <= 0 for slot in range(3)) and all(gsave(pair, q, r, s2, r2)[0] <= 0 for pair, q, r in sizes): continue
        total, blocks = choose(grp, grids, subs, s2, r2)
        rank = m * r2 - total
        if total > 0 and rank < B[f] and rank < res.get(f, (10 ** 9,))[0]:
            res[f] = (rank, B[f], tab.get(f), path, s2, total, blocks)
    return res


def sub_vectors(path, pair, S):
    """Explicit vectors of a subspace grid: the factors of the four products S lie in a plane in each slot of
    `pair`; with bases A_0, A_1 and C_0, C_1 of the planes and x_t = sum_j al_tj A_j, y_t = sum_k ga_tk C_k,
    sum_t x_t (x) y_t (x) z_t = sum_jk A_j (x) C_k (x) B_jk,  B_jk = sum_t al_tj ga_tk z_t."""
    from fractions import Fraction
    d = json.load(open(path))
    rows = [[[Fraction(str(v)) for v in d[k][t]] for t in S] for k in 'uvw']
    def plane(vs):
        for a in range(len(vs)):
            for b in range(a + 1, len(vs)):
                for c0 in range(len(vs[0])):
                    for c1 in range(c0 + 1, len(vs[0])):
                        det = vs[a][c0] * vs[b][c1] - vs[a][c1] * vs[b][c0]
                        if det == 0: continue
                        co = []
                        for v in vs:
                            al = (v[c0] * vs[b][c1] - v[c1] * vs[b][c0]) / det
                            be = (vs[a][c0] * v[c1] - vs[a][c1] * v[c0]) / det
                            assert all(v[i] == al * vs[a][i] + be * vs[b][i] for i in range(len(v))), 'not in a plane'
                            co.append((al, be))
                        return [vs[a], vs[b]], co
        raise SystemExit('no plane')
    X, Y = pair; Z = 3 - X - Y
    A, al = plane(rows[X]); C, ga = plane(rows[Y])
    Bv = {(j, k): [sum(al[t][j] * ga[t][k] * rows[Z][t][i] for t in range(len(S))) for i in range(len(rows[Z][0]))] for j in range(2) for k in range(2)}
    sparse = lambda v: [[i, str(x)] for i, x in enumerate(v) if x != 0]
    co = lambda slot, c: (c[slot], c[(slot + 1) % 3])
    vecs = [[], [], []]
    for j in range(2):
        vecs[X].append([*co(X, grid_cell(pair, j, 0)), sparse(A[j])])
        vecs[Y].append([*co(Y, grid_cell(pair, 0, j)), sparse(C[j])])
        for k in range(2): vecs[Z].append([*co(Z, grid_cell(pair, j, k)), sparse(Bv[j, k])])
    return vecs


def group_json(path, ty, body, s3):
    if body and body[0] == 'sub': return {'type': list(ty), 'members': body[2], 'vectors': sub_vectors(path, body[1], body[2]), 's3': s3}
    return {'type': list(ty), 'cells': body, 's3': s3}


name = lambda f: 'f_%d_%d_%d' % f
ref = lambda dims: {'op': 'orient', 'n': list(dims), 'of': {'op': 'ref', 'name': name(key(*dims))}}


def node(f):
    r = rec[f]
    if r[0] == 'trivial': return {'op': 'trivial', 'n': list(f)}
    if r[0] == 'file': return {'op': 'file', 'path': r[1]}
    if r[0] == 'sub': return {'op': 'sub', 'n': list(f), 'of': ref(r[1])}
    if r[0] == 'sum': return {'op': 'sum', 'axis': r[1], 'parts': [ref(r[2]), ref(r[3])]}
    return {'op': 'prod', 'parts': [ref(r[1]), ref(r[2])]}


def needs(f, acc):
    if f in acc: return
    acc[f] = node(f)
    r = rec[f]
    for d in {'sub': r[1:2], 'sum': r[2:4], 'prod': r[1:3]}.get(r[0], ()): needs(key(*d), acc)


if __name__ == '__main__':
    import multiprocessing
    multiprocessing.set_start_method('fork')
    buds = json.load(open(budsf))
    buds.sort(key=lambda x: -(x[2] or 0))
    best = {}
    with multiprocessing.Pool(int(os.environ.get('PROCS', '10'))) as pool:
        for res in pool.imap_unordered(one, buds, chunksize=1):
            for f, v in res.items():
                if v[0] < best.get(f, (10 ** 9,))[0]: best[f] = v
    os.makedirs(os.path.join(out, 'plans'), exist_ok=True)
    rows = []
    for f in sorted(best):
        rank, bar, t, path, s2, total, blocks = best[f]
        dims3 = lambda ty: tuple(ty[i] * s2[i] for i in range(3))
        acc = {}
        needs(key(*s2), acc)
        for ty, cells in blocks: needs(key(*dims3(ty)), acc)
        plan = {'defs': {name(k): v for k, v in acc.items()},
                'out': {'op': 'shared', 's1': {'op': 'file', 'path': path}, 's2': ref(s2),
                        'groups': [group_json(path, ty, cells, ref(dims3(ty))) for ty, cells in blocks]},
                'max_rank': rank,
                'note': {'method': 'Kronecker product with blocks of products sharing factors replaced (shared-factor product of '
                                   'Perminov, arXiv:2606.02480; blocks [P,Q,R] with two entries above 1 are grids sharing factors in two slots)',
                         's1': os.path.basename(path), 's2': list(s2), 'replaced': [[list(ty), list(dims3(ty))] for ty, cells in blocks]}}
        pn = '%dx%dx%d_m%d.plan.json' % (*f, rank)
        json.dump(plan, open(os.path.join(out, 'plans', pn), 'w'), separators=(',', ':'))
        rows.append({'format': list(f), 'formula': rank, 'bar': bar, 'table': t, 's1': os.path.basename(path), 's2': list(s2),
                     'saving': total, 'plan': pn, 'blocks': [list(ty) for ty, _ in blocks],
                     'subspace': sum(1 for _, b in blocks if b and b[0] == 'sub')})
        print('%dx%dx%d' % f, 'formula', rank, 'bar', bar, 'table', t, '|', os.path.basename(path), '(x) %dx%dx%d' % tuple(s2), 'saving', total,
              'grids', sum(sorted(ty)[1] > 1 for ty, _ in blocks), 'subspace', sum(1 for _, b in blocks if b and b[0] == 'sub'))
    json.dump(rows, open(os.path.join(out, 'plans.json'), 'w'), indent=1)
    print('formats below the bar: %d, total gain %d' % (len(rows), sum(r['bar'] - r['formula'] for r in rows)))
