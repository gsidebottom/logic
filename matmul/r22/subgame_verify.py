#!/usr/bin/env python3
"""Independent checker for subgame certificates (substitution game over F_2).

  python3 matmul/r22/subgame_verify.py CERT.json

The certificate is a DAG of states (U, V, X) = killed subspaces of the
three sides of T = <n,n,n>, each with a claimed lower bound `value` on
the rank of the quotient tensor T/(U,V,X), and either
  choice 0 (leaf): value <= max flattening rank of T/(U,V,X) (or, when
      the certificate header says coset: true, the F_2 coset-counting
      bound, or koszul: P, the Koszul flattening bound with p <= P —
      both recomputed here), or
  choice s in {1,2,3} with functional phi: the tensor is NONZERO, phi
      lies in the annihilator of the killed subspace and does not vanish
      on the side's SUPPORT (the smallest subspace S with T' in S (x) ..),
      value <= 1 + min over the extensions U + <v>, v in S with phi.v = 1,
      of the child's claimed value, and every such child is present —
      either literally, or via an explicit sandwich-group element g
      (checked here to preserve the tensor) mapping it onto a node that
      is present; isomorphic states have equal rank.
Soundness: R(T') >= flattening ranks; a minimal decomposition of T' can
be taken with its side-s vectors in S, and they span S, so for any phi
not vanishing on S some product vector v has phi.v = 1; quotienting by
it leaves rank <= r - 1, hence R(T') >= 1 + min over those v of R(T'/v).
Everything (subspace RREF, annihilators, quotient tensors, ranks, the
set of extensions) is recomputed here from scratch; nothing is trusted
from the prover except the claimed numbers being checked.
"""
import json, sys


def rref(rows):
    out = []
    for r in rows:
        v = r
        for o in out:
            p = o.bit_length() - 1
            if v >> p & 1:
                v ^= o
        if v:
            p = v.bit_length() - 1
            out = [o ^ v if o >> p & 1 else o for o in out]
            out.append(v)
    return tuple(sorted(out, reverse=True))


def annihilator(u, d):
    r = rref(u)
    piv = [row.bit_length() - 1 for row in r]
    basis = []
    for f in range(d):
        if f in piv:
            continue
        phi = 1 << f
        for row, p in zip(r, piv):
            if row >> f & 1:
                phi |= 1 << p
        basis.append(phi)
    return basis


def matmul_tensor(n):
    d = n * n
    t = [[0] * d for _ in range(d)]
    for a in range(n):
        for b in range(n):
            for c in range(n):
                for dd in range(n):
                    for p in range(n):
                        for q in range(n):
                            if b == c and a == p and dd == q:
                                t[a * n + b][c * n + dd] |= 1 << (p * n + q)
    return d, t


def quotient(d, t0, u, v, x):
    phi, psi, chi = annihilator(u, d), annihilator(v, d), annihilator(x, d)
    # contract c, then b, then a
    s1 = [[sum(((bin(t0[a][b] & ck).count("1") & 1) << k) for k, ck in enumerate(chi))
           for b in range(d)] for a in range(d)]
    s2 = [[0] * len(psi) for _ in range(d)]
    for a in range(d):
        for j, pj in enumerate(psi):
            row = 0
            for b in range(d):
                if pj >> b & 1:
                    row ^= s1[a][b]
            s2[a][j] = row
    t = [[0] * len(psi) for _ in range(len(phi))]
    for i, fi in enumerate(phi):
        for j in range(len(psi)):
            row = 0
            for a in range(d):
                if fi >> a & 1:
                    row ^= s2[a][j]
            t[i][j] = row
    return (len(phi), len(psi), len(chi)), t


def rank(rows):
    rows = [r for r in rows if r]
    rk = 0
    while rows:
        piv = max(rows)
        rows.remove(piv)
        rk += 1
        hb = piv.bit_length() - 1
        rows = [r ^ piv if r >> hb & 1 else r for r in rows if r]
        rows = [r for r in rows if r]
    return rk


def flattenings(dims, t):
    da, db, dc = dims
    ra = [sum(t[a][b] << (b * dc) for b in range(db)) for a in range(da)]
    rb = [sum(t[a][b] << (a * dc) for a in range(da)) for b in range(db)]
    rc = []
    for c in range(dc):
        v = 0
        for a in range(da):
            for b in range(db):
                if t[a][b] >> c & 1:
                    v |= 1 << (a * db + b)
        rc.append(v)
    return [rank(ra), rank(rb), rank(rc)]


# ---- sandwich symmetry (3x3): g = (P,Q,R) acts A: P^T a Q^T, B: Q^-T b R^T, C: P^-1 c R^-1
def m3_mul(a, b):
    c = 0
    for i in range(3):
        for j in range(3):
            s = 0
            for k in range(3):
                s ^= (a >> (i * 3 + k) & 1) & (b >> (k * 3 + j) & 1)
            c |= s << (i * 3 + j)
    return c


def m3_tr(a):
    c = 0
    for i in range(3):
        for j in range(3):
            c |= (a >> (i * 3 + j) & 1) << (j * 3 + i)
    return c


_inv_cache = {}


def m3_inv(a):
    if a in _inv_cache:
        return _inv_cache[a]
    ident = 0b100010001
    for b in range(512):
        if m3_mul(a, b) == ident:
            _inv_cache[a] = b
            return b
    raise AssertionError("singular group element")


_mul_cache = {}


def m3_mul_c(a, b):
    k = (a, b)
    r = _mul_cache.get(k)
    if r is None:
        r = m3_mul(a, b)
        _mul_cache[k] = r
    return r


def apply_sandwich(P, Q, R, state, d):
    """same computation as before; products and inverses memoized (speed only)"""
    u, v, x = state
    Pt, Qt, Rt = m3_tr(P), m3_tr(Q), m3_tr(R)
    Qit, Pi, Ri = m3_tr(m3_inv(Q)), m3_inv(P), m3_inv(R)
    fa = lambda m: m3_mul_c(m3_mul_c(Pt, m), Qt)
    fb = lambda m: m3_mul_c(m3_mul_c(Qit, m), Rt)
    fc = lambda m: m3_mul_c(m3_mul_c(Pi, m), Ri)
    return (rref([fa(m) for m in u]), rref([fb(m) for m in v]), rref([fc(m) for m in x]))


_sym_cache = {}


def is_symmetry(n, P, Q, R):
    """does g preserve the matmul tensor? (recomputed, cached per g)"""
    if (P, Q, R) in _sym_cache:
        return _sym_cache[(P, Q, R)]
    d, t0 = matmul_tensor(n)
    Pt, Qt, Rt = m3_tr(P), m3_tr(Q), m3_tr(R)
    Qit, Pi, Ri = m3_tr(m3_inv(Q)), m3_inv(P), m3_inv(R)
    fa = lambda m: m3_mul(m3_mul(Pt, m), Qt)
    fb = lambda m: m3_mul(m3_mul(Qit, m), Rt)
    fc = lambda m: m3_mul(m3_mul(Pi, m), Ri)
    tt = [[0] * d for _ in range(d)]
    for a in range(d):
        ia = fa(1 << a)
        for b in range(d):
            ib = fb(1 << b)
            for c in range(d):
                if not t0[a][b] >> c & 1:
                    continue
                ic = fc(1 << c)
                for a2 in range(d):
                    if not ia >> a2 & 1:
                        continue
                    for b2 in range(d):
                        if ib >> b2 & 1:
                            tt[a2][b2] ^= ic
    ok = tt == t0
    _sym_cache[(P, Q, R)] = ok
    return ok


def matrix_rank_bits(v, rows, cols):
    mask = (1 << cols) - 1
    return rank([(v >> (r * cols)) & mask for r in range(rows)])


def coset_bound(dims, t):
    """F_2 coset-counting leaf bound (recomputed): per side, if every
    nonzero element of the slice span (dim w) has rank >= 3, distinct
    rank-one products inject into the nonzero cosets of the span inside
    their own span, so r <= 2^(r-w) - 1; least such r. 0 if no side
    satisfies the premise."""
    da, db, dc = dims
    best = 0
    for side in (1, 2, 3):
        if side == 1:
            rows_n, cols_n = db, dc
            sl = [sum(t[a][b] << (b * dc) for b in range(db)) for a in range(da)]
        elif side == 2:
            rows_n, cols_n = da, dc
            sl = [sum(t[a][b] << (a * dc) for a in range(da)) for b in range(db)]
        else:
            rows_n, cols_n = da, db
            sl = []
            for c in range(dc):
                v = 0
                for a in range(da):
                    for b in range(db):
                        if t[a][b] >> c & 1:
                            v |= 1 << (a * db + b)
                sl.append(v)
        basis = list(rref(sl))
        w = len(basis)
        if w == 0:
            continue
        ok = True
        for code in range(1, 1 << w):
            m = 0
            for i, b in enumerate(basis):
                if code >> i & 1:
                    m ^= b
            if matrix_rank_bits(m, rows_n, cols_n) <= 2:
                ok = False
                break
        if not ok:
            continue
        r = w
        while not (r <= 2 ** (r - w) - 1):
            r += 1
        best = max(best, r)
    return best


def binom(n, k):
    from math import comb
    return comb(n, k) if 0 <= k <= n else 0


def koszul_side(dims, t, p):
    """Koszul flattening bound on side A (recomputed): rows (S' in Λ^{p+1}, k),
    columns (S in Λ^p, j); entry T[i][j][k] at (S u {i}, k), (S, j), i not in S.
    R >= ceil(rank / C(da-1, p)). Valid over any field; signs vanish over F_2."""
    da, db, dc = dims
    if da < 3 or p == 0 or p + 2 > da:
        return 0
    subs_p = [m for m in range(1 << da) if bin(m).count("1") == p]
    subs_q = [m for m in range(1 << da) if bin(m).count("1") == p + 1]
    ip = {m: i for i, m in enumerate(subs_p)}
    iq = {m: i for i, m in enumerate(subs_q)}
    rows = [0] * (len(subs_q) * dc)
    for sm, si in ip.items():
        for i in range(da):
            if sm >> i & 1:
                continue
            qi = iq[sm | (1 << i)]
            for j in range(db):
                bits = t[i][j]
                if not bits:
                    continue
                col = si * db + j
                for k in range(dc):
                    if bits >> k & 1:
                        rows[qi * dc + k] |= 1 << col
    rk = rank(rows)
    den = binom(da - 1, p)
    return -(-rk // den)


def with_side_first(dims, t, side):
    da, db, dc = dims
    if side == 1:
        return dims, t
    if side == 2:
        return (db, da, dc), [[t[i][j] for i in range(da)] for j in range(db)]
    nt = [[0] * da for _ in range(dc)]
    for i in range(da):
        for j in range(db):
            for k in range(dc):
                if t[i][j] >> k & 1:
                    nt[k][i] |= 1 << j
    return (dc, da, db), nt


def koszul_bound(dims, t, pmax):
    best = 0
    for side in (1, 2, 3):
        d2, t2 = with_side_first(dims, t, side)
        if d2[0] < 3:
            continue
        for p in range(1, min(d2[0] - 2, pmax) + 1):
            best = max(best, koszul_side(d2, t2, p))
    return best


def parse_key(k):
    parts = k.split("|")
    geo = tuple(tuple(int(x, 16) for x in p.split(",")) if p else () for p in parts[:3])
    rmin = tuple(int(x) for x in parts[3].split(",")) if len(parts) > 3 else (1, 1, 1)
    return geo, rmin


def rank3(m):
    rows = [m & 7, m >> 3 & 7, m >> 6 & 7]
    return rank(rows)


def coset_has_rank(ext, cur, lo, hi):
    """does the coset (span(ext) minus span(cur)) contain a vector of
    3x3-rank in [lo, hi]?"""
    cur_r = rref(cur)
    def in_cur(v):
        for o in cur_r:
            p = o.bit_length() - 1
            if v >> p & 1:
                v ^= o
        return v == 0
    for code in range(1, 1 << len(ext)):
        v = 0
        for i, b in enumerate(ext):
            if code >> i & 1:
                v ^= b
        if v == 0 or in_cur(v):
            continue
        if lo <= rank3(v) <= hi:
            return True
    return False


def all_extensions(supp_el, cur):
    seen = set()
    for v in supp_el:
        r = rref(list(cur) + [v])
        if len(r) == len(cur):
            continue
        seen.add(r)
    return seen


def annihilator_free(u, d):
    r = rref(u)
    piv = [row.bit_length() - 1 for row in r]
    basis, free = [], []
    for f in range(d):
        if f in piv:
            continue
        phi = 1 << f
        for row, p in zip(r, piv):
            if row >> f & 1:
                phi |= 1 << p
        basis.append(phi)
        free.append(f)
    return basis, free


def elements(basis):
    out = []
    for code in range(1 << len(basis)):
        v = 0
        for i, b in enumerate(basis):
            if code >> i & 1:
                v ^= b
        out.append(v)
    return out


def dot(a, b):
    return bin(a & b).count("1") & 1


def support(dims, t, side, killed, d):
    """killed + span of the side's flattening columns, mapped back via the
    dual basis e_i = 1 << f_i of the annihilator basis"""
    da, db, dc = dims
    _, free = annihilator_free(killed, d)
    cols = []
    if side == 1:
        for b in range(db):
            for k in range(dc):
                cols.append(sum(((t[i][b] >> k) & 1) << i for i in range(da)))
    elif side == 2:
        for i in range(da):
            for k in range(dc):
                cols.append(sum(((t[i][j] >> k) & 1) << j for j in range(db)))
    else:
        for i in range(da):
            for j in range(db):
                cols.append(t[i][j])
    rows = list(killed)
    for y in cols:
        rows.append(sum(1 << f for i, f in enumerate(free) if y >> i & 1))
    return rref(rows)


def forced_extensions(dims, t, side, killed, d, phi):
    """the adversary's options: U + <v> for v in the support with phi.v = 1"""
    supp = support(dims, t, side, killed, d)
    ann, _ = annihilator_free(killed, d)
    assert phi != 0 and rref(list(ann) + [phi]) == rref(ann), "phi not in U^perp"
    assert any(dot(phi, sv) for sv in supp), "phi vanishes on the support: no product is forced"
    seen = set()
    for v in elements(supp):
        if dot(phi, v) != 1:
            continue
        r = rref(list(killed) + [v])
        if len(r) == len(killed):
            continue
        seen.add(r)
    return seen


def main(path):
    cert = json.load(open(path))
    n = cert["n"]
    d, t0 = matmul_tensor(n)
    nodes = {nd["key"]: nd for nd in cert["nodes"]}
    root = cert["root"]
    assert root in nodes, "root missing"
    checked = 0
    for k, nd in nodes.items():
        (u, v, x), rmin = parse_key(k)
        dims, t = quotient(d, t0, list(u), list(v), list(x))
        assert list(dims) == nd["dims"], f"dims mismatch at {k}"
        fl = flattenings(dims, t)
        assert fl == nd["leaf"], f"flattening mismatch at {k}: {fl} vs {nd['leaf']}"
        value = nd["value"]
        leaf_bound = max(fl)
        if cert.get("coset"):
            leaf_bound = max(leaf_bound, coset_bound(dims, t))
        if cert.get("koszul", 0) and nd["choice"] == 0 and value > leaf_bound:
            leaf_bound = max(leaf_bound, koszul_bound(dims, t, cert["koszul"]))
        if nd["choice"] == 0:
            assert value <= leaf_bound, f"leaf claim too strong at {k}: {value} > {leaf_bound}"
        elif nd["choice"] >= 4:
            # rank-profile split on side s with threshold m: EITHER some alive
            # product's side-s vector (original space) has rank in
            # [rmin_s, m] — kill it: ALL support cosets containing such a
            # representative must appear as B1 children (no functional) — OR
            # none does: the same geometry with rmin_s := m+1 (B2). The
            # claimed value must be <= min(1 + min B1 claims, B2 claim).
            assert max(fl) > 0, f"split on the zero tensor at {k}"
            side = nd["choice"] - 3
            m = nd["phi"]
            rs = rmin[side - 1]
            assert rs <= m <= 2, f"bad split threshold at {k}"
            cur = [u, v, x][side - 1]
            supp = support(dims, t, side, list(cur), d)
            kids = {}
            for ch in nd["b1"]:
                if isinstance(ch, str):
                    kids[ch] = (ch, None)
                else:
                    kids[ch["raw"]] = (ch.get("canon", ch["raw"]), ch.get("g"))
            b1_worst = None
            for e in all_extensions(elements(supp), list(cur)):
                if not coset_has_rank(list(e), list(cur), rs, m):
                    continue
                parts = [list(u), list(v), list(x)]
                parts[side - 1] = list(e)
                ck = "|".join(",".join(format(r, "x") for r in pp) for pp in parts)
                ck += "|" + ",".join(str(r) for r in rmin)
                assert ck in kids, f"missing B1 child {ck} at {k}"
                target, gel = kids[ck]
                assert target in nodes, f"B1 child node {target} missing at {k}"
                if gel is not None:
                    P, Q, R = gel
                    assert is_symmetry(n, P, Q, R), f"bad iso at {k}"
                    img = apply_sandwich(P, Q, R, (tuple(e) if side == 1 else u, tuple(e) if side == 2 else v, tuple(e) if side == 3 else x), d)
                    timg = parse_key(target)
                    assert img == timg[0] and timg[1] == rmin, f"B1 iso edge does not hold at {k}"
                else:
                    assert target == ck
                cv = nodes[target]["value"]
                b1_worst = cv if b1_worst is None else min(b1_worst, cv)
            r2 = list(rmin); r2[side - 1] = m + 1
            b2k = nd["b2"]
            assert b2k in nodes, f"B2 node missing at {k}"
            (bu, bv, bx), brm = parse_key(b2k)
            assert (bu, bv, bx) == (u, v, x) and list(brm) == r2, f"B2 key mismatch at {k}"
            b2v = nodes[b2k]["value"]
            bound = b2v if b1_worst is None else min(1 + b1_worst, b2v)
            assert value <= bound, f"split claim too strong at {k}: {value} > {bound}"
        else:
            assert max(fl) > 0, f"kill move on the zero tensor at {k} (no product to kill)"
            side = nd["choice"]
            cur = [u, v, x][side - 1]
            assert len(cur) < d, f"killing on an exhausted side at {k}"
            exts = forced_extensions(dims, t, side, list(cur), d, nd["phi"])
            # children are listed raw, optionally with an isomorphism to a
            # canonical node: child = g^-1(canon), g = (P, Q, R) a sandwich
            # element (verified to preserve the tensor)
            kids = {}
            for ch in nd["children"]:
                if isinstance(ch, str):
                    kids[ch] = (ch, None)
                else:
                    kids[ch["raw"]] = (ch.get("canon", ch["raw"]), ch.get("g"))
            worst = None
            for e in exts:
                if rmin[side - 1] > 1 and not coset_has_rank(list(e), list([u, v, x][side - 1]), rmin[side - 1], 3):
                    continue  # not a legal product coset under the rank constraint
                parts = [u, v, x]
                parts[side - 1] = e
                ck = "|".join(",".join(format(r, "x") for r in p) for p in parts)
                ck += "|" + ",".join(str(r) for r in rmin)
                assert ck in kids, f"missing child {ck} at {k}"
                target, gel = kids[ck]
                assert target in nodes, f"child node {target} missing at {k}"
                if gel is not None:
                    P, Q, R = gel
                    assert is_symmetry(n, P, Q, R), f"g = {gel} is not a symmetry of the tensor"
                    img = apply_sandwich(P, Q, R, parse_key(ck)[0], d)
                    timg = parse_key(target)
                    assert img == timg[0] and timg[1] == rmin, f"iso edge {ck} -> {target} does not hold"
                else:
                    assert target == ck
                cv = nodes[target]["value"]
                worst = cv if worst is None else min(worst, cv)
            assert value <= 1 + worst, f"kill claim too strong at {k}: {value} > 1 + {worst}"
        checked += 1
    print(f"VERIFIED: {checked} states replayed from scratch; rank_F2(<{n},{n},{n}>) >= {nodes[root]['value']}")


if __name__ == "__main__":
    main(sys.argv[1])
