#!/usr/bin/env python3
"""Independent checker for subgame certificates (substitution game over F_2).

  python3 matmul/r22/subgame_verify.py CERT.json

The certificate is a DAG of states (U, V, X) = killed subspaces of the
three sides of T = <n,n,n>, each with a claimed lower bound `value` on
the rank of the quotient tensor T/(U,V,X), and either
  choice 0 (leaf): value <= max flattening rank of T/(U,V,X), or
  choice s in {1,2,3} with functional phi: the tensor is NONZERO, phi
      lies in the annihilator of the killed subspace and does not vanish
      on the side's SUPPORT (the smallest subspace S with T' in S (x) ..),
      value <= 1 + min over the extensions U + <v>, v in S with phi.v = 1,
      of the child's claimed value, and every such child is present.
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


def parse_key(k):
    parts = k.split("|")
    return tuple(tuple(int(x, 16) for x in p.split(",")) if p else () for p in parts)


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
        u, v, x = parse_key(k)
        dims, t = quotient(d, t0, list(u), list(v), list(x))
        assert list(dims) == nd["dims"], f"dims mismatch at {k}"
        fl = flattenings(dims, t)
        assert fl == nd["leaf"], f"flattening mismatch at {k}: {fl} vs {nd['leaf']}"
        value = nd["value"]
        if nd["choice"] == 0:
            assert value <= max(fl), f"leaf claim too strong at {k}: {value} > {max(fl)}"
        else:
            assert max(fl) > 0, f"kill move on the zero tensor at {k} (no product to kill)"
            side = nd["choice"]
            cur = [u, v, x][side - 1]
            assert len(cur) < d, f"killing on an exhausted side at {k}"
            exts = forced_extensions(dims, t, side, list(cur), d, nd["phi"])
            child_keys = set(nd["children"])
            # every extension must appear as a child with a claimed value
            worst = None
            for e in exts:
                parts = [u, v, x]
                parts[side - 1] = e
                ck = "|".join(",".join(format(r, "x") for r in p) for p in parts)
                assert ck in child_keys and ck in nodes, f"missing child {ck} at {k}"
                cv = nodes[ck]["value"]
                worst = cv if worst is None else min(worst, cv)
            assert value <= 1 + worst, f"kill claim too strong at {k}: {value} > 1 + {worst}"
        checked += 1
    print(f"VERIFIED: {checked} states replayed from scratch; rank_F2(<{n},{n},{n}>) >= {nodes[root]['value']}")


if __name__ == "__main__":
    main(sys.argv[1])
