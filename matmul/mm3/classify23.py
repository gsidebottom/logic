#!/usr/bin/env python3
"""Classify rank-23 3x3 decompositions from flip23 --descend against the Heule-Kauers-Seidl
database by the family string, the rank invariants its directories are named by:
x terms count the 69 factor matrices by rank, y terms count the 23 products by the sum of
their three factor ranks, z terms list the three per-slot rank totals, e.g.
'14x2+55x+4y6+2y4+17y3+2z28+z27'.  Ranks are over Q (our decompositions have
Z[1/2] coefficients; the database's signed lifts are read from dbcache/schemes.tgz) and are
symmetry invariants, so a family string absent from the database certifies a class the
database does not contain.  The database names its directories by ranks over F2 (recomputed
here over F2 they agree for all but 4 of 17,376), so they are compared only as a sanity check;
the classification compares Q-strings with Q-strings.  With --hb, Hell's Bells' ternary
schemes (Martensson et al., ePrint 2026/1688) count as known too; --known-out writes every
known family string, one per line, for flip23 --descend --known-families.

  classify23.py [--hb DIR] [--known-out FILE] DUMP ... (or @FILE listing them)
  (flip23 dumps: lines '([n0..n8], e) | (...) | (...)')
"""
import ast
import os
import sys
import tarfile
from collections import Counter, defaultdict
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
DB = os.path.join(HERE, "..", "dbcache", "schemes.tgz")


def rank3(m):
    """rank over Q of a 3x3 matrix given as 9 numbers, row-major"""
    rows = [[Fraction(m[3 * r + c]) for c in range(3)] for r in range(3)]
    rank = 0
    for c in range(3):
        p = next((k for k in range(rank, 3) if rows[k][c] != 0), None)
        if p is None:
            continue
        rows[rank], rows[p] = rows[p], rows[rank]
        for k in range(3):
            if k != rank and rows[k][c] != 0:
                f = rows[k][c] / rows[rank][c]
                rows[k] = [x - f * y for x, y in zip(rows[k], rows[rank])]
        rank += 1
    return rank


def family(scheme):
    """scheme: 23 (a, b, c) factor 9-tuples -> the database's family string"""
    ranks = [tuple(rank3(f) for f in prod) for prod in scheme]
    term = lambda count, var, exp: (str(count) if count > 1 else "") + var + exp
    xs = Counter(r for t in ranks for r in t)
    ys = Counter(sum(t) for t in ranks)
    zs = Counter(sum(t[s] for t in ranks) for s in range(3))
    parts = [term(xs[k], "x", str(k) if k > 1 else "") for k in sorted(xs, reverse=True)]
    parts += [term(ys[k], "y", str(k)) for k in sorted(ys, reverse=True)]
    parts += [term(zs[k], "z", str(k)) for k in sorted(zs, reverse=True)]
    return "+".join(parts)


def parse_tab(text):
    """a database .tab: per product three lines 'a row | b row | c row', blocks split by dashes"""
    blocks, cur = [], []
    for ln in text.splitlines():
        if not ln.strip():
            continue
        if set(ln.strip()) <= set("-+"):
            blocks.append(cur)
            cur = []
            continue
        cur.append([[int(x) for x in part.split()] for part in ln.split("|")])
    if cur:
        blocks.append(cur)
    return [tuple([v for row in blk for v in row[s]] for s in range(3)) for blk in blocks]


def parse_hb(path):
    """a Hell's Bells file: three blocks of 9 rows x 23 columns split by '#' lines; column m
    of each block holds product m's factor, entries row-major"""
    blocks, cur = [], []
    for ln in open(path):
        ln = ln.strip()
        if ln == "#":
            blocks.append(cur)
            cur = []
        elif ln:
            cur.append([int(v) for v in ln.split()])
    if cur:
        blocks.append(cur)
    assert len(blocks) == 3 and all(len(b) == 9 for b in blocks), path
    return [tuple([blocks[s][e][m] for e in range(9)] for s in range(3)) for m in range(23)]


def parse_dump(path):
    scheme = []
    for ln in open(path):
        if ln.strip():
            parts = [ast.literal_eval(p.strip()) for p in ln.split("|")]
            scheme.append(tuple([Fraction(n) * Fraction(2) ** e for n in nums] for nums, e in parts))
    return scheme


def main():
    args = sys.argv[1:]
    hb_dir = known_out = None
    if "--hb" in args:
        i = args.index("--hb")
        hb_dir = args[i + 1]
        del args[i:i + 2]
    if "--known-out" in args:
        i = args.index("--known-out")
        known_out = args[i + 1]
        del args[i:i + 2]
    db = defaultdict(int)
    mismatch = 0
    with tarfile.open(DB, "r:gz") as tf:
        for mem in tf:
            if not mem.name.endswith(".tab"):
                continue
            s = parse_tab(tf.extractfile(mem).read().decode())
            assert len(s) == 23, mem.name
            fam = family(s)
            db[fam] += 1
            if fam != mem.name.split("/")[-2]:
                mismatch += 1
    print(f"database: {sum(db.values())} schemes in {len(db)} family strings; "
          f"{mismatch} disagree with their (F2-rank) directory name")
    hb = defaultdict(int)
    if hb_dir:
        for name in sorted(os.listdir(hb_dir)):
            if name.endswith(".txt"):
                hb[family(parse_hb(os.path.join(hb_dir, name)))] += 1
        print(f"Hell's Bells: {sum(hb.values())} schemes in {len(hb)} family strings, "
              f"{len(set(hb) - set(db))} of them not in the database")
    known = set(db) | set(hb)
    if known_out:
        with open(known_out, "w") as f:
            f.write("".join(k + "\n" for k in sorted(known)))
        print(f"wrote {len(known)} known family strings to {known_out}")
    paths = [q.strip() for a in args for q in (open(a[1:]) if a.startswith("@") else [a]) if q.strip()]
    ours = defaultdict(list)
    for path in paths:
        s = parse_dump(path)
        assert len(s) == 23, path
        ours[family(s)].append(path)
    n = sum(len(v) for v in ours.values())
    new = {f: v for f, v in ours.items() if f not in known}
    print(f"ours: {n} decompositions in {len(ours)} family strings; "
          f"{len(ours) - len(new)} strings are known, {len(new)} are not")
    for f, v in sorted(ours.items(), key=lambda kv: -len(kv[1])):
        tag = "NEW" if f in new else (f"db {db[f]}" if f in db else f"hb {hb[f]}")
        runs = Counter(os.path.basename(os.path.dirname(p)) for p in v)
        print(f"  {len(v):4d}  {f:44s} {tag:8s} {dict(runs)}")


if __name__ == "__main__":
    main()
