#!/usr/bin/env python3
"""
Generality sweep — does the ONE exact-Gomory separator (cp_gmi) crack the
families that currently each need a separate hand-written detector?

The Rust detectors are per-family and structure-exact: cook_pbp (PHP / RoundRobin
/ clique-coloring / mutilated-chessboard), xor_gauss + parity_pbp (parity/XOR).
cp_gmi is ONE algorithm (exact rational simplex → Gomory cut → CG emission) with
no per-family pattern-matching.  This sweep generates small UNSAT instances of
several families and, per instance, reports:
  * UNSAT confirmed (cadical/the Rust cdcl backend),
  * what the Rust cook detector matches (--emit-cook-pbp), and whether default
    `sat` (xor_gauss + cook portfolio) dispatches it,
  * whether cp_gmi finds a veripb-VERIFIED proof, and at what cut cost.

Usage:  cp_sweep.py [--max-secs S] [--only FAMILY]
"""
from __future__ import annotations
import argparse, os, subprocess, sys, tempfile, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cp_search as cp                                    # noqa: E402
import cp_lp                                              # noqa: E402
import cp_gmi                                             # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SAT = os.path.join(ROOT, "target", "release", "sat")


# ── family generators (small UNSAT instances) ───────────────────────────────

def _write(path, nvars, clauses):
    with open(path, "w") as f:
        f.write(f"p cnf {nvars} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(map(str, c)) + " 0\n")
    return path


def coloring_cnf(edges, nverts, k, path):
    """Proper k-coloring of graph (nverts, edges).  Exactly-one color per vertex,
    adjacent vertices differ.  UNSAT iff chromatic number > k."""
    def cv(v, c):
        return (v - 1) * k + c + 1
    cl = []
    for v in range(1, nverts + 1):
        cl.append([cv(v, c) for c in range(k)])                 # >= 1 color
        for a in range(k):
            for b in range(a + 1, k):
                cl.append([-cv(v, a), -cv(v, b)])               # <= 1 color
    for (u, v) in edges:
        for c in range(k):
            cl.append([-cv(u, c), -cv(v, c)])                   # adjacent differ
    return _write(path, nverts * k, cl)


def odd_cycle_color(n, path, k=2):
    edges = [(i, i % n + 1) for i in range(1, n + 1)]           # C_n
    return coloring_cnf(edges, n, k, path)


def tseitin_cycle(n, path):
    """Tseitin parity on cycle C_n: edge var i joins vertices i,i+1.  Vertex j
    parity  e_{j-1} ⊕ e_j = τ_j  with τ_1=1, rest 0 (Στ odd) → UNSAT."""
    def xor2(a, b, rhs):
        return [[a, b], [-a, -b]] if rhs else [[a, -b], [-a, b]]
    cl = []
    for j in range(1, n + 1):
        e_prev = (j - 2) % n + 1
        cl += xor2(e_prev, j, 1 if j == 1 else 0)
    return _write(path, n, cl)


def mutilated_cnf(R, C, path):
    """Domino exact-cover of an R×C grid minus two same-colour opposite corners.
    Var per domino (edge between adjacent kept cells); each kept cell covered by
    exactly one domino.  UNSAT by colour imbalance."""
    removed = {(0, 0), (R - 1, C - 1)}
    assert (0 + 0) % 2 == (R - 1 + C - 1) % 2, "corners must share colour"
    cells = [(i, j) for i in range(R) for j in range(C) if (i, j) not in removed]
    cset = set(cells)
    eid, edges = {}, []
    for (i, j) in cells:
        for (di, dj) in ((0, 1), (1, 0)):
            nb = (i + di, j + dj)
            if nb in cset:
                edges.append(((i, j), nb))
                eid[((i, j), nb)] = len(edges)
    inc = {c: [] for c in cells}
    for ((a, b)), e in eid.items():
        inc[a].append(e)
        inc[b].append(e)
    cl = []
    for c in cells:
        es = inc[c]
        cl.append(es[:])                                        # >= 1 domino
        for x in range(len(es)):
            for y in range(x + 1, len(es)):
                cl.append([-es[x], -es[y]])                     # <= 1 domino
    return _write(path, len(edges), cl)


# ── probes ──────────────────────────────────────────────────────────────────

def _run_sat(cnf, extra=()):
    try:
        with open(cnf) as fh:
            data = fh.read()
        r = subprocess.run([SAT, *extra], input=data, capture_output=True,
                           text=True, timeout=60)
        return r.stdout + r.stderr, r.returncode
    except Exception as e:
        return f"(error {e})", -1


def detector_status(cnf):
    """Per-family structural detectors: does cook_pbp match the shape, and does
    xor_gauss solve / partially-recover / miss?  Plus the UNSAT sanity verdict."""
    out, _ = _run_sat(cnf, ["--emit-cook-pbp", "/dev/null"])
    if "no matching shape" in out:
        cook = "no-match"
    else:
        cook = next((ln.split("detected", 1)[1].split(" in ")[0].strip()
                     for ln in out.splitlines()
                     if "detected" in ln and "no matching" not in ln), "?")
    out2, _ = _run_sat(cnf)                                     # default eff + xor_gauss
    if "XOR system is inconsistent" in out2:
        xg = "solves"
    elif "mixed" in out2:
        xg = "partial"
    elif "recovered" in out2:
        xg = "partial"
    else:
        xg = "miss"
    verdict = "UNSAT" if "s UNSATISFIABLE" in out2 else (
        "SAT" if "s SATISFIABLE" in out2 else "?")
    return cook, xg, verdict


def gmi_status(cnf, max_secs):
    inputs = cp.read_cnf(cnf)
    nvars = max((v for c in inputs for v in c.coef), default=0)
    t0 = time.time()
    cons, refuted, recipes = cp_gmi.gmi_loop(inputs, nvars, max_secs=max_secs)
    if not refuted:
        return f"no-refute ({len(recipes)} cuts, {time.time()-t0:.1f}s)", False
    mult = cp_lp.farkas_refute(cons)
    if not mult:
        return f"Farkas-fail ({len(recipes)} cuts)", False
    pbp = cnf + ".gmi.pbp"
    cp_gmi.emit_gmi(len(inputs), recipes, mult, pbp)
    ok, _ = cp.verify(cnf, pbp)
    dt = time.time() - t0
    return (f"{len(recipes)} cuts / {dt:.1f}s / "
            f"{'VERIFIED' if ok else 'veripb-FAIL'}"), ok


def sweep(max_secs=60, only=None):
    td = tempfile.mkdtemp(prefix="gmi_sweep_")
    insts = []
    insts += [(f"parity(Tseitin C{n})", "parity", tseitin_cycle(n,
              os.path.join(td, f"tseitin_c{n}.cnf"))) for n in (3, 5, 7, 9)]
    insts += [(f"coloring(C{n}, 2-col)", "coloring", odd_cycle_color(n,
              os.path.join(td, f"color_c{n}.cnf"))) for n in (5, 7, 9)]
    insts += [(f"mutilated({R}x{C})", "mutilated", mutilated_cnf(R, C,
              os.path.join(td, f"mut_{R}x{C}.cnf")))
              for (R, C) in ((4, 4), (4, 6))]
    insts += [("PHP-4-3 (baseline)", "php", cp_gmi.php_cnf(4, 3,
              os.path.join(td, "php_4_3.cnf")))]
    if only:
        insts = [i for i in insts if i[1] == only]

    have_sat = os.path.exists(SAT)
    print(f"{'instance':22} {'vars':>4} {'cook_pbp':22} {'xor_gauss':9} "
          f"{'GMI (one engine)':30}")
    print("-" * 92)
    for name, fam, cnf in insts:
        nv = int(open(cnf).readline().split()[2])
        if have_sat:
            cook, xg, verdict = detector_status(cnf)
            assert verdict == "UNSAT", f"{name} not UNSAT ({verdict})!"
        else:
            cook, xg = "(no sat)", "-"
        gmi, ok = gmi_status(cnf, max_secs)
        print(f"{name:22} {nv:>4} {cook:22} {xg:9} {gmi:30}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-secs", type=float, default=60)
    ap.add_argument("--only")
    args = ap.parse_args()
    sweep(args.max_secs, args.only)


if __name__ == "__main__":
    main()
