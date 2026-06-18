#!/usr/bin/env python3
"""
Phase 3 — cutting-planes proof-SEARCH environment (MCGS foundation).

A node is a set of pseudo-Boolean constraints; actions derive a new constraint
via the VeriPB `pol` (reverse-polish cutting-planes) rules — add, multiply by a
positive constant, divide with ceiling rounding (the Chvátal–Gomory cut). A
terminal is the contradiction 0 >= 1. The derivation is emitted as a `.pbp`
proof and checked by VeriPB, so any proof the search finds is independently
verified (reward = a verified, compact proof).

Representation: signed-variable form  Σ c_v·x_v >= rhs  (c_v ∈ ℤ) — clean for
add/multiply; converted to literal-normalized (coeffs ≥ 0) for divide and for
contradiction detection.

This module is the env + a baseline (unguided best-first) search, to de-risk
whether search can construct verified CP proofs before adding a learned policy.

Usage:  cp_search.py --selftest
        cp_search.py --cnf foo.cnf [--max-nodes N --allow-divide]
"""
from __future__ import annotations
import argparse, math, os, subprocess, sys, tempfile, heapq
from dataclasses import dataclass, field

VERIPB = os.path.expanduser("~/.cargo/bin/veripb")


@dataclass
class PB:
    """Σ coef[v]·x_v >= rhs  (signed-variable form)."""
    coef: dict          # var(int>0) -> int coefficient (may be negative)
    rhs: int
    deriv: tuple = ("input", -1)   # provenance for proof emission
    cid: int = -1                   # VeriPB constraint id, assigned at emit

    def norm(self):
        self.coef = {v: c for v, c in self.coef.items() if c != 0}
        return self

    @staticmethod
    def from_clause(lits, idx):
        coef, rhs = {}, 1
        for L in lits:
            v = abs(L)
            if L > 0:
                coef[v] = coef.get(v, 0) + 1
            else:                       # ~x = 1 - x : subtract x, drop 1 from rhs
                coef[v] = coef.get(v, 0) - 1
                rhs -= 1
        return PB(coef, rhs, ("input", idx)).norm()

    def is_contradiction(self):
        return not self.coef and self.rhs >= 1

    def key(self):
        return (tuple(sorted(self.coef.items())), self.rhs)

    def nvars(self):
        return len(self.coef)


def add_scaled(a: PB, ma: int, b: PB, mb: int) -> PB:
    coef = {}
    for v, c in a.coef.items():
        coef[v] = coef.get(v, 0) + ma * c
    for v, c in b.coef.items():
        coef[v] = coef.get(v, 0) + mb * c
    return PB(coef, ma * a.rhs + mb * b.rhs, ("addsc", a, ma, b, mb)).norm()


def to_literal_normalized(p: PB):
    """Return (lit_coef, rhs') with all coeffs >= 0.  lit = ('x',v) or ('~',v)."""
    lit, rhs = {}, p.rhs
    for v, c in p.coef.items():
        if c > 0:
            lit[('x', v)] = c
        elif c < 0:                     # c·x = |c|·~x - |c| ; move -|c| to rhs
            lit[('~', v)] = -c
            rhs += -c
    return lit, rhs


def divide(p: PB, d: int) -> PB:
    """Chvátal–Gomory cut: in literal-normalized form divide by d, round up."""
    lit, rhs = to_literal_normalized(p)
    coef = {}
    for (s, v), c in lit.items():
        cc = math.ceil(c / d)
        coef[v] = coef.get(v, 0) + (cc if s == 'x' else -cc)
        if s == '~':
            # ceil(c/d)·~x = ceil(c/d)·(1-x) ; constant ceil moves to rhs
            pass
    # rebuild rhs: ceil(rhs/d) in literal form, then convert ~ constants back
    newrhs = math.ceil(rhs / d)
    for (s, v), c in lit.items():
        if s == '~':
            newrhs -= math.ceil(c / d)
    return PB(coef, newrhs, ("div", p, d)).norm()


# ── search ────────────────────────────────────────────────────────────────

@dataclass(order=True)
class Item:
    prio: tuple
    pb: PB = field(compare=False)


def search(inputs, max_nodes=20000, allow_divide=False, divide_consts=(2, 3)):
    """Best-first cutting-planes search for 0>=1.  Actions: eliminate a shared
    variable between two constraints (Fourier–Motzkin step), optionally divide."""
    pool = list(inputs)
    seen = {p.key() for p in pool}
    # index: var -> list of (pool_idx, coef sign)
    def push_heap(h, p):
        heapq.heappush(h, Item((p.nvars(), -p.rhs), p))
    h = []
    for p in pool:
        push_heap(h, p)
    nodes = 0
    while h and nodes < max_nodes:
        cur = heapq.heappop(h).pb
        nodes += 1
        if cur.is_contradiction():
            return cur, nodes
        # try to eliminate each var of `cur` against a pool constraint of opposite sign
        for v, cv in list(cur.coef.items()):
            for other in pool:
                if other is cur:
                    continue
                cw = other.coef.get(v, 0)
                if cw == 0 or (cv > 0) == (cw > 0):
                    continue            # need opposite signs on v to cancel
                g = math.gcd(abs(cv), abs(cw))
                ma, mb = abs(cw) // g, abs(cv) // g
                new = add_scaled(cur, ma, other, mb).norm()
                cand = [new]
                if allow_divide and new.coef:
                    g2 = math.gcd(*[abs(c) for c in new.coef.values()], abs(new.rhs) if new.rhs else 0) if new.coef else 1
                    for d in divide_consts:
                        cand.append(divide(new, d))
                for nc in cand:
                    if nc.is_contradiction():
                        return nc, nodes
                    k = nc.key()
                    if k not in seen and nc.nvars() <= max(cur.nvars(), 1) + 1:
                        seen.add(k); pool.append(nc); push_heap(h, nc)
    return None, nodes


# ── proof emission + verification ───────────────────────────────────────────

def collect(contra):
    """Topologically collect the derived constraints on the path to `contra`."""
    order, visited = [], set()
    def walk(p):
        if id(p) in visited:
            return
        visited.add(id(p))
        d = p.deriv
        if d[0] == "addsc":
            walk(d[1]); walk(d[3])
        elif d[0] == "div":
            walk(d[1])
        if d[0] != "input":
            order.append(p)
    walk(contra)
    return order


def emit_pbp(n_inputs, contra, path):
    derived = collect(contra)
    for i, p in enumerate(derived):
        p.cid = n_inputs + 1 + i
    lines = ["pseudo-Boolean proof version 3.0", f"f {n_inputs};"]
    for p in derived:
        d = p.deriv
        if d[0] == "addsc":
            _, a, ma, b, mb = d
            ia = a.cid if a.deriv[0] != "input" else a.deriv[1] + 1
            ib = b.cid if b.deriv[0] != "input" else b.deriv[1] + 1
            lines.append(f"pol {ia} {ma} * {ib} {mb} * + ;")
        elif d[0] == "div":
            _, a, dd = d
            ia = a.cid if a.deriv[0] != "input" else a.deriv[1] + 1
            lines.append(f"pol {ia} {dd} d ;")
    lines += ["output NONE;", "conclusion UNSAT : -1;", "end pseudo-Boolean proof;"]
    open(path, "w").write("\n".join(lines) + "\n")
    return len(derived)


def verify(cnf_path, pbp_path):
    r = subprocess.run([VERIPB, cnf_path, pbp_path], capture_output=True, text=True)
    return "VERIFIED UNSATISFIABLE" in r.stdout, r.stdout.strip().splitlines()[-1:]


def read_cnf(path):
    inputs, idx = [], 0
    for ln in open(path):
        ln = ln.strip()
        if not ln or ln[0] in "pc%":
            continue
        lits = [int(t) for t in ln.split() if t != "0"]
        if lits:
            inputs.append(PB.from_clause(lits, idx)); idx += 1
    return inputs


def prove_cnf(cnf_path, max_nodes, allow_divide):
    inputs = read_cnf(cnf_path)
    contra, nodes = search(inputs, max_nodes, allow_divide)
    if not contra:
        print(f"  no proof found ({nodes} nodes, divide={allow_divide})")
        return False
    pbp = cnf_path + ".pbp"
    nd = emit_pbp(len(inputs), contra, pbp)
    ok, tail = verify(cnf_path, pbp)
    print(f"  proof: {nd} derivations, {nodes} nodes searched, divide={allow_divide}"
          f"  ->  veripb: {'VERIFIED' if ok else 'FAILED '+str(tail)}")
    return ok


# ── self-tests ──────────────────────────────────────────────────────────────

def selftest():
    td = tempfile.mkdtemp(prefix="cp_")
    cases = {
        "trivial": "p cnf 1 2\n1 0\n-1 0\n",                       # x, ~x
        "lp_infeasible": "p cnf 2 3\n1 2 0\n1 -2 0\n-1 0\n",       # needs multiply
    }
    allok = True
    for name, cnf in cases.items():
        path = os.path.join(td, name + ".cnf"); open(path, "w").write(cnf)
        print(f"[{name}]")
        allok &= prove_cnf(path, 5000, allow_divide=True)
    print("SELFTEST", "PASS" if allok else "FAIL")
    return allok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--cnf")
    ap.add_argument("--max-nodes", type=int, default=20000)
    ap.add_argument("--allow-divide", action="store_true")
    args = ap.parse_args()
    if args.selftest:
        sys.exit(0 if selftest() else 1)
    if args.cnf:
        prove_cnf(args.cnf, args.max_nodes, args.allow_divide)


if __name__ == "__main__":
    main()
