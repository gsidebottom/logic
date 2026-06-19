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


def slack(p: PB) -> int:
    """LP slack: max achievable LHS minus rhs.  < 0 ⇒ the constraint alone is
    infeasible; 0>=1 has slack -1.  The search minimizes this toward a
    contradiction (a tighter LP relaxation is closer to a refutation)."""
    return sum(c for c in p.coef.values() if c > 0) - p.rhs


def divisors_for(p: PB):
    """Useful CG divisors: the distinct positive literal-coefficients (the
    rounding that turns Σ k·ℓ ≥ b into a cardinality), capped."""
    lit, _ = to_literal_normalized(p)
    ds = sorted({c for c in lit.values() if c >= 2})
    return ds[:6]


FEAT_NAMES = ["slack", "nvars", "rhs", "maxcoef", "sumcoef", "ncoefdistinct",
              "tightness", "from_divide"]


def feats(p: PB):
    """Cheap per-constraint features for the learned priority (step 2a)."""
    lit, r = to_literal_normalized(p)
    cs = list(lit.values()) or [0]
    pos = sum(c for c in cs if c > 0)
    return [float(slack(p)), float(p.nvars()), float(r), float(max(cs)),
            float(sum(cs)), float(len(set(cs))), r / (pos + 1.0),
            1.0 if p.deriv[0] == "div" else 0.0]


def ancestors(contra: PB):
    """Set of id()s of all constraints (incl. inputs) the proof actually uses."""
    seen = set()
    def walk(p):
        if id(p) in seen:
            return
        seen.add(id(p))
        d = p.deriv
        if d[0] == "addsc":
            walk(d[1]); walk(d[3])
        elif d[0] == "div":
            walk(d[1])
    walk(contra)
    return seen


def default_prio(p):
    return (slack(p), p.nvars())


def search(inputs, max_nodes=20000, allow_divide=False, same_sign=True,
           max_size=64, priority_fn=None, record=False,
           max_pool=0, max_secs=0.0):
    """Best-first cutting-planes search for 0>=1.  Actions between the current
    constraint and a pool constraint sharing a variable: Fourier–Motzkin
    elimination (opposite sign) and, with same_sign, cardinality-building
    summation (same sign); each result optionally CG-divided.  Default heuristic
    = (slack, nvars); a learned `priority_fn(pb)->sortable` overrides it.  With
    record=True, returns the list of expanded constraints (for imitation data).

    Hard bounds (a bad priority must never run away): max_nodes, max_pool
    constraints, max_secs wall-time (0 = off)."""
    import time as _t
    t0 = _t.time()

    if priority_fn is None:
        prio = default_prio                       # default path: identical to baseline
    else:
        def prio(p):                              # learned path: NaN/inf-guarded
            try:
                k = priority_fn(p)
                v = k[0] if isinstance(k, tuple) else k
                if v != v or v in (float("inf"), float("-inf")):
                    return default_prio(p)
                return k
            except Exception:
                return default_prio(p)
    pool = list(inputs)
    seen = {p.key() for p in pool}

    def push_heap(h, p):
        heapq.heappush(h, Item(prio(p), p))
    h = []
    for p in pool:
        push_heap(h, p)
    nodes = 0
    popped = [] if record else None
    while h and nodes < max_nodes:
        if (max_pool and len(pool) >= max_pool) or \
           (max_secs and _t.time() - t0 > max_secs):
            break                                  # bound (max_secs is the real
                                                   # runaway guard; pool off by default)
        cur = heapq.heappop(h).pb
        nodes += 1
        if record:
            popped.append(cur)
        if cur.is_contradiction():
            return cur, nodes, popped
        for v, cv in list(cur.coef.items()):
            for other in pool:
                if other is cur:
                    continue
                cw = other.coef.get(v, 0)
                if cw == 0:
                    continue
                opp = (cv > 0) != (cw > 0)
                g = math.gcd(abs(cv), abs(cw))
                if opp:                                  # FM elimination
                    combos = [(abs(cw) // g, abs(cv) // g)]
                elif same_sign:                          # cardinality-building sum
                    combos = [(1, 1)]
                else:
                    continue
                for ma, mb in combos:
                    new = add_scaled(cur, ma, other, mb).norm()
                    cand = [new]
                    if allow_divide and new.coef:
                        for d in divisors_for(new):
                            cand.append(divide(new, d))
                    for nc in cand:
                        if nc.is_contradiction():
                            if record:
                                popped.append(nc)
                            return nc, nodes, popped
                        k = nc.key()
                        if k not in seen and nc.nvars() <= max_size:
                            seen.add(k); pool.append(nc); push_heap(h, nc)
    return None, nodes, popped


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


def prove_cnf(cnf_path, max_nodes, allow_divide, same_sign=True, max_size=64):
    inputs = read_cnf(cnf_path)
    import time as _t
    t0 = _t.time()
    contra, nodes, _ = search(inputs, max_nodes, allow_divide, same_sign, max_size)
    dt = _t.time() - t0
    if not contra:
        print(f"  no proof found ({nodes} nodes, {dt:.1f}s, divide={allow_divide}, "
              f"same_sign={same_sign})")
        return False
    pbp = cnf_path + ".pbp"
    nd = emit_pbp(len(inputs), contra, pbp)
    ok, tail = verify(cnf_path, pbp)
    print(f"  proof: {nd} derivations, {nodes} nodes, {dt:.1f}s, "
          f"same_sign={same_sign}  ->  veripb: {'VERIFIED' if ok else 'FAILED '+str(tail)}")
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
    ap.add_argument("--no-same-sign", action="store_true",
                    help="disable cardinality-building same-sign summation (FM only)")
    ap.add_argument("--max-size", type=int, default=64)
    args = ap.parse_args()
    if args.selftest:
        sys.exit(0 if selftest() else 1)
    if args.cnf:
        prove_cnf(args.cnf, args.max_nodes, args.allow_divide,
                  same_sign=not args.no_same_sign, max_size=args.max_size)


if __name__ == "__main__":
    main()
