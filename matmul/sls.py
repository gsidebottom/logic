#!/usr/bin/env python3
"""Native-ANF local search prototype for Brent equations mod 2.

State = the real scheme bits only (no Tseitin aux). Each Brent equation is
XOR of r monomials (AND of 3 vars) = rhs. Flipping var v toggles equation e
iff v occurs in a monomial of e whose other two vars are currently 1 --
incremental make/break is O(#occurrences of v) = O(r * n^2 / ...) tiny.

WalkSAT/SKC-style: pick a random violated equation; among vars whose flip
would toggle it (monomial partners both true), flip a freebie (break 0) if
one exists, else with prob NOISE a random var of the equation, else the
min-break toggling var.

Usage: python3 matmul/sls.py n1 n2 n3 r [--seconds S] [--noise P] [--seed K]
"""
import sys
import time
import random
from brent import brent_equations, var_counts, verify_bits


def build(n1, n2, n3, r):
    eqs = brent_equations(n1, n2, n3, r)
    nv = sum(var_counts(n1, n2, n3, r))
    # adjacency: var -> list of (eq, partner1, partner2)
    adj = [[] for _ in range(nv)]
    eq_vars = []  # per eq: deduped var list (for noise moves)
    for e, (mons, _rhs) in enumerate(eqs):
        vs = set()
        for va, vb, vg in mons:
            adj[va].append((e, vb, vg))
            adj[vb].append((e, va, vg))
            adj[vg].append((e, va, vb))
            vs.update((va, vb, vg))
        eq_vars.append(list(vs))
    rhs = [rh for _, rh in eqs]
    mons_per_eq = [mons for mons, _ in eqs]
    return nv, adj, eq_vars, rhs, mons_per_eq


def random_pairing(n, r, rng):
    """Heule et al. method 1: assign the 27 type-3 terms (a,b,d) to products
    so 4 products hold 2 terms (differing in ALL coordinates) and r-4-... the
    rest hold 1 (needs r products with 27 = (r-19)*2 + ... for r=23: 4 pairs +
    19 singles). Returns list of frozen (var,1) assignments."""
    terms = [(a, b, d) for a in range(n) for b in range(n) for d in range(n)]
    npairs = n ** 3 - r  # 27-23=4 pairs (2 terms each), rest singletons
    assert npairs >= 0
    for _try in range(10000):
        rng.shuffle(terms)
        pairs, used = [], [False] * len(terms)
        for i in range(len(terms)):
            if len(pairs) == npairs:
                break
            if used[i]:
                continue
            for j in range(i + 1, len(terms)):
                if used[j]:
                    continue
                t, u = terms[i], terms[j]
                if t[0] != u[0] and t[1] != u[1] and t[2] != u[2]:
                    pairs.append((t, u))
                    used[i] = used[j] = True
                    break
        if len(pairs) == npairs:
            singles = [terms[i] for i in range(len(terms)) if not used[i]]
            assert len(pairs) * 2 + len(singles) == n ** 3
            groups = [list(p) for p in pairs] + [[s] for s in singles]
            assert len(groups) == r
            return groups
    raise RuntimeError("no pairing found")


def pairing_units(groups, n1, n2, n3, r):
    """Frozen var=1 assignments for a pairing: term (a,b,d) in product m sets
    alpha[m][a,b], beta[m][b,d], gamma[m][a,d]."""
    na, nb, _ = var_counts(n1, n2, n3, r)
    frozen = {}
    for m, terms in enumerate(groups):
        for (a, b, d) in terms:
            frozen[m * n1 * n2 + a * n2 + b] = 1
            frozen[na + m * n2 * n3 + b * n3 + d] = 1
            frozen[na + nb + m * n1 * n3 + a * n3 + d] = 1
    return frozen


class Sls:
    def __init__(self, n1, n2, n3, r, rng):
        self.dims = (n1, n2, n3, r)
        self.nv, self.adj, self.eq_vars, self.rhs, self.mons = build(
            n1, n2, n3, r)
        self.rng = rng
        self.flips = 0
        self.frozen = {}

    def init_random(self, density=0.5):
        rng = self.rng
        self.bits = [1 if rng.random() < density else 0
                     for _ in range(self.nv)]
        for v, b in self.frozen.items():
            self.bits[v] = b
        self._recompute()

    def _recompute(self):
        bits = self.bits
        self.viol = []
        ne = len(self.rhs)
        self.par = [0] * ne
        for e in range(ne):
            acc = 0
            for va, vb, vg in self.mons[e]:
                acc ^= bits[va] & bits[vb] & bits[vg]
            self.par[e] = acc
        # unsat set with O(1) add/remove/sample
        self.unsat = [e for e in range(ne) if self.par[e] != self.rhs[e]]
        self.pos = [-1] * ne
        for i, e in enumerate(self.unsat):
            self.pos[e] = i

    def _toggle_eq(self, e):
        self.par[e] ^= 1
        if self.par[e] != self.rhs[e]:            # became unsat
            self.pos[e] = len(self.unsat)
            self.unsat.append(e)
        else:                                     # became sat: swap-remove
            i = self.pos[e]
            last = self.unsat[-1]
            self.unsat[i] = last
            self.pos[last] = i
            self.unsat.pop()
            self.pos[e] = -1

    def flip(self, v):
        bits = self.bits
        bits[v] ^= 1
        for e, p1, p2 in self.adj[v]:
            if bits[p1] & bits[p2]:
                self._toggle_eq(e)
        self.flips += 1

    def break_count(self, v):
        bits, par, rhs = self.bits, self.par, self.rhs
        br = 0
        for e, p1, p2 in self.adj[v]:
            if bits[p1] & bits[p2] and par[e] == rhs[e]:
                br += 1
        return br

    def step(self, noise):
        rng = self.rng
        e = self.unsat[rng.randrange(len(self.unsat))]
        bits, frz = self.bits, self.frozen
        # toggling candidates: var in a monomial of e with both partners true
        cands = []
        for va, vb, vg in self.mons[e]:
            if bits[vb] & bits[vg] and va not in frz:
                cands.append(va)
            if bits[va] & bits[vg] and vb not in frz:
                cands.append(vb)
            if bits[va] & bits[vb] and vg not in frz:
                cands.append(vg)
        if not cands or rng.random() < noise:
            free = [v for v in self.eq_vars[e] if v not in frz]
            if free:
                self.flip(free[rng.randrange(len(free))])
            return
        best, bestbr = None, None
        for v in cands:
            br = self.break_count(v)
            if br == 0:
                self.flip(v)
                return
            if bestbr is None or br < bestbr:
                best, bestbr = v, br
        self.flip(best)

    def run(self, seconds, noise, report=5.0):
        t0 = time.time()
        best = len(self.unsat)
        nextrep = report
        while self.unsat:
            self.step(noise)
            if len(self.unsat) < best:
                best = len(self.unsat)
            if self.flips % 4096 == 0:
                el = time.time() - t0
                if el > seconds:
                    return best, False
                if el > nextrep:
                    print(f"  t={el:6.1f}s flips={self.flips} "
                          f"unsat={len(self.unsat)} best={best}", flush=True)
                    nextrep += report
        return 0, True


def main():
    n1, n2, n3, r = map(int, sys.argv[1:5])
    secs = 60.0
    noise = 0.2
    pair = False
    args = sys.argv[5:]
    for i, a in enumerate(args):
        if a == "--seconds":
            secs = float(args[i + 1])
        if a == "--noise":
            noise = float(args[i + 1])
        if a == "--pair":
            pair = True
    rng = random.Random(12345)
    tries = 0
    t0 = time.time()
    while time.time() - t0 < secs:
        tries += 1
        s = Sls(n1, n2, n3, r, rng)
        if pair:
            groups = random_pairing(n1, r, rng)
            s.frozen = pairing_units(groups, n1, n2, n3, r)
            print(f"pairing: froze {len(s.frozen)} vars "
                  f"({sum(1 for g in groups if len(g) == 2)} paired products)")
        s.init_random()
        left = secs - (time.time() - t0)
        best, ok = s.run(min(left, secs), noise)
        rate = s.flips / max(time.time() - t0, 1e-9)
        if ok:
            bad = verify_bits(s.bits, n1, n2, n3, r)
            print(f"SOLVED try={tries} flips={s.flips} "
                  f"({rate:.0f} flips/s) verify: {bad} violated "
                  f"({'VALID' if bad == 0 else 'BUG'})")
            return
        print(f"try {tries}: best={best} flips={s.flips} ({rate:.0f}/s)")
    print(f"no solution in {secs}s ({tries} tries)")


if __name__ == "__main__":
    main()
