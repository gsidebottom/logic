#!/usr/bin/env python3
"""Path-space (connection-method) local search on the Brent ANF matrix.

Assignment-space SLS walks on variable values. This walks on PATHS through
the non-clausal matrix: per equation a "scenario" S_e = the set of ON
monomials (|S_e| = rhs_e mod 2), and for every OFF monomial a "blocker" =
one of its 3 vars asserted 0 (the disjunct the path takes). A variable
forced 1 by some ON monomial and 0 by some blocker is a CONNECTION
(conflict); zero connections <=> the induced assignment (v=1 iff some ON
monomial contains v) satisfies every equation by construction.

Moves, on a random conflicted variable v:
  - re-blocker: a blocker asserting v moves to a sibling var of its
    monomial;
  - scenario swap: an ON monomial containing v swaps out of S_e for a
    currently-OFF monomial (parity preserved; the leaving monomial's
    blocker is set to v, aligning with the 0-side).
Greedy on the connection-count delta with WalkSAT-style noise.

Frozen bits are permanent force-counts: frozen-1 vars can't be blocked,
frozen-0 vars can't sit in ON monomials — violations surface as ordinary
connections the search must clear.

Usage: python3 pathsls.py n1 n2 n3 r [--seconds S] [--noise P]
                [--fix-file F --nfix K] [--seed N]
"""
import random
import sys
import time

from brent import brent_equations, var_counts, verify_bits


class PathSls:
    def __init__(self, n1, n2, n3, r, rng, frozen=None):
        self.dims = (n1, n2, n3, r)
        self.rng = rng
        eqs = brent_equations(n1, n2, n3, r)
        self.mons = [m for m, _ in eqs]
        self.rhs = [rh for _, rh in eqs]
        self.nv = sum(var_counts(n1, n2, n3, r))
        self.ne = len(eqs)
        self.moves = 0
        # frozen: dict var -> bit
        self.frozen = frozen or {}
        self.f1 = [0] * self.nv  # permanent force-1 (frozen 1)
        self.f0 = [0] * self.nv  # permanent force-0 (frozen 0)
        for v, b in self.frozen.items():
            (self.f1 if b else self.f0)[v] = 1

    # ---------------- state init ----------------

    def init_random(self, density=0.25):
        rng = self.rng
        x = [1 if rng.random() < density else 0 for _ in range(self.nv)]
        for v, b in self.frozen.items():
            x[v] = b
        self.on = []        # per eq: set of ON monomial indices
        self.blk = []       # per eq: dict off-mon-index -> blocker var
        self.force1 = list(self.f1)
        self.force0 = list(self.f0)
        for e in range(self.ne):
            mons = self.mons[e]
            s = {i for i, (a, b, g) in enumerate(mons)
                 if x[a] & x[b] & x[g]}
            if (len(s) & 1) != self.rhs[e]:
                # toggle one monomial to fix parity (prefer removing)
                if s:
                    s.discard(next(iter(s)))
                else:
                    s.add(rng.randrange(len(mons)))
            bd = {}
            for i, (a, b, g) in enumerate(mons):
                if i in s:
                    for v in (a, b, g):
                        self.force1[v] += 1
                else:
                    zeros = [v for v in (a, b, g) if x[v] == 0]
                    w = zeros[rng.randrange(len(zeros))] if zeros else \
                        (a, b, g)[rng.randrange(3)]
                    bd[i] = w
                    self.force0[w] += 1
            self.on.append(s)
            self.blk.append(bd)
        self._rebuild_conflicts()

    def _rebuild_conflicts(self):
        self.conf = [v for v in range(self.nv)
                     if self.force1[v] > 0 and self.force0[v] > 0]
        self.cpos = [-1] * self.nv
        for i, v in enumerate(self.conf):
            self.cpos[v] = i

    # ---------------- incremental conflict set ----------------

    def _chk(self, v):
        inc = self.force1[v] > 0 and self.force0[v] > 0
        if inc and self.cpos[v] < 0:
            self.cpos[v] = len(self.conf)
            self.conf.append(v)
        elif not inc and self.cpos[v] >= 0:
            i = self.cpos[v]
            last = self.conf[-1]
            self.conf[i] = last
            self.cpos[last] = i
            self.conf.pop()
            self.cpos[v] = -1

    def _d_force1(self, v, d):
        self.force1[v] += d
        self._chk(v)

    def _d_force0(self, v, d):
        self.force0[v] += d
        self._chk(v)

    # ---------------- moves ----------------

    def _delta_conflict(self, v, df1, df0):
        """conflict-count delta if force1[v] += df1, force0[v] += df0."""
        before = self.force1[v] > 0 and self.force0[v] > 0
        after = (self.force1[v] + df1) > 0 and (self.force0[v] + df0) > 0
        return int(after) - int(before)

    def _reblocker_delta(self, e, i, w_new, w_old):
        d = self._delta_conflict(w_old, 0, -1)
        d += self._delta_conflict(w_new, 0, +1) if w_new != w_old else 0
        return d

    def _apply_reblocker(self, e, i, w_new):
        w_old = self.blk[e][i]
        self.blk[e][i] = w_new
        self._d_force0(w_old, -1)
        self._d_force0(w_new, +1)
        self.moves += 1

    def _swap_delta_and_apply(self, e, i_out, i_in, apply_it):
        """swap ON monomial i_out with OFF monomial i_in in equation e;
        blocker of i_out becomes... caller supplies via apply; returns
        delta if not applying."""
        mons = self.mons[e]
        if not apply_it:
            d = 0
            f1 = self.force1
            for v in mons[i_out]:
                d += self._delta_conflict(v, -1, 0)
            # approximate: deltas of i_in vars computed on current counts
            for v in mons[i_in]:
                d += self._delta_conflict(v, +1, 0)
            w_in_blk = self.blk[e][i_in]
            d += self._delta_conflict(w_in_blk, 0, -1)
            # new blocker for i_out: choose best sibling later; assume the
            # conflicted var (0-side alignment) -> delta of +force0 there
            return d
        # apply
        for v in mons[i_out]:
            self._d_force1(v, -1)
        for v in mons[i_in]:
            self._d_force1(v, +1)
        w_in_blk = self.blk[e].pop(i_in)
        self._d_force0(w_in_blk, -1)
        self.on[e].discard(i_out)
        self.on[e].add(i_in)
        # blocker for the newly-OFF i_out: pick var minimizing conflicts
        best_w, best_d = None, None
        for v in mons[i_out]:
            d = self._delta_conflict(v, 0, +1)
            if best_d is None or d < best_d:
                best_w, best_d = v, d
        self.blk[e][i_out] = best_w
        self._d_force0(best_w, +1)
        self.moves += 1

    def step(self, noise=0.2, swap_prob=0.5):
        rng = self.rng
        if not self.conf:
            return False
        v = self.conf[rng.randrange(len(self.conf))]
        # gather move candidates on v
        blockers = [(e, i) for e in range(self.ne)
                    for i, w in self.blk[e].items() if w == v]
        # too slow to scan all equations: keep an index instead
        raise RuntimeError("unindexed prototype path; use PathSlsIdx")


class PathSlsIdx(PathSls):
    """PathSls + var -> (blocker sites, ON sites) indices for O(1) moves."""

    def init_random(self, density=0.25):
        super().init_random(density)
        self.blk_sites = [set() for _ in range(self.nv)]  # v -> {(e,i)}
        self.on_sites = [set() for _ in range(self.nv)]   # v -> {(e,i)}
        for e in range(self.ne):
            for i, w in self.blk[e].items():
                self.blk_sites[w].add((e, i))
            for i in self.on[e]:
                for v in self.mons[e][i]:
                    self.on_sites[v].add((e, i))

    def _apply_reblocker(self, e, i, w_new):
        w_old = self.blk[e][i]
        self.blk_sites[w_old].discard((e, i))
        self.blk_sites[w_new].add((e, i))
        super()._apply_reblocker(e, i, w_new)

    def _swap_apply(self, e, i_out, i_in):
        mons = self.mons[e]
        for v in mons[i_out]:
            self.on_sites[v].discard((e, i_out))
            self._d_force1(v, -1)
        for v in mons[i_in]:
            self.on_sites[v].add((e, i_in))
            self._d_force1(v, +1)
        w_in_blk = self.blk[e].pop(i_in)
        self.blk_sites[w_in_blk].discard((e, i_in))
        self._d_force0(w_in_blk, -1)
        self.on[e].discard(i_out)
        self.on[e].add(i_in)
        best_w, best_d = None, None
        for v in mons[i_out]:
            d = self._delta_conflict(v, 0, +1)
            if best_d is None or d < best_d or \
                    (d == best_d and self.rng.random() < 0.5):
                best_w, best_d = v, d
        self.blk[e][i_out] = best_w
        self.blk_sites[best_w].add((e, i_out))
        self._d_force0(best_w, +1)
        self.moves += 1

    def _pair_remove(self, e, i1, i2):
        """turn two ON monomials OFF (parity preserved)."""
        for i_out in (i1, i2):
            mons = self.mons[e]
            for v in mons[i_out]:
                self.on_sites[v].discard((e, i_out))
                self._d_force1(v, -1)
            self.on[e].discard(i_out)
            best_w, best_d = None, None
            for v in mons[i_out]:
                d = self._delta_conflict(v, 0, +1)
                if best_d is None or d < best_d:
                    best_w, best_d = v, d
            self.blk[e][i_out] = best_w
            self.blk_sites[best_w].add((e, i_out))
            self._d_force0(best_w, +1)
        self.moves += 1

    def _pair_add(self, e, i1, i2):
        """turn two OFF monomials ON (parity preserved)."""
        for i_in in (i1, i2):
            mons = self.mons[e]
            w = self.blk[e].pop(i_in)
            self.blk_sites[w].discard((e, i_in))
            self._d_force0(w, -1)
            self.on[e].add(i_in)
            for v in mons[i_in]:
                self.on_sites[v].add((e, i_in))
                self._d_force1(v, +1)
        self.moves += 1

    def step(self, noise=0.2, swap_prob=0.5, pair_prob=0.15):
        rng = self.rng
        if not self.conf:
            return False
        v = self.conf[rng.randrange(len(self.conf))]
        if rng.random() < pair_prob:
            # size-changing move around v (parity preserved)
            if self.on_sites[v] and rng.random() < 0.7:
                e, i1 = rng.choice(tuple(self.on_sites[v]))
                others = [i for i in self.on[e] if i != i1]
                if others:
                    self._pair_remove(e, i1,
                                      others[rng.randrange(len(others))])
                    return bool(self.conf)
            elif self.blk_sites[v]:
                e, i1 = rng.choice(tuple(self.blk_sites[v]))
                offs = [i for i in self.blk[e] if i != i1]
                if offs:
                    cand = rng.sample(offs, min(4, len(offs)))
                    i2 = min(cand, key=lambda i: sum(
                        self._delta_conflict(w, +1, 0)
                        for w in self.mons[e][i]))
                    self._pair_add(e, i1, i2)
                    return bool(self.conf)
        do_swap = rng.random() < swap_prob
        if not do_swap and self.blk_sites[v]:
            # re-blocker: move one blocker off v
            e, i = rng.choice(tuple(self.blk_sites[v]))
            sibs = [w for w in self.mons[e][i] if w != v]
            if rng.random() < noise:
                w = sibs[rng.randrange(len(sibs))]
            else:
                w = min(sibs, key=lambda x: self._delta_conflict(x, 0, +1))
            self._apply_reblocker(e, i, w)
        elif self.on_sites[v]:
            # scenario swap: push one ON monomial containing v out
            e, i_out = rng.choice(tuple(self.on_sites[v]))
            offs = [i for i in range(len(self.mons[e]))
                    if i not in self.on[e]]
            if not offs:
                return bool(self.conf)
            if rng.random() < noise:
                i_in = offs[rng.randrange(len(offs))]
            else:
                # sample a few candidates, pick min entering-conflict
                cand = rng.sample(offs, min(6, len(offs)))
                i_in = min(cand, key=lambda i: sum(
                    self._delta_conflict(w, +1, 0) for w in self.mons[e][i]))
            self._swap_apply(e, i_out, i_in)
        elif self.blk_sites[v]:
            e, i = rng.choice(tuple(self.blk_sites[v]))
            sibs = [w for w in self.mons[e][i] if w != v]
            w = sibs[rng.randrange(len(sibs))]
            self._apply_reblocker(e, i, w)
        return bool(self.conf)

    def assignment(self):
        return [1 if self.force1[v] > 0 else 0 for v in range(self.nv)]

    def run(self, seconds, noise=0.2, swap_prob=0.5, restart_moves=200_000):
        t0 = time.time()
        best = self.ne + 1
        while True:
            self.init_random()
            since = 0
            while self.conf:
                self.step(noise, swap_prob)
                since += 1
                best = min(best, len(self.conf))
                if self.moves % 2048 == 0 and time.time() - t0 > seconds:
                    return best, False
                if since > restart_moves:
                    break
            if not self.conf:
                return 0, True


def main():
    n1, n2, n3, r = map(int, sys.argv[1:5])
    args = sys.argv[5:]

    def val(k, d, cast=float):
        return cast(args[args.index(k) + 1]) if k in args else d

    secs = val("--seconds", 30.0)
    noise = val("--noise", 0.2)
    swap = val("--swap-prob", 0.5)
    seed = val("--seed", 1, int)
    rng = random.Random(seed)
    frozen = {}
    if "--fix-file" in args:
        s = open(args[args.index("--fix-file") + 1]).read().split()[-1]
        bits = [int(c) for c in s.strip()]
        nfix = val("--nfix", 300, int)
        idx = rng.sample(range(len(bits)), nfix)
        frozen = {v: bits[v] for v in idx}
    p = PathSlsIdx(n1, n2, n3, r, rng, frozen)
    t0 = time.time()
    best, ok = p.run(secs, noise, swap)
    dt = time.time() - t0
    rate = p.moves / dt
    if ok:
        x = p.assignment()
        bad = verify_bits(x, n1, n2, n3, r)
        print(f"SOLVED in {dt:.2f}s, {p.moves} moves ({rate:.0f}/s), "
              f"verify: {bad} violated ({'VALID' if bad == 0 else 'BUG'})")
    else:
        print(f"UNKNOWN after {dt:.1f}s, {p.moves} moves ({rate:.0f}/s), "
              f"best {best} connections")


if __name__ == "__main__":
    main()
