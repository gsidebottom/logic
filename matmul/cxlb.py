#!/usr/bin/env python3
"""Exact GF(2) XOR-SLP minimization / lower bounds for the C side.

The C side of a scheme computes 9 output forms over the 23 products.
Any Z-side SLP reduces mod 2 to an XOR-SLP, so the exact GF(2)
minimum is a sound LOWER bound on the ternary/Z C-side additions:
UNSAT of "k additions suffice" at k proves C_Z >= k+1.  Combined
with the slim-sides exhaustions, UNSAT at the right k on the right
(R,P) cells closes entire classes for 55.

Encoding (Fuhs--Schneider-Kamp flavored, simplified by unit-vector
inputs): step t in 1..k selects exactly two sources among the n
bases and steps 1..t-1; value bits are defined by parity chains
  x[t][i] = sel[t][base_i]  XOR  XOR_{j<t} (sel[t][step_j] AND x[j][i])
and every output form must equal some step value (or a base, for
weight-1 outputs).  Dead steps are forbidden (every step feeds a
later step or an output).  Solved with kissat; --drat asks kissat
for a DRAT proof on UNSAT (verifiable evidence for the bound).

Usage:
  cxlb.py selftest
  cxlb.py --bits FILE [--k N | --min] [--start K] [--timeout S]
  cxlb.py --forms 3,6,5 --n 3 --k 2      # masks over n base vars
"""
import os
import subprocess
import sys
import tempfile

sys.path.insert(0, __file__.rsplit("/", 1)[0])


class CNF:
    def __init__(self):
        self.n = 0
        self.clauses = []

    def var(self):
        self.n += 1
        return self.n

    def add(self, *lits):
        self.clauses.append(list(lits))

    def xor3(self, a, b, c):
        """c = a XOR b (4 clauses)."""
        self.add(-a, -b, -c)
        self.add(a, b, -c)
        self.add(a, -b, c)
        self.add(-a, b, c)

    def and2(self, a, b, c):
        """c = a AND b."""
        self.add(-a, -b, c)
        self.add(a, -c)
        self.add(b, -c)

    def exactly2(self, lits):
        """sequential counter <=2 plus >=2 (naive but small)."""
        # at least 2: forbid all-zero and exactly-one
        self.add(*lits)
        for i, x in enumerate(lits):
            others = [y for j, y in enumerate(lits) if j != i]
            self.add(-x, *others)  # x -> some other
        # at most 2: no three true (sequential counter)
        s1 = s2 = None
        for x in lits:
            n1, n2 = self.var(), self.var()
            # n1 = s1 | x ; n2 = s2 | (s1 & x); forbid s2 & x
            if s1 is None:
                self.add(-x, n1)
                self.add(x, -n1)
                self.add(-n2)
            else:
                self.add(-s1, n1)
                self.add(-x, n1)
                self.add(s1, x, -n1)
                aux = self.var()
                self.and2(s1, x, aux)
                self.add(-s2, n2)
                self.add(-aux, n2)
                self.add(s2, aux, -n2)
                # forbid third: s2 & x
                self.add(-s2, -x)
            s1, s2 = n1, n2

    def solve(self, timeout=None, drat=None):
        with tempfile.NamedTemporaryFile("w", suffix=".cnf",
                                         delete=False) as f:
            f.write(f"p cnf {self.n} {len(self.clauses)}\n")
            for c in self.clauses:
                f.write(" ".join(map(str, c)) + " 0\n")
            path = f.name
        cmd = ["kissat", "-q", path]
        if drat:
            cmd = ["kissat", "-q", path, drat]
        if timeout:
            cmd = ["kissat", "-q", f"--time={int(timeout)}", path] + (
                [drat] if drat else [])
        r = subprocess.run(cmd, capture_output=True, text=True)
        os.unlink(path)
        if "s SATISFIABLE" in r.stdout:
            model = set()
            for line in r.stdout.splitlines():
                if line.startswith("v"):
                    for tok in line.split()[1:]:
                        x = int(tok)
                        if x > 0:
                            model.add(x)
            return True, model
        if "s UNSATISFIABLE" in r.stdout:
            return False, None
        return None, None  # timeout / unknown


def slp_k(forms, n, k, timeout=None, drat=None):
    """SAT: k XOR additions compute all forms (masks over n bases)?
    Returns (True, chain) | (False, None) | (None, None) on timeout.
    chain = [(src1, src2), ...] with sources <n = bases else step."""
    forms = list(forms)
    for f in forms:
        assert 0 < f < (1 << n)
    cnf = CNF()
    # sel[t][j]: step t (0-based) uses source j (0..n+t-1)
    sel = [[cnf.var() for _ in range(n + t)] for t in range(k)]
    # x[t][i]
    x = [[cnf.var() for _ in range(n)] for _ in range(k)]
    for t in range(k):
        cnf.exactly2(sel[t])
        for i in range(n):
            # parity chain: x[t][i] = sel[t][i] ^ XOR_j (sel[t][n+j] & x[j][i])
            acc = sel[t][i]
            for j in range(t):
                a = cnf.var()
                cnf.and2(sel[t][n + j], x[j][i], a)
                nxt = cnf.var()
                cnf.xor3(acc, a, nxt)
                acc = nxt
            # x[t][i] <-> acc
            cnf.add(-x[t][i], acc)
            cnf.add(x[t][i], -acc)
    # outputs: each form equals some step value or a base
    outsel = []
    for f in forms:
        opts = []
        wt1_base = None
        if bin(f).count("1") == 1:
            wt1_base = f.bit_length() - 1
        for t in range(k):
            o = cnf.var()
            opts.append((o, t))
            for i in range(n):
                bit = (f >> i) & 1
                cnf.add(-o, x[t][i] if bit else -x[t][i])
        if wt1_base is not None:
            o = cnf.var()
            opts.append((o, None))  # base matches trivially
        cnf.add(*[o for o, _ in opts])
        outsel.append(opts)
    # no dead steps: step t feeds a later step or an output
    for t in range(k):
        feeds = [sel[t2][n + t] for t2 in range(t + 1, k)]
        feeds += [o for opts in outsel for (o, tt) in opts if tt == t]
        if feeds:
            cnf.add(*feeds)
        # (a step with no possible consumer only at t=k-1 with no
        # matching output — the clause above is then empty-safe)
    ok, model = cnf.solve(timeout=timeout, drat=drat)
    if ok is not True:
        return ok, None
    chain = []
    for t in range(k):
        srcs = [j for j in range(n + t) if sel[t][j] in model]
        assert len(srcs) == 2, srcs
        chain.append((srcs[0], srcs[1]))
    # replay-verify the witness
    vals = [1 << i for i in range(n)]
    for (a, b) in chain:
        vals.append(vals[a] ^ vals[b])
    for f in forms:
        assert f in vals, f"form {f:b} not computed"
    return True, chain


def min_slp(forms, n, start, timeout=None, verbose=True):
    """descend k from `start` until UNSAT; returns (min_k, status).
    status 'exact' if the UNSAT boundary was proven, 'timeout' if a
    solve timed out (min_k is then only an upper bound)."""
    k = start
    best = None
    while k >= 0:
        ok, chain = slp_k(forms, n, k, timeout=timeout)
        if verbose:
            tag = {True: "SAT", False: "UNSAT", None: "TIMEOUT"}[ok]
            print(f"  k={k}: {tag}", flush=True)
        if ok is True:
            best = k
            k -= 1
        elif ok is False:
            return best, "exact"
        else:
            return best, "timeout"
    return best, "exact"


def c_forms_from_bits(bits):
    forms = []
    for pq in range(9):
        m = 0
        for prod in range(23):
            if bits[414 + prod * 9 + pq]:
                m |= 1 << prod
        forms.append(m)
    return forms


def selftest():
    # single weight-3 output: min 2
    assert slp_k([0b111], 3, 2)[0] is True
    assert slp_k([0b111], 3, 1)[0] is False
    # pair + extension: min 2
    assert slp_k([0b011, 0b111], 3, 2)[0] is True
    assert slp_k([0b011, 0b111], 3, 1)[0] is False
    # three pairwise forms, pure chain: min 3
    fs = [0b011, 0b110, 0b101]
    assert slp_k(fs, 3, 3)[0] is True
    assert slp_k(fs, 3, 2)[0] is False
    # weight 4: min 3
    assert slp_k([0b1111], 4, 3)[0] is True
    assert slp_k([0b1111], 4, 2)[0] is False
    # weight-1 output is free
    assert slp_k([0b010, 0b011], 3, 1)[0] is True
    # shared subexpression: {a^b^c, a^b^d} = 3 (w=a^b reused)
    assert slp_k([0b0111, 0b1011], 4, 3)[0] is True
    assert slp_k([0b0111, 0b1011], 4, 2)[0] is False
    print("cxlb selftest: ALL OK")


def main():
    argv = sys.argv[1:]
    if argv and argv[0] == "selftest":
        selftest()
        return

    def opt(name, default, cast=str):
        if name in argv:
            i = argv.index(name)
            v = cast(argv[i + 1])
            del argv[i:i + 2]
            return v
        return default

    k = opt("--k", None, int)
    start = opt("--start", 30, int)
    timeout = opt("--timeout", None, float)
    formsarg = opt("--forms", None, str)
    nvars = opt("--n", 23, int)
    bitsfile = opt("--bits", None, str)
    do_min = "--min" in argv

    if formsarg:
        forms = [int(x) for x in formsarg.split(",")]
        n = nvars
    elif bitsfile:
        bits = [int(c) for c in open(bitsfile).read().split()[-1].strip()]
        forms = c_forms_from_bits(bits)
        n = 23
        w = sum(bin(f).count("1") for f in forms)
        print(f"{bitsfile}: C-side 9 forms over 23 products, "
              f"total weight {w}, naive {w - 9}")
    else:
        sys.exit("need --forms or --bits")

    if do_min:
        best, status = min_slp(forms, n, start, timeout=timeout)
        print(f"GF(2) C-min: {best} ({status})"
              + ("" if status == "exact"
                 else " — upper bound only; raise --timeout"))
        if status == "exact" and best is not None:
            print(f"=> C_Z >= {best} for every ternary/Z SLP "
                  f"of this C side (sound lower bound)")
    else:
        assert k is not None, "need --k or --min"
        ok, chain = slp_k(forms, n, k, timeout=timeout)
        print({True: f"SAT: {k} additions suffice",
               False: f"UNSAT: {k} additions impossible "
                      f"=> C >= {k + 1} (GF2, hence Z)",
               None: "TIMEOUT"}[ok])
        if chain:
            for t, (a, b) in enumerate(chain):
                fmt = lambda s: (f"M{s+1}" if s < n else f"t{s-n}")
                print(f"  t{t} = {fmt(a)} ^ {fmt(b)}")


if __name__ == "__main__":
    main()
