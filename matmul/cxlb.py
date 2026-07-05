#!/usr/bin/env python3
"""Exact GF(2) XOR-SLP minimization / lower bounds for the C side. v2.

The C side of a scheme computes 9 output forms over the 23 products.
Any Z-side SLP reduces mod 2 to an XOR-SLP, so the exact GF(2)
minimum is a sound LOWER bound on the ternary/Z C-side additions:
UNSAT of "k additions suffice" at k proves C_Z >= k+1.  Combined
with the slim-sides exhaustions, UNSAT at the right k on the right
(R,P) cells closes entire classes for 55.

Encoding (Fuhs--Schneider-Kamp flavored, simplified by unit-vector
inputs): step t selects exactly two sources among the n bases and
steps 1..t-1; value bits are parity-defined
  x[t][i] = sel[t][base_i] XOR XOR_{j<t} (sel[t][step_j] AND x[j][i])
and every output form must equal some step value (or a base, for
weight-1 outputs).  Dead steps are forbidden.

v2 additions:
  * symmetry breaking (default on): step values nonzero, and any two
    ADJACENT INDEPENDENT steps (t+1 does not consume t) must have
    strictly lex-increasing values.  Sound: swapping adjacent
    independent steps preserves validity, so any program bubble-sorts
    into this canonical form; distinct-value programs always exist at
    any feasible k (pad with fresh values).
  * parity constraints are collected abstractly and materialized as
    Tseitin chains (kissat/cadical/z3) or NATIVE x-lines for
    cryptominisat (Gaussian elimination can then engage; also drops
    the chain auxiliaries).
  * portfolio solving: kissat, cadical, cryptominisat5 in parallel on
    the same instance; first conclusive answer wins, rest killed.
  * --window K: the production single-shot decision (e.g. UNSAT at
    27 => C_Z >= 28), with --drat PATH for a kissat proof run.

Usage:
  cxlb.py selftest
  cxlb.py --bits FILE [--k N | --min | --window K] [--start K]
          [--timeout S] [--no-sb] [--solvers kissat,cadical,cms]
          [--drat PATH]
  cxlb.py --forms 3,6,5 --n 3 --k 2      # masks over n base vars
"""
import os
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, __file__.rsplit("/", 1)[0])

SOLVER_CMDS = {
    "kissat": ["kissat", "-q"],
    "cadical": ["cadical", "-q"],
    "cms": ["cryptominisat5", "--verb", "0"],
}


class CNF:
    """clauses + abstract XOR constraints (materialized per solver)."""

    def __init__(self):
        self.n = 0
        self.clauses = []
        self.xors = []  # lists of literals L with XOR(L) == False

    def var(self):
        self.n += 1
        return self.n

    def add(self, *lits):
        self.clauses.append(list(lits))

    def xor_zero(self, lits):
        """assert XOR of lits == 0 (even parity of true literals)."""
        lits = [l for l in lits if l != 0]
        assert lits
        self.xors.append(list(lits))

    def and2(self, a, b, c):
        """c = a AND b."""
        self.add(-a, -b, c)
        self.add(a, -c)
        self.add(b, -c)

    def exactly2(self, lits):
        # at least 2
        self.add(*lits)
        for i, x in enumerate(lits):
            others = [y for j, y in enumerate(lits) if j != i]
            self.add(-x, *others)
        # at most 2 (sequential)
        s1 = s2 = None
        for x in lits:
            n1, n2 = self.var(), self.var()
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
                self.add(-s2, -x)
            s1, s2 = n1, n2

    # ---- materialization ----

    def _tseitin_xor(self):
        """expand xors into CNF clauses with chain auxiliaries;
        returns (nvars, clauses)."""
        n = self.n
        clauses = [list(c) for c in self.clauses]

        def xor3(a, b, c):
            clauses.append([-a, -b, -c])
            clauses.append([a, b, -c])
            clauses.append([a, -b, c])
            clauses.append([-a, b, c])

        for lits in self.xors:
            if len(lits) == 1:
                clauses.append([-lits[0]])
                continue
            acc = lits[0]
            for l in lits[1:-1]:
                n += 1
                xor3(acc, l, n)
                acc = n
            # acc XOR last == 0  <=>  acc == last
            clauses.append([-acc, lits[-1]])
            clauses.append([acc, -lits[-1]])
        return n, clauses

    def write(self, path, native_xor=False):
        if native_xor:
            with open(path, "w") as f:
                f.write(f"p cnf {self.n} "
                        f"{len(self.clauses) + len(self.xors)}\n")
                for c in self.clauses:
                    f.write(" ".join(map(str, c)) + " 0\n")
                for lits in self.xors:
                    # x-line asserts XOR(lits) == True; flip one sign
                    # to assert == False
                    flipped = [-lits[0]] + lits[1:]
                    f.write("x " + " ".join(map(str, flipped)) + " 0\n")
        else:
            n, clauses = self._tseitin_xor()
            with open(path, "w") as f:
                f.write(f"p cnf {n} {len(clauses)}\n")
                for c in clauses:
                    f.write(" ".join(map(str, c)) + " 0\n")

    def solve(self, timeout=None, solvers=("kissat",), drat=None):
        """portfolio solve; returns (True, model)|(False, None)|(None, None).
        drat: path — kissat-only proof run (UNSAT certificate)."""
        if drat:
            solvers = ("kissat",)
        tmp = {}
        procs = {}
        try:
            for s in solvers:
                suffix = ".cnf"
                path = tempfile.NamedTemporaryFile(
                    "w", suffix=suffix, delete=False).name
                self.write(path, native_xor=(s == "cms"))
                tmp[s] = path
                cmd = list(SOLVER_CMDS[s]) + [path]
                if drat and s == "kissat":
                    cmd.append(drat)
                procs[s] = subprocess.Popen(
                    cmd, stdout=subprocess.PIPE,
                    stderr=subprocess.DEVNULL, text=True)
            t0 = time.time()
            done = {}
            while procs:
                for s, p in list(procs.items()):
                    rc = p.poll()
                    if rc is None:
                        continue
                    out = p.stdout.read()
                    del procs[s]
                    if "s SATISFIABLE" in out:
                        done[s] = (True, out)
                    elif "s UNSATISFIABLE" in out:
                        done[s] = (False, out)
                if done:
                    break
                if timeout and time.time() - t0 > timeout:
                    break
                time.sleep(0.05)
            for p in procs.values():
                p.kill()
            for p in procs.values():
                p.wait()
            if not done:
                return None, None
            s, (sat, out) = next(iter(done.items()))
            if not sat:
                return False, None
            model = set()
            for line in out.splitlines():
                if line.startswith("v"):
                    for tok in line.split()[1:]:
                        x = int(tok)
                        if x > 0:
                            model.add(x)
            return True, model
        finally:
            for path in tmp.values():
                try:
                    os.unlink(path)
                except OSError:
                    pass


def build_cnf(forms, n, k, sb=True):
    """encode: k XOR additions compute all forms; returns (cnf, sel)."""
    forms = list(forms)
    for f in forms:
        assert 0 < f < (1 << n)
    cnf = CNF()
    sel = [[cnf.var() for _ in range(n + t)] for t in range(k)]
    x = [[cnf.var() for _ in range(n)] for _ in range(k)]
    for t in range(k):
        cnf.exactly2(sel[t])
        for i in range(n):
            # x[t][i] XOR sel[t][i] XOR XOR_j (sel[t][n+j] & x[j][i]) = 0
            terms = [x[t][i], sel[t][i]]
            for j in range(t):
                a = cnf.var()
                cnf.and2(sel[t][n + j], x[j][i], a)
                terms.append(a)
            cnf.xor_zero(terms)
    # outputs
    outsel = []
    for f in forms:
        opts = []
        for t in range(k):
            o = cnf.var()
            opts.append((o, t))
            for i in range(n):
                bit = (f >> i) & 1
                cnf.add(-o, x[t][i] if bit else -x[t][i])
        if bin(f).count("1") == 1:
            o = cnf.var()
            opts.append((o, None))
        cnf.add(*[o for o, _ in opts])
        outsel.append(opts)
    # NOTE: no dead-step elimination — it breaks monotonicity in k
    # (odd-length padding cannot always avoid dead steps, so SAT(k)
    # could fail above the true min and a descent would misreport).
    # SB below keeps padding available: fresh-value steps appended in
    # a dependent chain never face a lex constraint.
    _ = outsel
    if sb:
        # step values nonzero
        for t in range(k):
            cnf.add(*[x[t][i] for i in range(n)])
        # adjacent independent steps strictly value-lex increasing
        for t in range(k - 1):
            ind = cnf.var()  # step t+1 does NOT use step t
            cnf.add(ind, sel[t + 1][n + t])
            cnf.add(-ind, -sel[t + 1][n + t])
            # ind -> x[t+1] >lex x[t]   (bit n-1 most significant)
            prefix = None  # prefix equality so far
            gts = []
            for i in range(n - 1, -1, -1):
                g = cnf.var()  # strictly greater decided at bit i
                if prefix is None:
                    # g = x[t+1][i] & ~x[t][i]
                    cnf.add(-g, x[t + 1][i])
                    cnf.add(-g, -x[t][i])
                    cnf.add(g, -x[t + 1][i], x[t][i])
                else:
                    cnf.add(-g, prefix)
                    cnf.add(-g, x[t + 1][i])
                    cnf.add(-g, -x[t][i])
                    cnf.add(g, -prefix, -x[t + 1][i], x[t][i])
                gts.append(g)
                eq = cnf.var()  # bits equal at i
                cnf.add(-eq, x[t + 1][i], -x[t][i])
                cnf.add(-eq, -x[t + 1][i], x[t][i])
                cnf.add(eq, x[t + 1][i], x[t][i])
                cnf.add(eq, -x[t + 1][i], -x[t][i])
                if prefix is None:
                    prefix = eq
                else:
                    np_ = cnf.var()
                    cnf.and2(prefix, eq, np_)
                    prefix = np_
            cnf.add(-ind, *gts)
    return cnf, sel


def slp_k(forms, n, k, timeout=None, solvers=("kissat",), sb=True,
          drat=None):
    """SAT: k XOR additions compute all forms (masks over n bases)?
    Returns (True, chain)|(False, None)|(None, None)."""
    cnf, sel = build_cnf(forms, n, k, sb=sb)
    ok, model = cnf.solve(timeout=timeout, solvers=solvers, drat=drat)
    if ok is not True:
        return ok, None
    chain = []
    for t in range(k):
        srcs = [j for j in range(n + t) if sel[t][j] in model]
        assert len(srcs) == 2, srcs
        chain.append((srcs[0], srcs[1]))
    vals = [1 << i for i in range(n)]
    for (a, b) in chain:
        vals.append(vals[a] ^ vals[b])
    for f in forms:
        assert f in vals, f"form {f:b} not computed"
    return True, chain


def min_slp(forms, n, start, timeout=None, solvers=("kissat",),
            sb=True, verbose=True):
    k = start
    best = None
    while k >= 0:
        ok, _ = slp_k(forms, n, k, timeout=timeout, solvers=solvers,
                      sb=sb)
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
    import itertools
    import random
    for sb in (True, False):
        assert slp_k([0b111], 3, 2, sb=sb)[0] is True
        assert slp_k([0b111], 3, 1, sb=sb)[0] is False
        assert slp_k([0b011, 0b111], 3, 2, sb=sb)[0] is True
        assert slp_k([0b011, 0b111], 3, 1, sb=sb)[0] is False
        fs = [0b011, 0b110, 0b101]
        assert slp_k(fs, 3, 3, sb=sb)[0] is True
        assert slp_k(fs, 3, 2, sb=sb)[0] is False
        assert slp_k([0b1111], 4, 3, sb=sb)[0] is True
        assert slp_k([0b1111], 4, 2, sb=sb)[0] is False
        assert slp_k([0b010, 0b011], 3, 1, sb=sb)[0] is True
        assert slp_k([0b0111, 0b1011], 4, 3, sb=sb)[0] is True
        assert slp_k([0b0111, 0b1011], 4, 2, sb=sb)[0] is False
    # monotonicity: SAT stays SAT above the min (padding must work)
    for sb in (True, False):
        for kk in (1, 2, 3, 4):
            assert slp_k([0b011], 3, kk, sb=sb)[0] is True, (sb, kk)
        for kk in (3, 4, 5):
            assert slp_k([0b011, 0b110, 0b101], 3, kk, sb=sb)[0] \
                is True, (sb, kk)
    print("micro optima + monotonicity: OK (sb on + off)")
    # SB-vs-noSB verdict agreement on random small instances
    rng = random.Random(11)
    for trial in range(6):
        n = 7
        forms = []
        while len(forms) < 4:
            f = rng.randrange(1, 1 << n)
            if bin(f).count("1") >= 2 and f not in forms:
                forms.append(f)
        for k in (5, 6, 7, 8):
            a = slp_k(forms, n, k, sb=True)[0]
            b = slp_k(forms, n, k, sb=False)[0]
            assert a == b, (forms, k, a, b)
    print("SB/no-SB verdict agreement: OK (6 random x 4 k's)")
    # portfolio smoke (all three solvers agree on a small instance)
    have = [s for s, cmd in SOLVER_CMDS.items()
            if subprocess.run(["which", cmd[0]],
                              capture_output=True).returncode == 0]
    ok, _ = slp_k([0b011, 0b110, 0b101], 3, 3, solvers=tuple(have))
    assert ok is True
    ok, _ = slp_k([0b011, 0b110, 0b101], 3, 2, solvers=tuple(have))
    assert ok is False
    print(f"portfolio smoke: OK ({','.join(have)})")
    print("cxlb v2 selftest: ALL OK")


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
    window = opt("--window", None, int)
    start = opt("--start", 30, int)
    timeout = opt("--timeout", None, float)
    formsarg = opt("--forms", None, str)
    nvars = opt("--n", 23, int)
    bitsfile = opt("--bits", None, str)
    drat = opt("--drat", None, str)
    solvers = tuple(opt("--solvers", "kissat,cadical,cms", str)
                    .replace("cryptominisat5", "cms").split(","))
    sb = "--no-sb" not in argv
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
        best, status = min_slp(forms, n, start, timeout=timeout,
                               solvers=solvers, sb=sb)
        print(f"GF(2) C-min: {best} ({status})"
              + ("" if status == "exact"
                 else " — upper bound only; raise --timeout"))
        if status == "exact" and best is not None:
            print(f"=> C_Z >= {best} (sound lower bound)")
        return
    dump = opt("--dump", None, str)
    kk = window if window is not None else k
    assert kk is not None, "need --k, --window or --min"
    if dump:
        cnf, _ = build_cnf(forms, n, kk, sb=sb)
        native = dump.endswith(".xnf")
        cnf.write(dump, native_xor=native)
        nv = cnf.n if native else cnf._tseitin_xor()[0]
        nc = (len(cnf.clauses) + len(cnf.xors)) if native \
            else len(cnf._tseitin_xor()[1])
        print(f"dumped k={kk} {'native-xor' if native else 'cnf'}: "
              f"{nv} vars, {nc} constraints -> {dump}")
        return
    t0 = time.time()
    ok, chain = slp_k(forms, n, kk, timeout=timeout, solvers=solvers,
                      sb=sb, drat=drat)
    dt = time.time() - t0
    print({True: f"SAT: {kk} additions suffice [{dt:.1f}s]",
           False: f"UNSAT: {kk} additions impossible => C >= {kk + 1} "
                  f"(GF2, hence Z) [{dt:.1f}s]"
                  + (f"; DRAT at {drat}" if drat else ""),
           None: f"TIMEOUT [{dt:.1f}s]"}[ok])
    if chain:
        for t, (a, b) in enumerate(chain):
            fmt = lambda s: (f"M{s+1}" if s < n else f"t{s-n}")
            print(f"  t{t} = {fmt(a)} ^ {fmt(b)}")


if __name__ == "__main__":
    main()
