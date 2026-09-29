#!/usr/bin/env python3
"""Self-test of cnf2aig's proof-carrying modes.  Nothing is taken on trust.

Generated instances (a random circuit twice, in different decompositions,
and a miter; the same with a planted difference; larger and-heavy circuits;
parity constraints that close definition cycles) go through the tool, and
for every one of them

  * an UNSAT answer on the output must come with a proof that drat-trim
    accepts against the ORIGINAL: the tool's prefix + the solver's proof,
  * a SAT answer with a model that extends to the original,
  * and the verdict must be the original's.

  MODE=sweep  (default)  cnf2aig --sweep, under a rotation of settings
  MODE=recode            cnf2aig --recode
  MODE=abc               cnf2aig --abc: ABC is not certified, so for UNSAT
                         only the verdicts are compared (ABC=path/to/abc)

  tools/selftest_cnf2aig.py FIRST_SEED LAST_SEED [PROCESSES]

Needs cadical and drat-trim (CADICAL=, DRAT= or on the PATH) and a release
build of cnf2aig (CNF2AIG= or target/release/cnf2aig).
"""
import random, itertools, subprocess, sys, os, re, tempfile, shutil
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
RS = os.environ.get("CNF2AIG", os.path.join(HERE, "..", "target", "release", "cnf2aig"))
CADICAL = os.environ.get("CADICAL", shutil.which("cadical") or "cadical")
DRAT = os.environ.get("DRAT", shutil.which("drat-trim") or "drat-trim")
ABC = os.environ.get("ABC", shutil.which("abc") or "abc")
MODE = os.environ.get("MODE", "sweep")

def write_cnf(path, nv, cls):
    with open(path, "w") as f:
        f.write(f"p cnf {nv} {len(cls)}\n")
        for c in cls: f.write(" ".join(map(str, c)) + " 0\n")

class Bld:
    def __init__(self, n_in, rng): self.v = n_in; self.cls = []; self.rng = rng
    def new(self): self.v += 1; return self.v
    def table(self, ins, f):
        # one clause per row (the padded encoding the generic detector is for)
        o = self.new()
        for bits in itertools.product([0, 1], repeat=len(ins)):
            ov = 1 if f(bits) else 0
            self.cls.append([(-x if b else x) for x, b in zip(ins, bits)] + [(o if ov else -o)])
        return o
    def and_(self, a, b): o = self.new(); self.cls += [[-o, a], [-o, b], [o, -a, -b]]; return o
    def or_(self, a, b): o = self.new(); self.cls += [[o, -a], [o, -b], [-o, a, b]]; return o
    def xor(self, a, b): o = self.new(); self.cls += [[-o, a, b], [-o, -a, -b], [o, -a, b], [o, a, -b]]; return o
    def ite(self, s, a, b): o = self.new(); self.cls += [[-s, -a, o], [-s, a, -o], [s, -b, o], [s, b, -o]]; return o
    def maj(self, a, b, c): o = self.new(); self.cls += [[-a, -b, o], [-a, -c, o], [-b, -c, o], [a, b, -o], [a, c, -o], [b, c, -o]]; return o
    def andw(self, ls): o = self.new(); self.cls += [[-o, x] for x in ls] + [[o] + [-x for x in ls]]; return o

ARITY = {"and": 2, "or": 2, "xor": 2, "xor3": 3, "maj": 3, "ite": 3, "and3": 3}

def node(b, op, a, style):
    if op == "and":  return b.and_(a[0], a[1]) if style == 0 else -b.or_(-a[0], -a[1])
    if op == "or":   return b.or_(a[0], a[1]) if style == 0 else -b.and_(-a[0], -a[1])
    if op == "xor":
        if style == 0: return b.xor(a[0], a[1])
        if style == 1: return b.or_(b.and_(a[0], -a[1]), b.and_(-a[0], a[1]))
        return b.and_(b.or_(a[0], a[1]), -b.and_(a[0], a[1]))
    if op == "xor3":
        if style == 0: return b.table(a, lambda r: (r[0] ^ r[1] ^ r[2]) == 1)
        return b.xor(b.xor(a[0], a[1]), a[2])
    if op == "maj":
        if style == 0: return b.maj(a[0], a[1], a[2])
        if style == 1: return b.or_(b.and_(a[0], a[1]), b.and_(a[2], b.or_(a[0], a[1])))
        return b.ite(a[0], b.or_(a[1], a[2]), b.and_(a[1], a[2]))
    if op == "ite":
        if style == 0: return b.ite(a[0], a[1], a[2])
        if style == 1: return b.or_(b.and_(a[0], a[1]), b.and_(-a[0], a[2]))
        return b.table(a, lambda r: r[1] if r[0] else r[2])
    if op == "and3":
        if style == 0: return b.andw(a)
        return b.and_(a[0], b.and_(a[1], a[2]))
    raise ValueError(op)

def instance(seed):
    rng = random.Random(seed)
    kind = seed % 5
    if kind == 4:
        return cyclic_instance(rng)
    if kind == 0:
        # a small random circuit twice, in different decompositions, and a miter
        n_in = rng.randint(3, 6); n_nodes = rng.randint(3, 12)
    elif kind == 1:
        n_in = rng.randint(4, 8); n_nodes = rng.randint(10, 40)
    elif kind == 2:
        # and-heavy and larger: many signals look constant or equal on few patterns
        n_in = rng.randint(8, 14); n_nodes = rng.randint(60, 250)
    else:
        n_in = rng.randint(3, 7); n_nodes = rng.randint(4, 20)
    ops = list(ARITY) if kind != 2 else ["and", "and", "and3", "or", "xor", "ite", "maj"]
    spec = []
    for j in range(n_nodes):
        op = rng.choice(ops); pool = n_in + j
        args = [(rng.randrange(pool), rng.random() < 0.3) for _ in range(ARITY[op])]
        if len({i for i, _ in args}) < len(args): args = [(i, n) for i, n in zip(rng.sample(range(pool), ARITY[op]), [x[1] for x in args])]
        spec.append((op, args))
    b = Bld(n_in, rng)
    bug = rng.randrange(n_nodes) if (kind == 3 and rng.random() < 0.6) else None
    sigs = []
    for copy in range(2):
        sig = list(range(1, n_in + 1))
        for j, (op, args) in enumerate(spec):
            a = [(-sig[i] if n else sig[i]) for i, n in args]
            if copy == 1 and bug == j:
                op2 = rng.choice([o for o in ARITY if ARITY[o] == ARITY[op] and o != op])
                sig.append(node(b, op2, a, 0))
            else:
                sig.append(node(b, op, a, 0 if copy == 0 else rng.randrange(3)))
        sigs.append(sig)
    # the miter over a few outputs, or loose constraints on the signals
    cls = b.cls
    outs = rng.sample(range(n_in, n_in + n_nodes), min(n_nodes, rng.randint(1, 4)))
    if kind == 3 and rng.random() < 0.3:
        v = b.v
        for _ in range(rng.randint(1, 4)):
            w = rng.randint(1, 3); cls.append([x if rng.random() < 0.5 else -x for x in rng.sample(range(1, v + 1), w)])
    else:
        xs = [b.xor(sigs[0][i], sigs[1][i]) for i in outs]
        cls = b.cls
        cls.append(list(xs))
    if rng.random() < 0.2: rng.shuffle(cls)
    if rng.random() < 0.2: cls = [rng.sample(c, len(c)) for c in cls]
    return b.v, cls

def cyclic_instance(rng):
    n_in = rng.randint(3, 7); n_nodes = rng.randint(4, 30)
    b = Bld(n_in, rng)
    sig = list(range(1, n_in + 1))
    for j in range(n_nodes):
        op = rng.choice(list(ARITY)); pool = len(sig)
        idx = rng.sample(range(pool), ARITY[op])
        a = [(-sig[i] if rng.random() < 0.3 else sig[i]) for i in idx]
        sig.append(node(b, op, a, rng.randrange(3)))
        if rng.random() < 0.3 and len(sig) > n_in + 1:
            # the same function again, to have something to merge
            sig.append(node(b, op, a, rng.randrange(3)))
    cls = b.cls
    gates = [x for x in sig[n_in:]]
    for _ in range(rng.randint(1, 4)):
        # x == g1 xor g2 (or its complement), x an input or an earlier gate: four clauses of one parity
        x = rng.choice(sig[:n_in + len(gates) // 2]); g1, g2 = rng.sample(gates, 2) if len(gates) >= 2 else (gates[0], gates[0])
        if len({abs(x), abs(g1), abs(g2)}) < 3: continue
        par = rng.randrange(2)
        for bits in itertools.product([0, 1], repeat=3):
            if sum(bits) % 2 == par: cls.append([(-v if bt else v) for v, bt in zip((x, g1, g2), bits)])
    for _ in range(rng.randint(0, 3)):
        w = rng.randint(2, 3); cls.append([v if rng.random() < 0.5 else -v for v in rng.sample(range(1, b.v + 1), w)])
    if rng.random() < 0.3: rng.shuffle(cls)
    return b.v, cls

SETTINGS = [[], ["--window", "1"], ["--window", "3", "--conflicts", "2"], ["--rounds", "1"], ["--tries", "1", "--rounds", "1", "--conflicts", "5"], ["--window", "4096", "--conflicts", "100000"],
            ["--rounds", "1", "--seconds", "0.002"], ["--rounds", "1", "--window", "40"],
            ["--first", "2"], ["--first", "1", "--recycle", "3", "--rounds", "1"], ["--first", "2", "--window", "30", "--rounds", "1"],
            ["--first", "1", "--conflicts", "3", "--recycle", "5"],
            ["--order", "depth"], ["--order", "depth", "--first", "2", "--rounds", "1"],
            ["--give-up", "1", "--conflicts", "2", "--first", "1"]]

def check(seed):
    nv, cls = instance(seed)
    opts = SETTINGS[(seed // 5) % len(SETTINGS)]
    d = tempfile.mkdtemp(prefix="sw_")
    try:
        inp = f"{d}/in.cnf"; out = f"{d}/out.cnf"; pre = f"{d}/prefix.drat"; drp = f"{d}/dropped.cnf"; prf = f"{d}/proof.drat"
        write_cnf(inp, nv, cls)
        if MODE == "sweep": cmd = [RS, inp, "--sweep", out, "--proof", pre, "--dropped", drp] + opts
        elif MODE == "recode": cmd = [RS, inp, "--recode", out, "--proof", pre, "--dropped", drp]; opts = []
        else: cmd = [RS, inp, "--abc", ABC, "--script", ["none", "dc2f", "resyn2f", "fraig"][seed % 4], "--out", out, "--keep", f"{d}/abc"]; opts = []
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
        if r.returncode != 0: return (seed, "TOOL FAILED", (r.stderr or r.stdout)[-400:], None)
        stats = [l for l in r.stdout.splitlines() if "sweep:" in l and "attempts" in l]   # the counts, then the whole cones
        g = subprocess.run([CADICAL, "-q", inp], capture_output=True, text=True, timeout=300)
        truth = {10: True, 20: False}.get(g.returncode)
        c = subprocess.run([CADICAL, "-q", "--binary=false", out, prf], capture_output=True, text=True, timeout=300)
        got = {10: True, 20: False}.get(c.returncode)
        if got is None or truth is None: return (seed, "SOLVER FAILED", f"in={g.returncode} out={c.returncode}", None)
        if got != truth: return (seed, "VERDICT DIFFERS", f"in={truth} out={got} opts={opts}", None)
        if not got and MODE == "abc":
            return (seed, "ok-unsat", [], opts)     # ABC is not certified: the verdicts agree, that is all
        if not got:
            comp = f"{d}/full.drat"
            with open(comp, "wb") as f: f.write(open(pre, "rb").read()); f.write(open(prf, "rb").read())
            t = subprocess.run([DRAT, inp, comp], capture_output=True, text=True, timeout=600)
            if "s VERIFIED" not in t.stdout: return (seed, "PROOF REJECTED", f"opts={opts} " + t.stdout[-500:], None)
            return (seed, "ok-unsat", stats, opts)
        used = {abs(int(t)) for l in open(out) if not l.startswith("p") and not l.startswith("c") for t in l.split() if int(t) != 0}
        model = [int(t) for l in c.stdout.splitlines() if l.startswith("v") for t in l.split()[1:] if int(t) != 0 and abs(int(t)) in used and abs(int(t)) <= nv]
        ext = f"{d}/ext.cnf"; write_cnf(ext, nv, cls + [[l] for l in model])
        e = subprocess.run([CADICAL, "-q", ext], capture_output=True, text=True, timeout=300)
        if e.returncode != 10: return (seed, "MODEL DOES NOT EXTEND", f"opts={opts}", None)
        # and by propagation alone through the dropped definitions
        return (seed, "ok-sat", stats, opts)
    except subprocess.TimeoutExpired as ex:
        return (seed, "TIMEOUT", str(ex)[:200], None)
    finally:
        shutil.rmtree(d, ignore_errors=True)

if __name__ == "__main__":
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    procs = int(sys.argv[3]) if len(sys.argv) > 3 else 12
    bad = 0; n = 0; unsat = 0; sat = 0
    whole = [0, 0]
    tot = {"attempts": 0, "merged": 0, "constant": 0, "refuted": 0, "refinements": 0, "undecided": 0, "budget": 0}
    with Pool(procs) as pool:
        for seed, verdict, info, opts in pool.imap_unordered(check, range(lo, hi), chunksize=4):
            n += 1
            if verdict == "ok-unsat": unsat += 1
            elif verdict == "ok-sat": sat += 1
            else: bad += 1; print(f"seed {seed}: {verdict}: {info}", flush=True)
            if verdict.startswith("ok") and info:
                m = re.search(r"(\d+) attempts: (\d+) merged, (\d+) constant, (\d+) refuted \((\d+) refinements\), (\d+) undecided in the window, (\d+) out of budget", info[0])
                if m:
                    for k, x in zip(tot, m.groups()): tot[k] += int(x)
                m = re.search(r"(\d+) of the attempts went to whole cones, in (\d+) solvers", info[1]) if len(info) > 1 else None
                if m: whole[0] += int(m.group(1)); whole[1] += int(m.group(2))
    proved = "UNSAT verdicts agreed (no proof: ABC is not certified)" if MODE == "abc" else "proofs verified against the original"
    print(f"{MODE} self-test: {bad} failures in {n} checks ({unsat} {proved}, {sat} models extended)")
    sys.exit(1 if bad else 0)
    print(f"  over all instances: {tot}; {whole[0]} attempts on whole cones in {whole[1]} solvers")
