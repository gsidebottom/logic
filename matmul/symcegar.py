#!/usr/bin/env python3
"""Propose-and-block search for a cyclic-invariant rank-23 scheme whose
A-leg costs at most L additions (per-step 3L+14; L = 12 is the 50), over
the quotient's orbit ansatz.

Each worker drives one symcegar solver (src/bin/symcegar.rs; seeds and
clause orders differ).  A proposed scheme is re-verified against the
full Brent system; its A-row set S has d <= L+9 distinct rows.  fbmin
decides cost(S) <= L exactly (KLAXON if so).  Otherwise S is shrunk
greedily to minimal subsets that still provably cost more than L
(fbmin's exhaustive tiers certify at most floor+3, so a core has at
least L+7 rows), and every scheme whose A-row set contains a core, or
any image of one under the cyclic symmetry group (X -> P X P^-1 for
P in GL(3,2), and transposition: 336 maps), is blocked.  Sound: leg
cost is monotone under inclusion and invariant under every invertible
linear map.  Cores are shared through workdir/cores.txt; census schemes
seed them.  "s UNSAT" from any worker proves that no scheme in the
ansatz has A-leg <= L.

The first K workers (--lex-workers) also break the relabeling symmetry
(the solver's lex constraints): they propose schemes slowly but are the
ones built to finish an UNSAT proof; the rest propose fast.  Either kind
of UNSAT is sound, since every scheme has a canonical relabeling with
the same A-row set.

Usage: symcegar.py symcegar-bin cnf map workdir fbmin [--workers N]
         [--lex-workers K] [--threads T] [--leg L] [--seed-dirs d1,..]
         [--pin file] [--max-solutions M] [--core-timeout SECS]
         [--solve-budget SECS] [--cubes reps.txt] [--wid-offset K]
Core-shrinking tests stop after SECS (an unproved subset is simply not
used as a core); the decisive test on each proposed scheme has no limit.
Each solve call is budgeted; on running out the worker loads the cores
found meanwhile and resumes (learned clauses persist).  A restart in
the same workdir reloads cores.txt and skips seeds already processed.

Cube mode (--cubes reps.txt, lines "a b"): split the final proof by the
fixed pair {A21, A22}, one cube per orbit under the 336 maps.  Every
scheme has a symmetric image whose fixed pair is its orbit's
representative (a <= b) and then a canonical relabeling (which leaves
the fixed blocks alone), with the same leg cost -- so all cubes UNSAT
proves the claim.  Workers take cubes from a queue, each in a fresh lex
solver with the pair pinned and every shared core loaded; UNSAT cubes
go to cubes_done.txt (skipped on restart).
Stop: touch workdir/STOP (checked between solves).
"""
import fcntl
import multiprocessing as mp
import os
import pathlib
import queue
import re
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from brent import brent_equations  # noqa: E402

args = sys.argv[1:]
opts = {"--workers": "8", "--lex-workers": "0", "--threads": "3", "--leg": "12",
        "--seed-dirs": "", "--pin": "", "--max-solutions": "0", "--core-timeout": "20",
        "--solve-budget": "600", "--cubes": "", "--wid-offset": "0"}
pos = []
i = 0
while i < len(args):
    if args[i] in opts:
        opts[args[i]] = args[i + 1]
        i += 2
    else:
        pos.append(args[i])
        i += 1
BIN, CNF, MAPF, FBMIN = pos[0], pos[1], pos[2], pos[4]
WORKD = pathlib.Path(pos[3])
NW, NT, L = int(opts["--workers"]), int(opts["--threads"]), int(opts["--leg"])
NLEX = int(opts["--lex-workers"])
CORE_TO = float(opts["--core-timeout"])
BUDGET = float(opts["--solve-budget"])
CUBES = opts["--cubes"]
WOFF = int(opts["--wid-offset"])
CUBES_DONE = WORKD / "cubes_done.txt"
NEED = L + 1
PIN = opts["--pin"]
MAXSOL = int(opts["--max-solutions"])
SEED_DIRS = [d for d in opts["--seed-dirs"].split(",") if d]
CORES = WORKD / "cores.txt"
LEG_RE = re.compile(r"min_adds(>?=)(\d+)")
EQS = list(brent_equations(3, 3, 3, 23))


# --- rows and the symmetry maps -------------------------------------------
# A row is a 9-bit int, bit (8-k) = entry k of the row-major 3x3 block.

def to_mat(v):
    return [[(v >> (8 - (3 * i + j))) & 1 for j in range(3)] for i in range(3)]


def to_row(M):
    return sum(M[i][j] << (8 - (3 * i + j)) for i in range(3) for j in range(3))


def mul(X, Y):
    return [[sum(X[i][t] & Y[t][j] for t in range(3)) & 1 for j in range(3)]
            for i in range(3)]


def det(P):
    return (P[0][0] & (P[1][1] & P[2][2] ^ P[1][2] & P[2][1])
            ^ P[0][1] & (P[1][0] & P[2][2] ^ P[1][2] & P[2][0])
            ^ P[0][2] & (P[1][0] & P[2][1] ^ P[1][1] & P[2][0]))


def build_maps():
    gl = [to_mat(v) for v in range(512) if det(to_mat(v))]
    eye = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
    maps = set()
    for P in gl:
        Pi = next(Q for Q in gl if mul(P, Q) == eye)
        conj = [to_row(mul(mul(P, to_mat(v)), Pi)) for v in range(512)]
        maps.add(tuple(conj))
        maps.add(tuple(to_row([list(r) for r in zip(*to_mat(conj[v]))])
                       for v in range(512)))
    assert len(maps) == 336, len(maps)
    return [list(m) for m in maps]


MAPS = build_maps()


def images(core):
    """Distinct bitmasks (over row values) of the core's 336 images."""
    return {sum(1 << M[v] for v in core) for M in MAPS}


def mask(rows):
    return sum(1 << v for v in rows)


def rank9(rows):
    basis = []
    for v in rows:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
    return len(basis)


# --- schemes ----------------------------------------------------------------

def brent_ok(bits):
    for mons, rhs in EQS:
        acc = 0
        for (x, y, z) in mons:
            acc ^= bits[x] & bits[y] & bits[z]
        if acc != rhs:
            return False
    return True


def arows(bits):
    return frozenset(v for v in (int("".join(map(str, bits[9 * m:9 * m + 9])), 2)
                                 for m in range(23)) if v)


# --- the cost oracle ----------------------------------------------------------

def fbmin_out(rows, flags, timeout=None):
    """fbmin's stdout, or None when it ran past `timeout` seconds."""
    with tempfile.NamedTemporaryFile("w", suffix=".legs", dir=WORKD / "tmp",
                                     delete=False) as f:
        f.write("\n".join(format(v, "09b") for v in sorted(rows)) + "\n")
        path = f.name
    try:
        return subprocess.run([FBMIN, *flags, "--threads", "1", path],
                              capture_output=True, text=True, timeout=timeout).stdout
    except subprocess.TimeoutExpired:
        return None
    finally:
        os.unlink(path)


def leg_ge(rows, need, timeout=None):
    """True iff fbmin proves the leg cost of `rows` is >= need (within
    `timeout` seconds, when given; running out counts as not proved)."""
    slack = need - (len(rows) - 9)
    if slack <= 0:
        return True
    if slack >= 4 or rank9(rows) < 9:
        return False
    flags = {1: ["--tier1-only"], 2: [], 3: ["--tier3"]}[slack]
    out = fbmin_out(rows, flags, timeout)
    if out is None:
        return False
    m = LEG_RE.search(out)
    if not m:
        raise RuntimeError(f"fbmin gave no verdict on {sorted(rows)}")
    return int(m.group(2)) >= need


def exact_or_bound(rows):
    m = LEG_RE.search(fbmin_out(rows, ["--tier3"]))
    return (m.group(1) == "="), int(m.group(2))


def extract_cores(S, pool):
    """Minimal-by-greedy subsets of S that provably cost >= NEED."""
    found = []
    cur = sorted(S)
    while len(cur) - 1 >= NEED + 6:
        cands = [tuple(x for x in cur if x != r) for r in cur]
        good = [c for c, ok in zip(cands, pool.map(lambda c: leg_ge(c, NEED, CORE_TO),
                                                   cands)) if ok]
        if not good:
            break
        found.extend(good)
        cur = list(good[0])
    if not found:
        found = [tuple(sorted(S))]
    found.sort(key=len)
    keep = []
    for c in found:
        mc = mask(c)
        if not any((mask(k) & mc) == mask(k) for k in keep):
            keep.append(c)
    return keep


def publish(cores, src):
    with open(CORES, "a") as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        for c in cores:
            f.write("core " + " ".join(map(str, c)) + f" | {src}\n")
        f.flush()
        fcntl.flock(f, fcntl.LOCK_UN)


# --- a worker -----------------------------------------------------------------

def finish(wi, say, kind, text):
    with open(WORKD / "RESULT", "a") as f:
        f.write(f"{kind} worker={wi} {text}\n")
    (WORKD / "DONE").touch()
    say(f"{kind}: {text}")


def stopped():
    return (WORKD / "DONE").exists() or (WORKD / "STOP").exists()


def run_server(wi, lex, pin, tag, say, pool):
    """One solver: load every shared core, then propose / verify / block
    until UNSAT.  Returns ("UNSAT", text) for that formula, or None after
    a global finish (KLAXON, UNDECIDED, ERROR) or a stop."""
    cmd = [BIN, CNF, MAPF, "--dmax", str(L + 9), "--seed", str(wi + 1),
           "--shuffle", str(wi + 1)]
    if not lex:
        cmd.append("--no-lex")
    if pin:
        cmd += ["--pin", pin]
    log = open(WORKD / f"w{wi:02d}.log", "a", buffering=1)
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                            stderr=log, text=True, bufsize=1)

    def ask(line):
        proc.stdin.write(line + "\n")
        proc.stdin.flush()
        return proc.stdout.readline().strip()

    blocked = set()
    offset = 0

    def send(core):
        n = 0
        for img in images(core):
            if img in blocked:
                continue
            blocked.add(img)
            rows = [v for v in range(512) if img >> v & 1]
            assert ask("block " + " ".join(map(str, rows))) == "ok"
            n += 1
        return n

    def sync():
        nonlocal offset
        n = 0
        with open(CORES, "rb") as f:
            f.seek(offset)
            data = f.read()
        end = data.rfind(b"\n") + 1
        offset += end
        for ln in data[:end].decode().splitlines():
            if ln.startswith("core "):
                n += send(tuple(int(t) for t in ln.split("|")[0].split()[1:]))
        return n

    nsol = 0
    t_start = time.time()
    t_solve = 0.0
    nb = 0
    result = None
    try:
        while not stopped():
            nb += sync()
            t0 = time.time()
            r = ask(f"solve {BUDGET:.0f}")
            t_solve += time.time() - t0
            if r == "s UNKNOWN":
                say(f"{tag}budget spent ({t_solve:.0f}s in this solve so far), "
                    f"{len(blocked)} blocks loaded; resuming")
                continue
            dt, t_solve = t_solve, 0.0
            if r == "s UNSAT":
                result = ("UNSAT", f"{tag}after {nsol} solutions, {len(blocked)} blocks "
                                   f"loaded, {time.time() - t_start:.0f}s")
                break
            if not r.startswith("b "):
                finish(wi, say, "ERROR", f"{tag}solver said {r!r}")
                break
            bits = [int(c) for c in r[2:]]
            nsol += 1
            assert brent_ok(bits), "solution fails full Brent"
            S = arows(bits)
            sm = mask(S)
            assert len(S) <= L + 9, f"d={len(S)} exceeds dmax"
            assert rank9(S) == 9, "A-rows do not span"
            assert not any((b & sm) == b for b in blocked), "solution contains a blocked core"
            name = f"w{wi:02d}-{tag.strip().replace(' ', '').rstrip(':')}-{nsol:05d}.bits" \
                if tag else f"w{wi:02d}-{nsol:05d}.bits"
            sched = WORKD / "schemes" / name
            sched.write_text("".join(map(str, bits)) + "\n")
            if not leg_ge(S, NEED):
                exact, a = exact_or_bound(S)
                if exact and a <= L:
                    finish(wi, say, "KLAXON",
                           f"A-leg {a} (per-step {3 * a + 14}) d={len(S)} -> {sched}")
                    break
                if not exact or a < NEED:
                    finish(wi, say, "UNDECIDED",
                           f"leg {'=' if exact else '>='}{a} d={len(S)} -> {sched}")
                    break
            t1 = time.time()
            cores = extract_cores(S, pool)
            publish(cores, f"w{wi} {tag}sol{nsol} d={len(S)}")
            nown = sum(send(c) for c in cores)
            say(f"{tag}sol {nsol}: d={len(S)} solve {dt:.0f}s, cores "
                f"{[len(c) for c in cores]} ({time.time() - t1:.0f}s), "
                f"+{nb} shared/+{nown} own blocks, {len(blocked)} total")
            nb = 0
            if MAXSOL and nsol >= MAXSOL:
                say("max solutions reached")
                break
    finally:
        proc.stdin.close()
        proc.kill()
    return result


def worker(wi, seed_files, cubeq):
    log = open(WORKD / f"w{wi:02d}.log", "a", buffering=1)

    def say(msg):
        log.write(time.strftime("%H:%M:%S ") + msg + "\n")

    pool = ThreadPoolExecutor(NT)
    lex = cubeq is not None or wi - WOFF < NLEX
    say(f"start: {'lex' if lex else 'no-lex'}, {len(seed_files)} seed schemes"
        + (", cube mode" if cubeq is not None else ""))
    done_seeds = {ln.split("| seed ")[1].split()[0] for ln in open(CORES)
                  if "| seed " in ln}
    for path in seed_files:
        tag = "/".join(path.split("/")[-2:])
        if tag in done_seeds:
            continue
        bits = [int(c) for c in open(path).read().strip()]
        assert len(bits) == 621 and brent_ok(bits), path
        S = arows(bits)
        if not leg_ge(S, NEED):
            say(f"seed {path}: not provably >= {NEED}, skipped")
            continue
        cores = extract_cores(S, pool)
        publish(cores, f"seed {tag} d={len(S)}")
        say(f"seed {tag} d={len(S)}: cores {[len(c) for c in cores]}")

    if cubeq is None:
        res = run_server(wi, lex, PIN, "", say, pool)
        if res:
            finish(wi, say, *res)
        return
    while not stopped():
        try:
            idx, a, b = cubeq.get_nowait()
        except queue.Empty:
            break
        base = open(PIN).read().strip() if PIN else "-" * 207
        pat = base[:189] + format(a, "09b") + format(b, "09b")
        pin = WORKD / "tmp" / f"cube{idx:03d}.pin"
        pin.write_text(pat + "\n")
        res = run_server(wi, True, str(pin), f"cube {idx}: ", say, pool)
        if res is None:
            break
        with open(CUBES_DONE, "a") as f:
            fcntl.flock(f, fcntl.LOCK_EX)
            f.write(f"{idx} {a} {b} UNSAT {res[1]}\n")
            fcntl.flock(f, fcntl.LOCK_UN)
        say(f"cube {idx} ({a},{b}) UNSAT")


if __name__ == "__main__":
    for sub in ("tmp", "schemes"):
        (WORKD / sub).mkdir(parents=True, exist_ok=True)
    CORES.touch()
    for f in ("DONE",):
        (WORKD / f).unlink(missing_ok=True)
    seeds, seen = [], set()
    for path in sorted(str(p) for d in SEED_DIRS for p in pathlib.Path(d).glob("sym-*.bits")):
        S = arows([int(c) for c in open(path).read().strip()])
        key = min(tuple(sorted(M[v] for v in S)) for M in MAPS)
        if key not in seen:
            seen.add(key)
            seeds.append(path)
    print(f"symcegar: leg <= {L} (dmax {L + 9}), {NW} workers ({NLEX} lex) x {NT} fbmin threads, "
          f"{len(seeds)} seed schemes, {len(MAPS)} symmetry maps, pin={PIN or '-'}",
          flush=True)
    cubeq = None
    if CUBES:
        reps = [tuple(map(int, ln.split())) for ln in open(CUBES) if ln.strip()]
        CUBES_DONE.touch()
        done = {int(ln.split()[0]) for ln in open(CUBES_DONE) if ln.strip()}
        cubeq = mp.Queue()
        for i, (a, b) in enumerate(reps):
            if i not in done:
                cubeq.put((i, a, b))
        print(f"cube mode: {len(reps)} cubes, {len(done)} already UNSAT", flush=True)
    procs = [mp.Process(target=worker, args=(w + WOFF, seeds[w::NW], cubeq))
             for w in range(NW)]
    for p in procs:
        p.start()
    for p in procs:
        p.join()
    if CUBES and not (WORKD / "DONE").exists():
        done = {int(ln.split()[0]) for ln in open(CUBES_DONE) if ln.strip()}
        if len(done) == len(reps):
            with open(WORKD / "RESULT", "a") as f:
                f.write(f"UNSAT all {len(reps)} cubes (fixed-pair orbits) UNSAT\n")
            (WORKD / "DONE").touch()
    res = (WORKD / "RESULT").read_text() if (WORKD / "RESULT").exists() else "no result"
    print(res, flush=True)
