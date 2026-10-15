#!/usr/bin/env python3
"""Design-first 50-hunt: enumerate the structure a sub-51 scheme MUST
have, then search for schemes realizing it.

A per-step total T = sum of leg minima + 14, and a leg at its floor
d-9 provably has every row in an internal addition triple.  Writing
f = sum(d) - 13 for the per-step floor, T = 50 needs total slack
50 - f: all-floor legs give T = f, so any realizable all-floor design
at sum(d) <= 63 beats or ties 50 (61 -> 48!, 62 -> 49, 63 -> 50).

Stage 1 (design sampling): a floor-achieving leg IS a waste-free
closure -- 9 independent generators (WLOG unit vectors, by the GL
action) plus d-9 pairwise XOR sums, all distinct, with every
generator parenting at least one sum (isolation 0).  Sample such a
DAG, then a surjection of the 23 products onto its d nodes.

Stage 2 (realization search): freeze the A-side to the instantiated
design (207 bits) via anf --freeze-file and let the native-ANF SLS +
tri-linear closure search for B, C satisfying Brent.  Any solution is
a scheme whose A-leg is AT ITS FLOOR and triple-saturated by
construction; its B/C legs land free and are screened as usual
(mint-style stats), with the exact tiers reserved for keepers.

Stage 2 comes in two modes.  --mode a freezes the A design (207
bits) and warm-starts B/C from a rotating donor scheme (--donors dir;
the engine's --init-file + WalkSAT close-repair: the control completes
a known frozen A in milliseconds where cold-start fails at 80 s).
--mode ab freezes A and B designs (414 bits): Brent is then LINEAR in
C, and the closure hook decides the completion near-instantly -- any
solve hands us the C leg to screen.

Usage: design50.py workdir anf-binary [--trials N] [--dA D] [--dB D]
         [--seconds S] [--threads T] [--mult MAX] [--mode a|ab]
         [--donors dir] [--mutate-cert cert --mutate-bits scheme.bits
         --mutations K]

--mutate-cert seeds the design sampler from a KNOWN floor-achieving
leg: the fbmin certificate's basis+adds DAG is re-coordinatized over
unit generators (GL-invariance), the scheme's A-block supplies the
product->node multiplicity, and each trial applies K random DAG
mutations (re-parent a sum / move a duplicate product), keeping
distinctness and triple saturation.  Design-space walk around a
realizable design instead of uniform sampling.
Stop: touch <workdir>/STOP.
"""
import pathlib
import random
import subprocess
import sys
import time

args = sys.argv[1:]
flags = {"--trials": 200, "--dA": 20, "--dB": 20, "--seconds": 30.0,
         "--threads": 2, "--mult": 4, "--mode": "a", "--donors": "",
         "--mutate-cert": "", "--mutate-bits": "", "--mutations": 2}
pos = []
i = 0
while i < len(args):
    if args[i] in flags:
        cast = type(flags[args[i]])
        flags[args[i]] = cast(args[i + 1])
        i += 2
    else:
        pos.append(args[i])
        i += 1
WORK, ANF = pathlib.Path(pos[0]), pos[1]
WORK.mkdir(parents=True, exist_ok=True)
RES = WORK / "design_results.csv"
if not RES.exists():
    RES.write_text("trial,dA,solved,secs,best,bits\n")


def sample_design(d, rng):
    """Waste-free triple-saturated closure: 9 unit generators plus
    d-9 distinct pairwise sums, every generator a parent."""
    gens = [1 << k for k in range(9)]
    for _ in range(400):
        nodes = list(gens)
        unparented = set(gens)
        ok = True
        for step in range(d - 9):
            # bias toward covering unparented generators first
            need = [g for g in nodes if g in unparented]
            for _ in range(200):
                x = rng.choice(need) if need and rng.random() < 0.8 \
                    else rng.choice(nodes)
                y = rng.choice(nodes)
                z = x ^ y
                if z and z not in nodes:
                    nodes.append(z)
                    unparented.discard(x)
                    unparented.discard(y)
                    break
            else:
                ok = False
                break
        if ok and not unparented:
            return nodes
    return None


def assign_products(nodes, rng, maxmult):
    """Surjection of 23 products onto the d nodes, multiplicity capped."""
    d = len(nodes)
    for _ in range(100):
        counts = [1] * d
        for _ in range(23 - d):
            j = rng.randrange(d)
            counts[j] += 1
        if max(counts) <= maxmult:
            rows = []
            for node, c in zip(nodes, counts):
                rows.extend([node] * c)
            rng.shuffle(rows)
            return rows
    return None


def freeze_lines(rows, off=0):
    out = []
    for m, r in enumerate(rows):
        for c in range(9):
            out.append(f"{off + m * 9 + c} {(r >> c) & 1}")
    return "\n".join(out) + "\n"


def parse_cert(path):
    """fbmin cert -> (DAG over generator indices, in emission order).
    Returns nodes as frozensets of generator indices (coordinates)."""
    basis, adds = [], []
    for ln in pathlib.Path(path).read_text().splitlines():
        ln = ln.strip()
        if ln.startswith("basis:"):
            basis = ln.split()[1:]
        elif ln.startswith("add "):
            _, x, _, y, _, z = ln.split()
            adds.append((x, y, z))
    coords = {b: frozenset([i]) for i, b in enumerate(basis)}
    order = []
    for x, y, z in adds:
        coords[z] = coords[x] ^ coords[y]
        order.append((coords[x], coords[y]))
    return coords, order


def dag_nodes(order):
    """Rebuild node set (as generator-coordinate frozensets) from the
    parent list; returns None on a collision/zero."""
    nodes = [frozenset([i]) for i in range(9)]
    seen = set(nodes)
    for x, y in order:
        z = x ^ y
        if not z or z in seen or x not in seen or y not in seen:
            return None
        nodes.append(z)
        seen.add(z)
    return nodes


def saturated(nodes):
    s = set(nodes)
    iso = set(nodes)
    for i, a in enumerate(nodes):
        for b in nodes[i + 1:]:
            c = a ^ b
            if c in s:
                iso -= {a, b, c}
    return not iso


def mutate_order(order, rng, k):
    """k random re-parentings; parents drawn from nodes earlier than
    the mutated position."""
    order = list(order)
    for _ in range(k):
        j = rng.randrange(len(order))
        pool = [frozenset([i]) for i in range(9)]
        nodes = dag_nodes(order[:j])
        if nodes is None:
            return None
        for _ in range(60):
            x, y = rng.choice(nodes), rng.choice(nodes)
            if x != y:
                order[j] = (x, y)
                if dag_nodes(order) is not None:
                    break
        else:
            return None
        _ = pool
    return order


def coords_to_int(c):
    v = 0
    for i in c:
        v |= 1 << i
    return v


rng = random.Random(20261014)
MUT = None
if flags["--mutate-cert"]:
    coords, base_order = parse_cert(flags["--mutate-cert"])
    bits = pathlib.Path(flags["--mutate-bits"]).read_text().split()[-1].strip()
    arows = [bits[9 * m: 9 * m + 9] for m in range(23)]
    # map each product's row string to node coordinates
    assign = []
    for r in arows:
        if r not in coords:
            sys.exit(f"product row {r} not covered by cert nodes")
        assign.append(coords[r])
    MUT = (base_order, assign)
    print(f"mutation seed: {len(base_order)} adds, "
          f"{len(set(assign))} distinct rows over 23 products", flush=True)
donors = []
if flags["--donors"]:
    donors = sorted(pathlib.Path(flags["--donors"]).glob("*.bits"))
solved = 0
for t in range(flags["--trials"]):
    if (WORK / "STOP").exists():
        print("STOP file present -- halting.", flush=True)
        break
    if MUT is not None:
        base_order, base_assign = MUT
        order = mutate_order(base_order, rng, flags["--mutations"])
        if order is None:
            continue
        nodes = dag_nodes(order)
        if nodes is None or not saturated(nodes):
            continue
        # keep the product->position multiplicity pattern; nodes moved
        old_nodes = dag_nodes(base_order)
        remap = dict(zip(old_nodes, nodes))
        rows = [coords_to_int(remap[a]) for a in base_assign]
    else:
        nodes = sample_design(flags["--dA"], rng)
        if nodes is None:
            continue
        nodes = [frozenset(i for i in range(9) if n >> i & 1)
                 for n in nodes]
        rows_f = assign_products([coords_to_int(n) for n in nodes],
                                 rng, flags["--mult"])
        if rows_f is None:
            continue
        rows = rows_f
    lines = freeze_lines(rows)
    if flags["--mode"] == "ab":
        nodesB = sample_design(flags["--dB"], rng)
        rowsB = assign_products(nodesB, rng, flags["--mult"]) if nodesB else None
        if rowsB is None:
            continue
        lines += freeze_lines(rowsB, off=207)
    fz = WORK / f"design_{t:04d}.freeze"
    fz.write_text(lines)
    cmd = [ANF, "3", "3", "3", "23", "--seconds", str(flags["--seconds"]),
           "--threads", str(flags["--threads"]),
           "--closure-every", "512" if flags["--mode"] == "ab" else "4096",
           "--freeze-file", str(fz), "--seed", str(1000 + t), "--quiet"]
    if flags["--mode"] == "a" and donors:
        cmd += ["--noise", "0.2", "--density", "0.05",
                "--init-file", str(donors[t % len(donors)])]
    else:
        cmd += ["--probsat", "--cb", "2.5", "--density", "0.10"]
    t0 = time.time()
    r = subprocess.run(cmd, capture_output=True, text=True)
    secs = time.time() - t0
    sol = None
    sat = False
    best = ""
    for ln in r.stdout.splitlines():
        if ln.startswith("s SATISFIABLE"):
            sat = True
        if ln.startswith("s UNKNOWN") and " best " in ln:
            best = ln.split(" best ")[1].split()[0]
        if ln.startswith("b "):
            tok = ln[2:].strip()
            if len(tok) == 621 and set(tok) <= {"0", "1"}:
                sol = tok
    hit = sat and sol is not None
    if hit:
        solved += 1
        out = WORK / f"design_{t:04d}.bits"
        out.write_text(sol + "\n")
        print(f"*** DESIGN-SOLVE trial {t} (dA={flags['--dA']}, "
              f"{secs:.0f} s) -> {out} ***", flush=True)
    with open(RES, "a") as f:
        f.write(f"{t},{flags['--dA']},{int(hit)},{secs:.1f},{best},"
                f"{'design_%04d.bits' % t if hit else ''}\n")
    fz.unlink()
    if t % 10 == 9:
        print(f"[{t + 1} trials, {solved} solves]", flush=True)
print(f"design50 pass done: {solved}/{flags['--trials']} solved.",
      flush=True)
