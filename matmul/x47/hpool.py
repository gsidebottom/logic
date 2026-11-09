#!/usr/bin/env python3
"""Worker pool over the orbit shapes of hcnf.py's sandwich-group quotient at rank r (default 47): each job is
(shape, solver, seed) with a wall cap; shapes are visited most-constrained first (fewest free variables) and revisited
with fresh seeds, cadical and kissat alternating.  SAT models are decoded and checked against all 4096 Brent
equations (hcnf.decode) and saved as OUTDIR/sol_*.bits; an UNSAT verdict settles the shape.  Orbit types use one
subgroup per conjugacy class of the group.
Usage: hpool.py OUTDIR [--group d8] [--rank 47] [--workers 12] [--cap 1200] [--hours 8] [--max-shapes 400]
"""
import sys, pathlib, itertools, argparse, time, threading, subprocess, concurrent.futures as cf
HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import hcnf  # noqa: E402

def conj_classes(G, subs):
    classes = []
    seen = set()
    for i, K in enumerate(subs):
        if i in seen: continue
        cl = {i}
        for g in G:
            # g K g^-1
            ginv = next(h for h in G if hcnf.gcomp(g, h) == tuple((0,1,2,3) for _ in range(3)))
            Kc = tuple(sorted(hcnf.gcomp(hcnf.gcomp(g, k), ginv) for k in K))
            for j, K2 in enumerate(subs):
                if tuple(sorted(K2)) == Kc: cl.add(j)
        seen |= cl; classes.append(sorted(cl))
    return classes

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out"); ap.add_argument("--group", default="d8"); ap.add_argument("--rank", type=int, default=47)
    ap.add_argument("--workers", type=int, default=12); ap.add_argument("--cap", type=int, default=1200)
    ap.add_argument("--hours", type=float, default=8); ap.add_argument("--max-shapes", type=int, default=400); ap.add_argument("--min-full", type=int, default=3)
    args = ap.parse_args()
    G = hcnf.GROUPS[args.group]; subs = hcnf.subgroups(G); n = len(G)
    classes = conj_classes(G, subs); reps = [c[0] for c in classes]
    sizes = [n // len(subs[k]) for k in reps]
    out = pathlib.Path(args.out); (out / "cnf").mkdir(parents=True, exist_ok=True)
    # all shapes: counts per class with sum count*size = rank
    shapes = []
    def rec(i, left, cur):
        if i == len(reps):
            if left == 0: shapes.append(tuple(cur))
            return
        for c in range(left // sizes[i] + 1):
            rec(i + 1, left - c * sizes[i], cur + [c])
    rec(0, args.rank, [])
    # order: most full orbits first (the 262's 48 layers are six free 8-orbits), then fewest orbits, then fewest fixed products
    shapes = [s for s in shapes if s[0] >= args.min_full]
    shapes.sort(key=lambda s: (-s[0], sum(s), s[-1], s))
    shapes = shapes[: args.max_shapes]
    def shape_list(s): return [(k, c) for k, c in zip(reps, s) if c]
    deadline = time.time() + args.hours * 3600
    lock = threading.Lock(); settled = set(); solved = set()
    log = open(out / "pool.log", "a", buffering=1)
    def say(msg):
        with lock:
            log.write(time.strftime("%H:%M:%S ") + msg + "\n"); print(time.strftime("%H:%M:%S ") + msg, flush=True)
    say(f"group {args.group} order {n}; subgroup classes {[(k, len(subs[k])) for k in reps]} orbit sizes {sizes}; {len(shapes)} shapes at rank {args.rank}")
    def cnf_for(s):
        f = out / "cnf" / ("h_" + "_".join(map(str, s)) + ".cnf")
        with lock:
            if not f.exists():
                hcnf.write_cnf(G, shape_list(s), str(f))
        return f
    def job(s, solver, seed):
        if time.time() > deadline or s in settled or s in solved: return
        f = cnf_for(s)
        if open(f).readline().startswith("c structurally UNSAT"):
            settled.add(s); say(f"UNSAT shape {s} (structural)"); return
        tag = "_".join(map(str, s)) + f"_{solver[0]}{seed}"
        res = out / f"run_{tag}.out"
        cap = int(min(args.cap, max(1, deadline - time.time())))
        t0 = time.time()
        with open(res, "w") as fh:
            rc = subprocess.run(["timeout", str(cap), solver, f"--seed={seed}", "-q", str(f)], stdout=fh, stderr=subprocess.STDOUT).returncode
        dt = time.time() - t0
        if rc == 10:
            bits = out / f"sol_{tag}.bits"
            try:
                r, nd = hcnf.decode(G, shape_list(s), str(res), str(bits))
                solved.add(s); say(f"SAT shape {s} by {solver} seed {seed} in {dt:.0f}s -> {bits.name} (rank {r}, {nd} distinct products, Brent verified)")
            except SystemExit as e:
                say(f"DECODE FAILURE shape {s} {solver} seed {seed}: {e}")
        elif rc == 20:
            settled.add(s); say(f"UNSAT shape {s} by {solver} seed {seed} in {dt:.0f}s"); res.unlink()
        else:
            say(f"timeout shape {s} {solver} seed {seed} ({dt:.0f}s)"); res.unlink()
    def jobs():
        for rnd in itertools.count():
            solver = "cadical" if rnd % 2 == 0 else "kissat"
            for s in shapes: yield s, solver, 100 + rnd
    with cf.ThreadPoolExecutor(args.workers) as ex:
        pending = set()
        for item in jobs():
            if time.time() > deadline or len(settled) + len(solved) == len(shapes): break
            if item[0] in settled or item[0] in solved: continue
            while len(pending) >= args.workers:
                done, pending = cf.wait(pending, return_when=cf.FIRST_COMPLETED)
            pending.add(ex.submit(job, *item))
        cf.wait(pending)
    say(f"pool done: {len(settled)} shapes UNSAT, {len(solved)} shapes SAT, {len(shapes) - len(settled) - len(solved)} open")
if __name__ == "__main__":
    main()
