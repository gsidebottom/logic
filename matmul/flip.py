#!/usr/bin/env python3
"""Flip-graph walk over mod-2 matrix-multiplication schemes
(Kauers-Moosbauer, arXiv:2212.01175), with a sign-SAT liftability
lottery on every new scheme.

The flip move: two rank-1 summands sharing a factor in the same slot,
    a (x) b (x) c   and   a (x) b' (x) c',
rewrite (validity-preserving, checked here by construction AND by the
Brent verifier on every emitted scheme):
    a (x) (b+b') (x) c   and   a (x) b' (x) (c+c').
Analogous moves for a shared middle or last factor. If any summand's
factor becomes ZERO the summand vanishes: RANK REDUCTION (r -> r-1) —
at 4x4x4 r=47 that would be rank 46, an open-problem event, saved and
announced loudly.

Every new distinct-after-summand-sort scheme is (optionally, default on)
sign-SAT lift-tested: a liftable 4x4x4-47 scheme would beat the rank-48
record over Z. Any LIFTED result is saved and announced loudly.

Usage:
  python3 flip.py --dims 4,4,4,47 --seeds seeds4 --archive found4f
                  [--minutes 30] [--lift-every 1] [--rng 1]
"""
import argparse
import glob
import os
import random
import sys
import time

from brent import var_counts, verify_bits
from canon import canon_key
from lift import lift, z_verify


def load(path, dims):
    s = open(path).read().split()[-1].strip()
    bits = [int(c) for c in s]
    assert verify_bits(bits, *dims) == 0, f"{path} does not verify"
    return bits


def to_summands(bits, dims):
    """list of (a,b,c) factor bitmasks (sa,sb,sg bits each)."""
    n1, n2, n3, r = dims
    na, nb, ng = var_counts(*dims)
    sa, sb, sg = n1 * n2, n2 * n3, n1 * n3
    out = []
    for m in range(r):
        a = b = g = 0
        for k in range(sa):
            a |= bits[m * sa + k] << k
        for k in range(sb):
            b |= bits[na + m * sb + k] << k
        for k in range(sg):
            g |= bits[na + nb + m * sg + k] << k
        out.append([a, b, g])
    return out


def to_bits(summ, dims):
    n1, n2, n3, r = dims
    na, nb, ng = var_counts(*dims)
    sa, sb, sg = n1 * n2, n2 * n3, n1 * n3
    bits = [0] * (na + nb + ng)
    for m, (a, b, g) in enumerate(summ):
        for k in range(sa):
            bits[m * sa + k] = (a >> k) & 1
        for k in range(sb):
            bits[na + m * sb + k] = (b >> k) & 1
        for k in range(sg):
            bits[na + nb + m * sg + k] = (g >> k) & 1
    return bits


def random_flip(summ, rng, allow_zero=False):
    """apply one random flip in place; drops zeroed summands.
    With allow_zero=False, zero-producing flips (which reduce the rank —
    including the trivial undo of a fresh split) are skipped: exploration
    diffuses material instead of annihilating it. Returns 'flip',
    'reduce', or None."""
    r = len(summ)
    for _ in range(64):
        slot = rng.randrange(3)
        i = rng.randrange(r)
        j = rng.randrange(r)
        if i == j or summ[i][slot] != summ[j][slot] or summ[i][slot] == 0:
            continue
        o1, o2 = [x for x in (0, 1, 2) if x != slot]
        if rng.random() < 0.5:
            o1, o2 = o2, o1
        would_zero = (summ[i][o1] == summ[j][o1]
                      or summ[i][o2] == summ[j][o2])
        if would_zero and not allow_zero:
            continue
        summ[i][o1] ^= summ[j][o1]
        summ[j][o2] ^= summ[i][o2]
        if 0 in summ[i] or 0 in summ[j]:
            summ[:] = [s for s in summ if 0 not in s]
            return "reduce"
        return "flip"
    return None


def seek_reduction(summ, rng, attempts=200):
    """actively look for a zero-producing flip (rank -1). Returns True
    if a reduction fired."""
    for _ in range(attempts):
        if random_flip(summ, rng, allow_zero=True) == "reduce":
            return True
    return False


def split(summ, rng, dims):
    """plus-transition (rank +1): replace a x b x c by
    a' x b x c  +  (a+a') x b x c. Crucially a' is chosen as ANOTHER
    summand's factor in that slot, so the child immediately shares a
    factor with an existing (non-twin) summand — twin-only sharing is
    sterile (every twin flip is zero-producing, so nothing diffuses)."""
    n1, n2, n3, _ = dims
    sizes = (n1 * n2, n2 * n3, n1 * n3)
    for _ in range(64):
        m = rng.randrange(len(summ))
        k = rng.randrange(len(summ))
        slot = rng.randrange(3)
        f = summ[m][slot]
        x = summ[k][slot]
        if k == m or x == f or x == 0 or f == 0:
            continue
        child = list(summ[m])
        summ[m][slot] = x
        child[slot] = f ^ x
        summ.append(child)
        return
    # fallback: random factor
    m = rng.randrange(len(summ))
    slot = rng.randrange(3)
    f = summ[m][slot]
    while True:
        x = rng.randrange(1, 1 << sizes[slot])
        if x != f:
            break
    child = list(summ[m])
    summ[m][slot] = x
    child[slot] = f ^ x
    summ.append(child)


def descend(args, dims, seeds, pool, rng, t0):
    """KM discovery pipeline: from a high-rank seed, greedily seek
    reductions (with flip diffusion between attempts); save, canon-dedupe
    and lift-test every landing at rank <= args.save_at; restart on
    stall. A landing below the known record rank is the jackpot."""
    n1, n2, n3, _ = dims
    from lift import lift as _lift
    from lift import pretty as _pretty
    from lift import z_verify as _zv
    cur = to_summands(seeds[rng.randrange(len(seeds))], dims)
    best = len(cur)
    ntraj = nsaved = nlift = 0
    stats = {}
    stall = 0
    while time.time() - t0 < args.minutes * 60:
        if seek_reduction(cur, rng, attempts=800):
            stall = 0
            rk = len(cur)
            if rk <= args.save_at:
                d2 = (n1, n2, n3, rk)
                bits = to_bits(cur, d2)
                if verify_bits(bits, *d2) != 0:
                    print("DESCEND BUG: invalid scheme", flush=True)
                    cur = to_summands(
                        seeds[rng.randrange(len(seeds))], dims)
                    continue
                k = canon_key(bits, *d2)
                if k not in pool:
                    pool[k] = 1
                    nsaved += 1
                    stats[rk] = stats.get(rk, 0) + 1
                    out = f"{args.archive}/r{rk}-{stats[rk]:05d}.bits"
                    open(out, "w").write("".join(map(str, bits)) + "\n")
                    if rk <= 48 and args.lift_every:
                        nlift += 1
                        res = _lift(bits, d2)
                        if res is not None:
                            signs, _ = res
                            assert _zv(bits, signs, d2) == 0
                            lout = out.replace(".bits", ".LIFTED.txt")
                            open(lout, "w").write(
                                _pretty(bits, signs, out, d2))
                            print("!" * 60 + f"\nLIFTABLE rank-{rk} "
                                  f"SCHEME over Z -> {lout}\n" + "!" * 60,
                                  flush=True)
                    if rk < 47:
                        print("!" * 60 + f"\nRANK {rk} < 47 REACHED -> "
                              f"{out}\n" + "!" * 60, flush=True)
            if rk < best:
                best = rk
                print(f"[{time.time()-t0:6.0f}s] new min rank {best} "
                      f"(traj {ntraj})", flush=True)
        else:
            for _ in range(rng.randrange(100, 600)):
                random_flip(cur, rng)
            stall += 1
            if stall > 12:
                ntraj += 1
                cur = to_summands(
                    seeds[rng.randrange(len(seeds))], dims)
                stall = 0
    print(f"descend done: {nsaved} schemes saved at rank<={args.save_at} "
          f"{dict(sorted(stats.items()))}, {nlift} lift-tested, "
          f"{ntraj} trajectories, min rank {best}", flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dims", default="4,4,4,47")
    ap.add_argument("--seeds", default="seeds4")
    ap.add_argument("--archive", default="found4f")
    ap.add_argument("--minutes", type=float, default=30.0)
    ap.add_argument("--kick", type=int, default=20,
                    help="flips between dedupe/lift checkpoints")
    ap.add_argument("--max-excess", type=int, default=8,
                    help="rank excursion above target (plus-transitions)")
    ap.add_argument("--hard-excess", type=int, default=14,
                    help="absolute excursion cap before restart")
    ap.add_argument("--p-split", type=float, default=0.05,
                    help="probability of a plus-transition per move")
    ap.add_argument("--restart-every", type=int, default=400,
                    help="checkpoints before restarting from a random seed")
    ap.add_argument("--descend", action="store_true",
                    help="KM discovery mode: reduction-greedy descent from "
                    "high-rank seeds (e.g. trivial-64); saves + lift-tests "
                    "every distinct scheme at rank <= --save-at")
    ap.add_argument("--save-at", type=int, default=49)
    ap.add_argument("--lift-every", type=int, default=1,
                    help="lift-test every Nth new scheme (1 = all)")
    ap.add_argument("--rng", type=int, default=1)
    args = ap.parse_args()
    dims = tuple(int(x) for x in args.dims.split(","))
    n1, n2, n3, r = dims

    os.makedirs(args.archive, exist_ok=True)
    rng = random.Random(args.rng)
    pool = {}
    for p in sorted(glob.glob(f"{args.seeds}/*.bits")) + \
            sorted(glob.glob(f"{args.archive}/*.bits")):
        bits = load(p, dims)
        pool[canon_key(bits, *dims)] = p
    print(f"flip walk: dims {dims}, pool {len(pool)}, "
          f"{args.minutes} min", flush=True)

    seeds = [load(p, dims) for p in sorted(glob.glob(f"{args.seeds}/*.bits"))]
    cur = to_summands(seeds[rng.randrange(len(seeds))], dims)
    t0 = time.time()
    nflip = nnew = nlift = nred = ncheck = nsplit = ndup = 0

    if args.descend:
        descend(args, dims, seeds, pool, rng, t0)
        return

    while time.time() - t0 < args.minutes * 60:
        # phase 1: go up (split) and diffuse (non-destructive flips)
        while len(cur) - r < args.max_excess:
            split(cur, rng, dims)
            nsplit += 1
            diffuse = rng.randrange(40, args.kick * 20)
            for _ in range(diffuse):
                if random_flip(cur, rng) == "flip":
                    nflip += 1
        # phase 2: descend to target; on stall, split-diffuse further
        # (up to the hard cap), else restart from a seed
        stalled = False
        while len(cur) > r:
            if seek_reduction(cur, rng, attempts=400):
                nred += 1
                for _ in range(rng.randrange(10, 80)):
                    if random_flip(cur, rng) == "flip":
                        nflip += 1
            elif len(cur) - r < args.hard_excess:
                split(cur, rng, dims)
                nsplit += 1
                for _ in range(rng.randrange(40, 200)):
                    if random_flip(cur, rng) == "flip":
                        nflip += 1
            else:
                stalled = True
                break
        if stalled:
            cur = to_summands(seeds[rng.randrange(len(seeds))], dims)
            continue
        if len(cur) > r:
            continue
        if len(cur) < r:
            # below target rank: an open-problem event at 4x4x47
            rb = to_bits(cur, (n1, n2, n3, len(cur)))
            bad = verify_bits(rb, n1, n2, n3, len(cur))
            out = f"{args.archive}/RANK{len(cur)}-{nred}.bits"
            open(out, "w").write("".join(map(str, rb)) + "\n")
            print("!" * 60 + f"\nRANK BELOW TARGET: {len(cur)} < {r} "
                  f"(verify {bad} violated) -> {out}\n" + "!" * 60,
                  flush=True)
            cur = to_summands(seeds[rng.randrange(len(seeds))], dims)
            continue
        ncheck += 1
        bits = to_bits(cur, dims)
        if verify_bits(bits, *dims) != 0:
            print("FLIP BUG: invalid scheme, restarting", flush=True)
            cur = to_summands(seeds[rng.randrange(len(seeds))], dims)
            continue
        k = canon_key(bits, *dims)
        if k in pool:
            ndup += 1
        if k not in pool:
            nnew += 1
            out = f"{args.archive}/flip-{nnew:06d}.bits"
            open(out, "w").write("".join(map(str, bits)) + "\n")
            pool[k] = out
            if args.lift_every and nnew % args.lift_every == 0:
                res = lift(bits, dims)
                nlift += 1
                if res is not None:
                    signs, _ = res
                    assert z_verify(bits, signs, dims) == 0
                    lout = out.replace(".bits", ".LIFTED-RECORD.txt")
                    from lift import pretty
                    open(lout, "w").write(
                        pretty(bits, signs, out, dims))
                    print("!" * 60 + f"\nLIFTABLE rank-{r} SCHEME over Z"
                          f" -> {lout}\n" + "!" * 60, flush=True)
            if nnew % 200 == 0:
                el = time.time() - t0
                print(f"[{el:6.0f}s] {nnew} new, {nlift} lift-tested, "
                      f"{nred} reductions, {nsplit} splits, {nflip} flips",
                      flush=True)
        if ncheck % args.restart_every == 0:
            cur = to_summands(seeds[rng.randrange(len(seeds))], dims)
    el = time.time() - t0
    print(f"done: {nnew} new schemes at rank {r} ({ncheck} checkpoints, "
          f"{ndup} dups), {nlift} lift-tested, {nred} reductions, "
          f"{nsplit} splits, {nflip} flips in {el:.0f}s", flush=True)


if __name__ == "__main__":
    main()
