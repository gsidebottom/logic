#!/usr/bin/env python3
"""Mine box candidates out of the clauses a box-engine run kept failing on.

`sat -b boxes` with `BOXES_EFF_STUDY=1 BOXES_EFF_DUMP=<file>` writes every
clause that carried a conflict, with its count, whether it was learned, and
its LBD.  This groups those clauses into candidate boxes and scores each
one by the only thing that makes a box worth compiling:

    a box gives GAC on the CONJUNCTION of its clauses;
    unit propagation gives arc consistency on each clause SEPARATELY.

So the score is the gap: under a random partial assignment, how many
literals does the table force that unit propagation over the same clauses
does not (and how often does the table see a conflict UP misses).  A group
with no gap is a group whose clauses already propagate everything their
conjunction implies, and compiling it buys nothing however often the search
fails on it.

The competing cost is rows.  A tight group has few rows and propagates
hard; a loose one has close to 2^n rows and no power at all, so the row
budget is both the cost bound and the power filter.  Groups are therefore
grown greedily under a *variable* budget (rows are bounded by 2^n).

Usage:
    tools/mine_boxes.py dump.json [residual.cnf] [--vars 16] [--groups 8]
                                  [--samples 400]

Giving the CNF matters: the dump holds only conflict-carrying clauses, and
a table built from those alone is a weaker constraint than one built from
every clause over the same variables.  With the CNF, each candidate's table
is the models of *all* clauses inside its variable set.
"""
import json, sys, random, itertools


def load_dump(path):
    d = json.load(open(path))
    return d.get("conflicts", {}), d["clauses"]


def load_cnf(path):
    out = []
    for line in open(path):
        line = line.strip()
        if not line or line[0] in "cp%":
            continue
        lits = [int(t) for t in line.split()]
        if lits and lits[-1] == 0:
            lits.pop()
        if lits:
            out.append(lits)
    return out


def grow_groups(clauses, var_budget, n_groups):
    """Greedy: seed with the busiest clause, then keep adding the busiest
    clause that shares a variable and still fits the budget."""
    pool = sorted(clauses, key=lambda c: -c["conflicts"])
    used, groups = set(), []
    for _ in range(n_groups):
        seed = next((i for i, c in enumerate(pool)
                     if i not in used and len(set(map(abs, c["lits"]))) <= var_budget), None)
        if seed is None:
            break
        members, V = [seed], set(map(abs, pool[seed]["lits"]))
        used.add(seed)
        while True:
            best = None
            for i, c in enumerate(pool):
                if i in used:
                    continue
                cv = set(map(abs, c["lits"]))
                if not (cv & V) or len(V | cv) > var_budget:
                    continue
                best = i
                break            # pool is sorted, so the first fit is the busiest
            if best is None:
                break
            members.append(best)
            V |= set(map(abs, pool[best]["lits"]))
            used.add(best)
        groups.append((sorted(V), [pool[i] for i in members]))
    return groups


def masks(clauses, index):
    """Each clause as (pos, neg) bitmasks over the group's local indices."""
    out = []
    for lits in clauses:
        p = n = 0
        for l in lits:
            b = 1 << index[abs(l)]
            if l > 0:
                p |= b
            else:
                n |= b
        out.append((p, n))
    return out


def models(ms, n):
    """Every assignment over n variables satisfying all clauses, as ints."""
    full = (1 << n) - 1
    return [a for a in range(1 << n)
            if all((a & p) or (~a & full & q) for p, q in ms)]


def up_closure(ms, n, asg, val):
    """Unit propagation over the clause masks.  `asg`/`val` are bitmasks of
    assigned variables and their values.  Returns (asg, val, conflict)."""
    full = (1 << n) - 1
    changed = True
    while changed:
        changed = False
        for p, q in ms:
            # literals not yet falsified
            sat = (val & p) | (~val & full & q & asg)
            if sat & asg:
                continue                      # already satisfied
            free_p, free_q = p & ~asg, q & ~asg
            free = free_p | free_q
            if free == 0:
                return asg, val, True         # all literals false
            if free & (free - 1) == 0:        # exactly one free literal
                asg |= free
                if free & free_p:
                    val |= free
                changed = True
    return asg, val, False


def gac_closure(rows, n, asg, val):
    """The table's view: rows consistent with the assignment, then the
    literals every survivor agrees on."""
    full = (1 << n) - 1
    live = [r for r in rows if (r & asg) == (val & asg)]
    if not live:
        return asg, val, True
    ones = full
    zeros = full
    for r in live:
        ones &= r
        zeros &= ~r & full
    return asg | ones | zeros, val | ones, False


def score(rows, ms, n, samples, rng):
    """Mean extra literals GAC forces over UP, and how often it sees a
    conflict UP misses."""
    extra, extra_conf, wins = 0, 0, 0
    for _ in range(samples):
        k = rng.randrange(1, max(2, n // 2 + 1))
        picked = rng.sample(range(n), k)
        asg = val = 0
        for i in picked:
            asg |= 1 << i
            if rng.random() < 0.5:
                val |= 1 << i
        ua, uv, uc = up_closure(ms, n, asg, val)
        ga, gv, gc = gac_closure(rows, n, asg, val)
        if gc and not uc:
            extra_conf += 1
            wins += 1
            continue
        if uc:
            continue                      # UP already refuted it
        d = bin(ga & ~ua).count("1")
        if d:
            extra += d
            wins += 1
    return extra / samples, extra_conf / samples, wins / samples


def selftest(samples=2000):
    """Gate the scorer on a case whose answer is known.

    A full adder's gate CNF is the repo's own example of an encoding that
    loses propagation: the boxed adder refutes with zero conflicts where
    the gate clauses search.  So the scorer MUST report a gap here.  A
    scorer that reports zero everywhere would otherwise look like a
    discovery instead of a bug.
    """
    def AND(z, x, y): return [[-z, x], [-z, y], [z, -x, -y]]
    def OR(z, x, y):  return [[z, -x], [z, -y], [-z, x, y]]
    def XOR(z, x, y): return [[-z, x, y], [-z, -x, -y], [z, -x, y], [z, x, -y]]
    # 1=a 2=b 3=cin 4=sum 5=cout 6=u 7=v 8=w
    cls = AND(6, 1, 2) + XOR(8, 1, 2) + AND(7, 8, 3) + OR(5, 6, 7) + XOR(4, 8, 3)
    V = sorted({abs(l) for c in cls for l in c})
    index = {v: i for i, v in enumerate(V)}
    ms = masks(cls, index)
    rows = models(ms, len(V))
    el, ec, w = score(rows, ms, len(V), samples, random.Random(1))
    ok = len(rows) == 8 and w > 0.02
    print(f"selftest: full adder, {len(rows)} rows of {1 << len(V)} "
          f"(expected 8), +{el:.2f} literals, table wins {100 * w:.1f}% of samples")
    print("selftest:", "PASS" if ok else "FAIL — the scorer finds no gap where one is known")
    return 0 if ok else 1


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    if "--selftest" in sys.argv:
        return selftest()
    opt = {a.split("=")[0]: a.split("=")[1] for a in sys.argv[1:] if a.startswith("--") and "=" in a}
    if not args:
        print(__doc__)
        return 1
    var_budget = int(opt.get("--vars", 16))
    n_groups = int(opt.get("--groups", 8))
    samples = int(opt.get("--samples", 400))
    rng = random.Random(20260918)

    totals, clauses = load_dump(args[0])
    empty = sum(1 for c in clauses if not c["lits"])
    clauses = [c for c in clauses if c["lits"]]
    if empty:
        print(f"note: dropped {empty} clause(s) with no literals (deleted slots)")
    cnf = load_cnf(args[1]) if len(args) > 1 else []
    total_conf = sum(totals.values()) or 1
    print(f"dump: {len(clauses)} conflict-carrying clauses; conflicts {totals}")
    print(f"      {100 * sum(c['conflicts'] for c in clauses) / total_conf:.1f}% of all conflicts are in the dumped clauses")
    if cnf:
        print(f"cnf:  {len(cnf)} clauses, for completing each candidate's table")
    print(f"\n{'group':>5s} {'vars':>5s} {'cls':>5s} {'rows':>9s} {'tight':>7s} {'conf%':>7s} "
          f"{'+lits':>7s} {'+confl':>7s} {'gap%':>6s}")

    for gi, (V, members) in enumerate(grow_groups(clauses, var_budget, n_groups)):
        index = {v: i for i, v in enumerate(V)}
        n = len(V)
        inside = [c["lits"] for c in members]
        if cnf:
            vs = set(V)
            extra = [c for c in cnf if all(abs(l) in vs for l in c)]
            seen = {tuple(sorted(c)) for c in inside}
            inside += [c for c in extra if tuple(sorted(c)) not in seen]
        ms = masks(inside, index)
        rows = models(ms, n)
        conf = sum(c["conflicts"] for c in members)
        if not rows:
            print(f"{gi:5d} {n:5d} {len(inside):5d} {'UNSAT':>9s}  (the group alone is unsatisfiable)")
            continue
        el, ec, w = score(rows, ms, n, samples, rng)
        print(f"{gi:5d} {n:5d} {len(inside):5d} {len(rows):9d} {len(rows) / (1 << n):7.3f} "
              f"{100 * conf / total_conf:6.2f}% {el:7.2f} {ec:7.3f} {100 * w:5.1f}%")
    print("\nrows = the box's table size; tight = rows / 2^vars (small is a strong constraint).")
    print("+lits = mean literals GAC forces that UP does not, per sampled partial assignment;")
    print("+confl = conflicts GAC sees that UP misses; gap% = samples where the table won.")
    print("A group with gap% ~ 0 propagates nothing its clauses do not already, whatever its conflict share.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
