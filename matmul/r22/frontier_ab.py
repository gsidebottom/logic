#!/usr/bin/env python3
"""Four-arm A/B on the frontier states whose exact-rank SAT call timed out
(frontier_analysis.py, 60 s cadical): reproduce the same deterministic
sample, take the TIMEOUT instances, and run each under
  cadical        plain Tseitin encoding
  cadical_lex    + lex-leader ordering of the products on their (a,b) bits
                   (breaks the S_r product-permutation symmetry; sound)
  kissat         plain encoding
  hydra_satsuma  ./target/release/sat -b hydra_satsuma (Cook -> XOR/GE ->
                   satsuma symmetry breaking + kissat, certified), if the
                   Docker image exists
with a per-call cap, 12-way parallel.  Cross-checks that no two arms
disagree (SAT vs UNSAT) on an instance.  (2026-09-03)"""
import sys, os, re, random, time, subprocess, csv
from collections import Counter, defaultdict
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tensor_sat import encode
from frontier_analysis import parse, to_slices_min_side, compress, PER_CLASS

CAP = int(os.environ.get("AB_CAP", "300"))
JOBS = int(os.environ.get("AB_JOBS", "12"))
OUT = os.environ.get("AB_OUT", "matmul/r22/frontier_ab")

def sample_instances(frontier_path, report_path):
    recs = parse(frontier_path)
    finals = [r for r in recs if r['kind'] == 'final' and r['tensor'] is not None]
    seen = {}
    for r in finals:
        key = (tuple(tuple(row) for row in r['tensor']), r['k'])
        seen.setdefault(key, r)
    uniq = list(seen.values())
    by = defaultdict(list)
    for r in uniq:
        by[(tuple(sorted(r['dims'])), r['k'])].append(r)
    random.seed(11)
    ordered = []
    for (dims, k), rs in sorted(by.items(), key=lambda kv: (kv[0][0][0] * kv[0][0][1] * kv[0][0][2], kv[0][1])):
        for r in random.sample(rs, min(PER_CLASS, len(rs))):
            ordered.append(((dims, k), r))
    # align with the report lines (same order) and keep the TIMEOUTs
    pat = re.compile(r"\s+dims \((\d+), (\d+), (\d+)\) k (\d+) lb (\d+) compressed (\d+)x(\d+)x(\d+): rank<=(\d+) (\w+) ([0-9.]+)s")
    results = []
    for line in open(report_path):
        m = pat.match(line)
        if m:
            results.append(m.groups())
    assert len(results) <= len(ordered), (len(results), len(ordered))
    picked = []
    for i, res in enumerate(results):
        (dims, k), r = ordered[i]
        assert (int(res[0]), int(res[1]), int(res[2])) == dims and int(res[3]) == k, (i, res, dims, k)
        if res[9] == "TIMEOUT":
            picked.append((i, dims, k, r))
    return picked

def lex_clauses(a, b, r, k, m, nv):
    """lex-leader: word_i <= word_{i+1} where word = (a bits, b bits), MSB first."""
    cls = []
    def new():
        nv[0] += 1
        return nv[0]
    for i in range(r - 1):
        x = a[i] + b[i]
        y = a[i + 1] + b[i + 1]
        e = new()          # e_0 = true
        cls.append([e])
        for j in range(len(x)):
            xj, yj = x[j], y[j]
            # e_j -> (x_j <= y_j)
            cls.append([-e, -xj, yj])
            if j + 1 < len(x):
                e2 = new()
                # e2 -> e, e2 -> (x_j <-> y_j)
                cls.append([-e2, e]); cls.append([-e2, -xj, yj]); cls.append([-e2, xj, -yj])
                # (e & x_j & y_j) -> e2 ; (e & -x_j & -y_j) -> e2
                cls.append([-e, -xj, -yj, e2]); cls.append([-e, xj, yj, e2])
                e = e2
    return cls

def write_cnf(path, nv, cls):
    with open(path, "w") as f:
        f.write(f"p cnf {nv} {len(cls)}\n")
        for c in cls:
            f.write(" ".join(map(str, c)) + " 0\n")

def build_instance(idx, dims, k, r):
    da, db, dc = r['dims']
    kk, slices, m, n = to_slices_min_side(r['tensor'], da, db, dc)
    X, cs, rs = compress(slices, m, n)
    nn = max(cs, rs)
    Xp = [[X[s][j] if j < cs else 0 for j in range(nn)] for s in range(kk)]
    target = k - 1
    nv, cls = encode(Xp, kk, nn, target)
    plain = f"{OUT}/inst{idx:03d}.cnf"
    write_cnf(plain, nv, cls)
    # lex variant: recover the a/b variable ids the way encode() allocates them
    a = [[i * kk + s + 1 for s in range(kk)] for i in range(target)]
    base = target * kk
    b = [[base + i * nn + j + 1 for j in range(nn)] for i in range(target)]
    nvl = [nv]
    lex = lex_clauses(a, b, target, kk, nn, nvl)
    write_cnf(f"{OUT}/inst{idx:03d}_lex.cnf", nvl[0], cls + lex)
    return dict(idx=idx, dims=dims, k=k, shape=f"{kk}x{cs}x{rs}", target=target, plain=plain, lex=f"{OUT}/inst{idx:03d}_lex.cnf")

def run_arm(task):
    inst, arm = task
    path = inst['lex'] if arm == "cadical_lex" else inst['plain']
    t0 = time.time()
    try:
        if arm in ("cadical", "cadical_lex"):
            out = subprocess.run(["cadical", "-q", path], capture_output=True, text=True, timeout=CAP)
            res = "SAT" if out.returncode == 10 else "UNSAT" if out.returncode == 20 else f"rc{out.returncode}"
        elif arm == "kissat":
            out = subprocess.run(["kissat", "-q", path], capture_output=True, text=True, timeout=CAP)
            res = "SAT" if out.returncode == 10 else "UNSAT" if out.returncode == 20 else f"rc{out.returncode}"
        else:
            with open(path) as f:
                out = subprocess.run(["./target/release/sat", "-b", "hydra_satsuma", "--timeout", str(CAP)], stdin=f, capture_output=True, text=True, timeout=CAP + 120)
            txt = out.stdout + out.stderr
            res = "UNSAT" if re.search(r"\bUNSAT", txt) else "SAT" if re.search(r"\bSAT\b|SATISFIABLE", txt) else "TIMEOUT" if "TIMEOUT" in txt else f"rc{out.returncode}"
    except subprocess.TimeoutExpired:
        res = "TIMEOUT"
    return (inst['idx'], arm, res, round(time.time() - t0, 1))

def main():
    os.makedirs(OUT, exist_ok=True)
    picked = sample_instances("matmul/r22/frontier19.txt", "matmul/r22/frontier19_report.txt")
    print(f"timeout instances reproduced: {len(picked)}", flush=True)
    insts = [build_instance(i, dims, k, r) for (i, dims, k, r) in picked]
    arms = ["cadical", "cadical_lex", "kissat"]
    have_hydra = subprocess.run(["docker", "image", "inspect", "satsuma-iter-kissat"], capture_output=True).returncode == 0
    if have_hydra:
        arms.append("hydra_satsuma")
    print("arms:", arms, flush=True)
    tasks = [(inst, arm) for inst in insts for arm in arms]
    results = []
    with Pool(JOBS) as pool:
        for res in pool.imap_unordered(run_arm, tasks):
            results.append(res)
            print(f"  inst {res[0]:03d} {res[1]:14s} {res[2]:8s} {res[3]}s", flush=True)
    with open(f"{OUT}/results.csv", "w") as f:
        w = csv.writer(f)
        w.writerow(["idx", "dims", "k", "shape", "arm", "result", "seconds"])
        meta = {i['idx']: i for i in insts}
        for idx, arm, res, dt in sorted(results):
            w.writerow([idx, meta[idx]['dims'], meta[idx]['k'], meta[idx]['shape'], arm, res, dt])
    print("\nSUMMARY (per arm):")
    per = defaultdict(Counter)
    tsum = defaultdict(float)
    for idx, arm, res, dt in results:
        per[arm][res] += 1
        tsum[arm] += dt
    for arm in arms:
        print(f"  {arm:14s} {dict(per[arm])}  total {tsum[arm]:.0f}s")
    # cross-check disagreements and per-shape decided counts
    byidx = defaultdict(dict)
    for idx, arm, res, dt in results:
        byidx[idx][arm] = res
    bad = [(i, d) for i, d in byidx.items() if "SAT" in d.values() and "UNSAT" in d.values()]
    print(f"  disagreements (SAT vs UNSAT on the same instance): {len(bad)} {bad[:5]}")
    decided = Counter()
    for i, d in byidx.items():
        v = "UNSAT" if "UNSAT" in d.values() else "SAT" if "SAT" in d.values() else "open"
        decided[(meta[i]['shape'][0], v)] += 1
    print("  decided by any arm, by slice count:", dict(sorted(decided.items())))
    print("exit 0")

if __name__ == "__main__":
    main()
