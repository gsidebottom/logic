#!/usr/bin/env python3
"""Which anniversary instances hydra's stages and the circuit stage apply to,
without running any engine: sat -b hydra_circuit_satsuma --stop-at-fallthrough
with the circuit trigger's product threshold out of reach, so the stage only
reports what its trial factoring finds.  Cook / XOR / factoring verdicts are
real (and fast); the circuit trigger is applied offline to the trial numbers
(>= 64 products, paired gates >= 5% of all gates, >= 20 paired gates per
product, <= 10M clauses).  Two at a time, beside the duo run.  -> scan.jsonl"""
import json, re, subprocess, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

SAT = "/Users/greg/projects/logic/target/release/sat"
import sys
IDX = sys.argv[1] if len(sys.argv) > 1 else "/Users/greg/projects/sat_benchmarks/anni_2022.jsonl"
HERE = Path(sys.argv[2]).resolve() if len(sys.argv) > 2 else Path(".").resolve()
OUT = HERE / "scan.jsonl"
TMP = HERE / "tmp"; TMP.mkdir(exist_ok=True)

done = set()
if OUT.exists():
    for l in open(OUT):
        try:
            done.add(json.loads(l)["hash"])
        except (ValueError, KeyError):
            pass


def one(rec):
    h = rec["hash"]
    xz = next(iter(sorted(Path("/Users/greg/projects/sat_benchmarks").glob(f"{h}-*.cnf.xz"))), None)
    out = dict(hash=h, name=rec["filename"].replace(".cnf.xz", ""), family=rec["family"],
               nclauses=rec.get("nclauses"))
    if xz is None:
        out["outcome"] = "missing"
        return out
    cnf = TMP / f"{h}.cnf"
    with open(cnf, "wb") as f:
        subprocess.run(["xz", "-dc", str(xz)], stdout=f, check=False)
    t0 = time.time()
    try:
        p = subprocess.run([SAT, "-b", "hydra_circuit_satsuma", "-t", "900", "--stop-at-fallthrough",
                            "--circuit-min-products", "1000000000", "--no-verify",
                            "--proof", str(TMP / f"{h}.proof")],
                           stdin=open(cnf, "rb"), capture_output=True, text=True, timeout=1200)
        err, so = p.stderr, p.stdout
    except subprocess.TimeoutExpired:
        err, so = "", ""
        out["outcome"] = "scan timeout"
    out["wall_s"] = round(time.time() - t0, 2)
    cnf.unlink(missing_ok=True)
    (TMP / f"{h}.proof").unlink(missing_ok=True)
    m = re.search(r"prover=(cook|xor|factoring)", err)
    v = re.search(r"^s (SATISFIABLE|UNSATISFIABLE)", so, re.M)
    if m and v:
        out.update(outcome=f"decided by {m.group(1)}", verdict=v.group(1)[:5].replace("UNSAT", "UNSAT"),
                   time_s=float(re.search(r"c (?:UN)?SAT in ([0-9.]+)ms", err).group(1)) / 1000
                   if re.search(r"c (?:UN)?SAT in ([0-9.]+)ms", err) else None)
        out["verdict"] = "UNSAT" if v.group(1).startswith("UNSAT") else "SAT"
    elif "circuit-max-clauses" in err and "skipped" in err:
        out["outcome"] = "fall-through, over the circuit clause cap"
    else:
        t = re.search(r"circuit stage: (\d+) gates in (\d+) clauses; factoring finds (\d+) products of inputs on (\d+) gates \(([0-9.]+)s\)", err)
        if t:
            g, c, pr, pa, ts = int(t.group(1)), int(t.group(2)), int(t.group(3)), int(t.group(4)), float(t.group(5))
            fires = pr >= 64 and pa * 100 >= g * 5 and pa >= pr * 20
            out.update(outcome="circuit stage would fire" if fires else "fall-through, circuit declines",
                       gates=g, products=pr, paired=pa, trial_s=ts)
        elif "fall-through: stopping" in err:
            out["outcome"] = "fall-through, no circuit trial"
        elif "outcome" not in out:
            out["outcome"] = "other: " + (err.strip().splitlines()[-1][:120] if err.strip() else "no output")
    fac = re.search(r"factoring-verdict=(\w+)", err)
    if fac:
        out["factoring_verdict"] = fac.group(1)
    return out


recs = [json.loads(l) for l in open(IDX) if l.strip()]
todo = [r for r in recs if r["hash"] not in done]
with ThreadPoolExecutor(2) as ex, open(OUT, "a") as f:
    for res in ex.map(one, todo):
        f.write(json.dumps(res) + "\n")
        f.flush()
print("SCAN DONE", flush=True)
