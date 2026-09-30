#!/usr/bin/env python3
"""The circuit stage of `sat -b hydra_circuit` on the generated instances of
tools/selftest_cnf2aig.py, with the thresholds lowered so that it fires
wherever it can: verdicts against cadical, SAT models checked against the
instance, UNSAT certificates verified by the stage itself (drat-trim).

    tools/circuit/stage_test.py FIRST_SEED LAST_SEED
"""
import sys, subprocess, os, tempfile, shutil
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, ".."))
import selftest_cnf2aig as t
SAT = os.environ.get("SAT_BIN", os.path.join(HERE, "..", "..", "target", "release", "sat"))
lo, hi = int(sys.argv[1]), int(sys.argv[2])
bad = 0; n = 0; fired = 0; probe = 0; passes = 0; unsat_ok = 0; sat_ok = 0
for seed in range(lo, hi):
    nv, cls = t.instance(seed)
    d = tempfile.mkdtemp(prefix="st_")
    inp = f"{d}/in.cnf"; t.write_cnf(inp, nv, cls)
    truth = {10: True, 20: False}.get(subprocess.run([t.CADICAL, "-q", inp], capture_output=True).returncode)
    r = subprocess.run([SAT, "-b", "hydra_circuit", "--timeout", "60", "--circuit-min-products", "1", "--circuit-min-share", "1", "--circuit-min-sharing", "1",
                        "--circuit-probe-conflicts", ["1", "1", "1", "50", "20000"][seed % 5], "--circuit-passes", ["factor,cuts", "factor,sweep,cuts", "cuts", "sweep"][seed % 4]],
                       stdin=open(inp), capture_output=True, text=True, timeout=300)
    n += 1
    got = True if "s SATISFIABLE" in r.stdout else False if "s UNSATISFIABLE" in r.stdout else None
    err = r.stderr
    if "circuit stage decided" in err: fired += 1
    if "decided (probe)" in err: probe += 1
    if "+ cadical) " in err: passes += 1
    if got is None or got != truth:
        bad += 1; print(f"seed {seed}: verdict {got} truth {truth} rc={r.returncode}\n  {err[-600:]}"); shutil.rmtree(d); continue
    if "circuit stage decided" in err:
        if got:
            model = [int(x) for l in r.stdout.splitlines() if l.startswith("v") for x in l.split()[1:] if x != "0"]
            val = {abs(x): x > 0 for x in model}
            if len(val) != nv or any(not any(val[abs(l)] == (l > 0) for l in c) for c in cls):
                bad += 1; print(f"seed {seed}: the model does not satisfy the instance"); shutil.rmtree(d); continue
            sat_ok += 1
        else:
            if "drat-trim VERIFIED UNSAT" not in err:
                bad += 1; print(f"seed {seed}: UNSAT without a verified certificate\n  {err[-400:]}"); shutil.rmtree(d); continue
            unsat_ok += 1
    shutil.rmtree(d)
print(f"stage test: {bad} failures in {n} instances; the stage decided {fired} ({probe} by the probe, {passes} after the passes): {unsat_ok} certificates verified, {sat_ok} models checked")
sys.exit(1 if bad else 0)
