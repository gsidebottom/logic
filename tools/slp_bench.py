#!/usr/bin/env python3
"""Tractable SLP(k) benchmarks (lib/slp.jq) — boxes backend vs CaDiCaL.

For each instance: descend k from the naive bound with CaDiCaL (capped) to
the minimum, then time both engines at min-1, min, min+1.  Prints a table.

    tools/slp_bench.py [--cap 60] [--url http://localhost:3001] [instance …]
"""
import argparse, json, sys, time, urllib.request

def call(base, method, path, body=None):
    req = urllib.request.Request(base + path, data=json.dumps(body).encode() if body is not None else None,
                                 method=method, headers={"Content-Type": "application/json"})
    return json.load(urllib.request.urlopen(req, timeout=3600))

def run(base, engine, formula, cap):
    """(verdict, seconds) — verdict SAT/UNSAT/timeout."""
    if engine == "boxes":
        call(base, "POST", "/satisfiable", {"formula": formula, "backend": "boxes"}); t0 = time.time()
        while True:
            r = call(base, "GET", "/satisfiable")
            if not r.get("running"): break
            if time.time() - t0 > cap: call(base, "POST", "/satisfiable/cancel", {}); time.sleep(0.5); return "timeout", cap
            time.sleep(0.03)
        if r.get("error"): sys.exit("boxes: " + r["error"])
        return ("SAT" if r["uncovered_paths"] else "UNSAT"), r.get("elapsed_secs", time.time() - t0)
    call(base, "POST", "/cadical/sat", {"formula": formula}); t0 = time.time()
    while True:
        r = call(base, "GET", "/cadical/sat")
        if not r.get("running"): break
        if time.time() - t0 > cap: call(base, "POST", "/cadical/sat/cancel", {}); time.sleep(0.5); return "timeout", cap
        time.sleep(0.03)
    if r.get("error"): sys.exit("CaDiCaL: " + r["error"])
    res = r.get("result") or r
    return ("SAT" if res.get("assignment") else "UNSAT"), res.get("elapsed_secs", time.time() - t0)

DEFAULT = [
    ("strassen_out", "strassen_out"),
    ("sun56[0,3,7]", "slp_window(sun56_cell; [0, 3, 7])"),
    ("sun56[0,5,7]", "slp_window(sun56_cell; [0, 5, 7])"),
    ("i12[0,1,3]",   "slp_window(i12_cell; [0, 1, 3])"),
    ("i19[4,6,7]",   "slp_window(i19_cell; [4, 6, 7])"),
    ("cn120[0,6,8]", "slp_window(cn120_cell; [0, 6, 8])"),
    ("i12[0,3,4]",   "slp_window(i12_cell; [0, 3, 4])"),
    ("sun56[1,2,4]", "slp_window(sun56_cell; [1, 2, 4])"),
]

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("instances", nargs="*", help="label=jq-expression (default: the window set)")
    ap.add_argument("--cap", type=float, default=60); ap.add_argument("--url", default="http://localhost:3001")
    ap.add_argument("--no-sb", action="store_true")
    args = ap.parse_args()
    base = args.url
    call(base, "POST", "/jq-lib", {"path": "slp.jq"})
    insts = [tuple(a.split("=", 1)) for a in args.instances] or DEFAULT
    sb = "false" if args.no_sb else "true"
    rows = []
    for label, expr in insts:
        inst = json.loads(call(base, "POST", "/jq", {"filter": f"({expr}) | tojson"})["results"][0])
        forms = [f for f in inst["forms"] if sum(f) >= 2]
        n, kmax = inst["n"], sum(sum(f) - 1 for f in forms)
        formula_of = lambda k: call(base, "POST", "/jq", {"filter": f"slp({expr}; {k}; {sb})"})["results"][0]
        # descent with CaDiCaL: the smallest k that is SAT (naive bound is SAT by construction)
        k, kmin, unknown = kmax, kmax, False
        while k >= 1:
            v, _ = run(base, "cadical", formula_of(k), args.cap)
            if v == "SAT": kmin = k; k -= 1
            elif v == "UNSAT": break
            else: unknown = True; break
        print(f"=== {label}: n = {n}, {len(forms)} forms (weights {[sum(f) for f in forms]}), naive {kmax}, minimum {kmin}{' (descent timed out below)' if unknown else ''}", flush=True)
        for kk in [kmin - 1, kmin, kmin + 1]:
            if kk < 1: continue
            F = formula_of(kk)
            cells = []
            for engine in ["boxes", "cadical"]:
                v, s = run(base, engine, F, args.cap)
                cells.append(f"{v} {s:.2f}s" if v != "timeout" else f">{args.cap:.0f}s")
            print(f"  k = {kk:2}: boxes {cells[0]:16} CaDiCaL {cells[1]:16} ({F.count('(')} boxes)", flush=True)
            rows.append((label, kk, cells))
    print("\n| instance | k | boxes backend | CaDiCaL |\n|---|---|---|---|")
    for label, kk, cells in rows: print(f"| {label} | {kk} | {cells[0]} | {cells[1]} |")

if __name__ == "__main__":
    main()
