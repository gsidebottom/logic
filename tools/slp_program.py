#!/usr/bin/env python3
"""Read an XOR straight-line program off a satisfying assignment of lib/slp.jq.

    tools/slp_program.py 'strassen_out' 8 [--no-sb] [--cadical] [--url http://localhost:3001]

Runs slp(<instance>; k[; sb]) on the web app's boxes backend (or CaDiCaL),
decodes the witness — each step's two sources from the s_t_j selectors —
replays the program over GF(2)^n and checks that every form of weight ≥ 2
is the value of some step (the same replay check matmul/cxlb.py does).
"""
import argparse, json, sys, time, urllib.request

def call(base, method, path, body=None):
    req = urllib.request.Request(base + path, data=json.dumps(body).encode() if body is not None else None,
                                 method=method, headers={"Content-Type": "application/json"})
    return json.load(urllib.request.urlopen(req, timeout=3600))

def witness_boxes(base, formula, cap):
    call(base, "POST", "/satisfiable", {"formula": formula, "backend": "boxes"})
    t0 = time.time()
    while True:
        r = call(base, "GET", "/satisfiable")
        if not r.get("running"): break
        if time.time() - t0 > cap: call(base, "POST", "/satisfiable/cancel", {}); return "timeout", None
        time.sleep(0.05)
    if r.get("error"): sys.exit("boxes backend: " + r["error"])
    if not r["uncovered_paths"]: return "UNSAT", None
    asg = {}
    for tok in r["uncovered_paths"][0].strip("{} ").split(", "):
        tok = tok.strip()
        if "(" in tok or not tok: continue
        asg[tok.rstrip("'")] = 1 if tok.endswith("'") else 0   # a path literal is FALSE in the model
    return "SAT", asg

def witness_cadical(base, formula, cap):
    call(base, "POST", "/cadical/sat", {"formula": formula})
    t0 = time.time()
    while True:
        r = call(base, "GET", "/cadical/sat")
        if not r.get("running"): break
        if time.time() - t0 > cap: call(base, "POST", "/cadical/sat/cancel", {}); return "timeout", None
        time.sleep(0.05)
    if r.get("error"): sys.exit("CaDiCaL: " + r["error"])
    res = r.get("result") or r
    if not res.get("assignment"): return "UNSAT", None
    names = res["vars"]
    return "SAT", {names[i]: (0 if neg else 1) for i, neg in res["assignment"]}

def decode(asg, n, k):
    """[(sources of step t)] with sources 0..n-1 the inputs, n+u step u."""
    steps = []
    for t in range(k):
        srcs = [j for j in range(n + t) if asg.get(f"s_{t}_{j}", 0) == 1]
        steps.append(srcs)
    return steps

def replay(steps, n):
    vals = []
    for srcs in steps:
        v = [0] * n
        for j in srcs:
            src = ([1 if i == j else 0 for i in range(n)] if j < n else vals[j - n])
            v = [a ^ b for a, b in zip(v, src)]
        vals.append(v)
    return vals

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("instance", help="jq expression for the instance, e.g. strassen_out or 'slp_window(sun56_cell; [0,3,7])'")
    ap.add_argument("k", type=int)
    ap.add_argument("--no-sb", action="store_true"); ap.add_argument("--cadical", action="store_true")
    ap.add_argument("--cap", type=float, default=600); ap.add_argument("--url", default="http://localhost:3001")
    args = ap.parse_args()
    call(args.url, "POST", "/jq-lib", {"path": "slp.jq"})
    inst = json.loads(call(args.url, "POST", "/jq", {"filter": f"({args.instance}) | tojson"})["results"][0])
    n, forms = inst["n"], [f for f in inst["forms"] if sum(f) >= 2]
    filt = f"slp({args.instance}; {args.k}; {'false' if args.no_sb else 'true'})"
    formula = call(args.url, "POST", "/jq", {"filter": filt})["results"][0]
    t0 = time.time()
    verdict, asg = (witness_cadical if args.cadical else witness_boxes)(args.url, formula, args.cap)
    engine = "CaDiCaL" if args.cadical else "boxes backend"
    print(f"{engine}: SLP({args.k}) on {args.instance} (n = {n}, {len(forms)} forms of weight ≥ 2, {formula.count('(')} boxes): {verdict} in {time.time() - t0:.2f}s")
    if verdict != "SAT": return
    steps = decode(asg, n, args.k)
    vals = replay(steps, n)
    name = lambda j: f"x{j + 1}" if j < n else f"y{j - n + 1}"
    for t, srcs in enumerate(steps):
        if len(srcs) != 2: sys.exit(f"step {t + 1} selects {len(srcs)} sources")
        print(f"y{t + 1} = {name(srcs[0])} + {name(srcs[1])}    = {''.join(map(str, vals[t]))}")
    ok = True
    for f in forms:
        hits = [t + 1 for t, v in enumerate(vals) if v == f]
        print(f"form {''.join(map(str, f))}: {'y' + str(hits[0]) if hits else 'NOT COMPUTED'}")
        ok &= bool(hits)
    for t in range(1, args.k):   # the witness's own value bits agree with the replay
        for i in range(n):
            if f"x_{t}_{i}" in asg and asg[f"x_{t}_{i}"] != vals[t][i]: sys.exit(f"x_{t}_{i} disagrees with the replay")
    print("replay:", "every form computed" if ok else "FAILED")

if __name__ == "__main__":
    main()
