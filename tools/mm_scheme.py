#!/usr/bin/env python3
"""Read a matrix-multiplication scheme off a satisfying assignment.

Runs the web app's boxes backend (default) or CaDiCaL on a formula from
lib/matmul.jq — e.g. mm_boxes_sym(2; 7) — decodes the witness into the
matrices alpha^m, beta^m, gamma^m of each product, prints the scheme
(M_m = (sum of A entries)(sum of B entries), C_pq = sum of M's, all over GF(2)) and checks it:
every Brent equation over GF(2), and C = A·B on random matrices.

    tools/mm_scheme.py 'mm_boxes_sym(2; 7)' [--cadical] [--url http://localhost:3001]

n and r are read off the witness (the largest product and entry index among
the a_m_k variables), so any generator of the library works as the argument.
"""
import argparse, itertools, json, random, sys, time, urllib.request

def call(base, method, path, body=None):
    req = urllib.request.Request(base + path, data=json.dumps(body).encode() if body is not None else None,
                                 method=method, headers={"Content-Type": "application/json"})
    return json.load(urllib.request.urlopen(req, timeout=3600))

def witness_boxes(base, formula):
    """The boxes backend's satisfying assignment as {name: 0/1} (from the path
    literals, which are FALSE in the model, plus the appended witness)."""
    call(base, "POST", "/satisfiable", {"formula": formula, "backend": "boxes"})
    while True:
        r = call(base, "GET", "/satisfiable")
        if not r.get("running"): break
        time.sleep(0.05)
    if r.get("error"): sys.exit("boxes backend: " + r["error"])
    if not r["uncovered_paths"]: return None, r
    path = r["uncovered_paths"][0].strip("{} ")
    asg = {}
    for tok in path.split(", "):
        tok = tok.strip()
        if "(" in tok or not tok: continue          # a box-call atom, not a variable
        neg = tok.endswith("'")
        asg[tok.rstrip("'")] = 1 if neg else 0
    return asg, r

def witness_cadical(base, formula):
    call(base, "POST", "/cadical/sat", {"formula": formula})
    while True:
        r = call(base, "GET", "/cadical/sat")
        if not r.get("running"): break
        time.sleep(0.05)
    if r.get("error"): sys.exit("CaDiCaL: " + r["error"])
    res = r.get("result") or r
    if not res.get("assignment"): return None, res
    names = res["vars"]
    return {names[i]: (0 if neg else 1) for i, neg in res["assignment"]}, res

def shape(asg):
    """(n, r) from the a_m_k names of the witness."""
    ms, ks = set(), set()
    for name in asg:
        parts = name.split("_")
        if len(parts) == 3 and parts[0] == "a" and parts[1].isdigit() and parts[2].isdigit():
            ms.add(int(parts[1])); ks.add(int(parts[2]))
    if not ms: sys.exit("no a_m_k variables in the witness — not a matmul.jq formula?")
    r, n2 = max(ms), max(ks) + 1
    n = int(round(n2 ** 0.5))
    if n * n != n2: sys.exit(f"entry indices 0..{n2 - 1} do not form a square matrix")
    return n, r

def matrices(asg, n, r):
    out = []
    for m in range(1, r + 1):
        def mat(v):
            return [[asg.get(f"{v}_{m}_{n * i + j}", 0) for j in range(n)] for i in range(n)]
        out.append((mat("a"), mat("b"), mat("c")))
    return out

def brent_ok(scheme, n):
    idx = lambda i, j: n * i + j
    for a, b, c, d, p, q in itertools.product(range(n), repeat=6):
        lhs = sum(al[a][b] & be[c][d] & ga[p][q] for al, be, ga in scheme) % 2
        if lhs != int(b == c and a == p and d == q): return False
    return True

def multiply(scheme, A, B, n):
    C = [[0] * n for _ in range(n)]
    for al, be, ga in scheme:
        M = (sum(al[i][j] & A[i][j] for i in range(n) for j in range(n)) % 2) & \
            (sum(be[i][j] & B[i][j] for i in range(n) for j in range(n)) % 2)
        for p in range(n):
            for q in range(n):
                C[p][q] ^= ga[p][q] & M
    return C

def entries(mat, name, n):
    return " + ".join(f"{name}{i + 1}{j + 1}" for i in range(n) for j in range(n) if mat[i][j]) or "0"

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("filter", help="jq expression producing the formula, e.g. 'mm_boxes_sym(2; 7)'")
    ap.add_argument("--cadical", action="store_true"); ap.add_argument("--url", default="http://localhost:3001")
    args = ap.parse_args()
    call(args.url, "POST", "/jq-lib", {"path": "matmul.jq"})
    formula = call(args.url, "POST", "/jq", {"filter": args.filter})["results"][0]
    t0 = time.time()
    asg, raw = (witness_cadical if args.cadical else witness_boxes)(args.url, formula)
    print(f"{'CaDiCaL' if args.cadical else 'boxes backend'}: {'SAT' if asg else 'UNSAT'} in {time.time() - t0:.2f}s")
    if not asg: return
    n, r = shape(asg)
    print(f"{n}x{n} matrices, {r} products")
    scheme = matrices(asg, n, r)
    for m, (al, be, ga) in enumerate(scheme, 1):
        print(f"M{m} = ({entries(al, 'A', n)}) ({entries(be, 'B', n)})")
    for p in range(n):
        for q in range(n):
            terms = [f"M{m}" for m, (_, _, ga) in enumerate(scheme, 1) if ga[p][q]]
            print(f"C{p + 1}{q + 1} = {' + '.join(terms) or '0'}")      # + is XOR over GF(2)
    print("Brent equations:", "all satisfied" if brent_ok(scheme, n) else "VIOLATED")
    rnd = random.Random(1)
    for _ in range(200):
        A = [[rnd.randint(0, 1) for _ in range(n)] for _ in range(n)]
        B = [[rnd.randint(0, 1) for _ in range(n)] for _ in range(n)]
        AB = [[sum(A[i][k] & B[k][j] for k in range(n)) % 2 for j in range(n)] for i in range(n)]
        if multiply(scheme, A, B, n) != AB: sys.exit("scheme gives a wrong product on a random pair")
    print("C = AB on 200 random pairs over GF(2): ok;", sum(1 for al, _, _ in scheme if any(map(any, al))), "non-zero products")

if __name__ == "__main__":
    main()
