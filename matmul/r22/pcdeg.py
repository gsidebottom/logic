#!/usr/bin/env python3
"""Experiment (a): Polynomial-Calculus / Groebner refutation degree of the
Brent system over F_2 as a function of the rank r.

  python3 matmul/r22/pcdeg.py [--ranks 1,2,3,4,5,6] [--maxdeg 8]
                              [--time 600] [--mem-gb 16] [--n 3]

For each rank r and degree bound D = 3, 4, ... the Brent polynomials of
<n,n,n> at rank r (plus the Boolean field equations x^2 + x) are handed
to Singular with `degBound = D`: Buchberger's algorithm discarding every
S-polynomial above total degree D. If the truncated standard basis is
{1}, the ideal contains 1 within degree D -- a degree-<=D Polynomial
Calculus refutation exists (every line of the derivation has degree
<= D). The minimal such D is an UPPER bound on the PC refutation degree
of the rank-r instance; 'OPEN' at D means the truncated computation did
not reach 1 (not a proof that no degree-D refutation exists). Each
(r, D) run is bounded in wall-clock and RSS. Results append to
matmul/r22/pcdeg.csv: n, r, D, verdict, seconds, rss_mb.

Variables: a{m}x{i}{j} = alpha^(m)_{ij}, b{m}x{i}{j} = beta^(m)_{ij},
g{m}x{i}{j} = gamma^(m)_{ij}. Equation (a,b,c,d,p,q):
  sum_m a{m}x{a}{b} * b{m}x{c}{d} * g{m}x{p}{q}  +  [b=c][a=p][d=q]
"""
import argparse, csv, os, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))


def brent_polys(n, r):
    polys = []
    for a in range(n):
        for b in range(n):
            for c in range(n):
                for d in range(n):
                    for p in range(n):
                        for q in range(n):
                            terms = [f"a{m}x{a}{b}*b{m}x{c}{d}*g{m}x{p}{q}"
                                     for m in range(r)]
                            rhs = 1 if (b == c and a == p and d == q) else 0
                            polys.append("+".join(terms) + ("+1" if rhs else ""))
    return polys


def variables(n, r):
    vs = []
    for m in range(r):
        for kind in "abg":
            for i in range(n):
                for j in range(n):
                    vs.append(f"{kind}{m}x{i}{j}")
    return vs


def singular_script(n, r, D):
    vs = variables(n, r)
    lines = [f"ring R = 2, ({','.join(vs)}), dp;",
             "ideal I;"]
    for P in brent_polys(n, r):
        lines.append(f"I = I, {P};")
    for v in vs:
        lines.append(f"I = I, {v}^2+{v};")
    lines += [f"degBound = {D};",
              "option(redSB);",
              "ideal G = std(I);",
              "if (size(G) == 1 and G[1] == 1) { print(\"RESULT REFUTED\"); }"
              " else { print(\"RESULT OPEN size=\" + string(size(G))); }",
              "quit;"]
    return "\n".join(lines) + "\n"


def run_bounded(cmd, stdin_text, time_s, mem_gb):
    """Run cmd with stdin, kill on wall-clock or RSS overrun. Returns
    (stdout, seconds, peak_rss_mb, status) with status in
    {ok, timeout, memout}."""
    t0 = time.time()
    p = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, text=True)
    p.stdin.write(stdin_text)
    p.stdin.close()
    peak = 0
    status = "ok"
    while True:
        rc = p.poll()
        if rc is not None:
            break
        try:
            rss_kb = int(subprocess.check_output(
                ["ps", "-o", "rss=", "-p", str(p.pid)], text=True).strip() or 0)
        except Exception:
            rss_kb = 0
        peak = max(peak, rss_kb // 1024)
        if time.time() - t0 > time_s:
            status = "timeout"; p.kill(); break
        if peak > mem_gb * 1024:
            status = "memout"; p.kill(); break
        time.sleep(0.5)
    out = p.stdout.read() if p.stdout else ""
    return out, time.time() - t0, peak, status


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ranks", default="1,2,3,4,5,6")
    ap.add_argument("--maxdeg", type=int, default=8)
    ap.add_argument("--time", type=float, default=600)
    ap.add_argument("--mem-gb", type=float, default=16)
    ap.add_argument("--n", type=int, default=3)
    ap.add_argument("--singular", default="Singular")
    args = ap.parse_args()
    csv_path = os.path.join(HERE, "pcdeg.csv")
    new = not os.path.exists(csv_path)
    with open(csv_path, "a", newline="") as f:
        w = csv.writer(f)
        if new:
            w.writerow(["n", "r", "D", "verdict", "seconds", "rss_mb"])
        for r in [int(x) for x in args.ranks.split(",")]:
            for D in range(3, args.maxdeg + 1):
                script = singular_script(args.n, r, D)
                out, secs, rss, status = run_bounded(
                    [args.singular, "-q"], script, args.time, args.mem_gb)
                if status != "ok":
                    verdict = status.upper()
                elif "RESULT REFUTED" in out:
                    verdict = "REFUTED"
                elif "RESULT OPEN" in out:
                    verdict = "OPEN"
                else:
                    verdict = "ERROR:" + out.strip().splitlines()[-1][:80] if out.strip() else "ERROR"
                w.writerow([args.n, r, D, verdict, f"{secs:.1f}", rss]); f.flush()
                print(f"n={args.n} r={r} D={D}: {verdict} ({secs:.1f}s, {rss} MB)", flush=True)
                if verdict == "REFUTED":
                    break            # minimal degree found for this r
                if verdict in ("TIMEOUT", "MEMOUT"):
                    break            # larger D only costs more
            else:
                print(f"n={args.n} r={r}: not refuted up to D={args.maxdeg}", flush=True)


if __name__ == "__main__":
    main()
