#!/usr/bin/env python3
"""Gate for the 2x2 calibration of the certified pipeline.

  python3 matmul/r22/check_2x2.py

1. Decodes the hydra_satsuma rank-7 witness (brent_2x2x7_hs.out) and
   verifies it against the 2x2 Brent equations (brent.py).
2. Checks it is Strassen's algorithm up to symmetry: equal, as a set of
   (alpha, beta, gamma) product triples, to Strassen under the change
   of basis A -> A J, B -> J B (J swaps the summation index 1<->2;
   gamma unchanged since (AJ)(JB) = AB), and shares the rank-type
   signature {one (2,2,2), six (1,1,1)} -- de Groote's uniqueness.
3. Confirms the rank-6 run reported UNSAT with dsr-trim verification
   against the input formula (brent_2x2x6_hs.{out,err}).
4. Confirms the independent dsr-trim re-check of the saved certificate
   (brent_2x2x6_dsrtrim.out; the .sr itself is gitignored, 59 MB).
"""
import os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, ".."))
from brent import strassen, scheme_to_bits, verify_bits, var_counts  # noqa: E402


def model_bits(path, n1, n2, n3, r):
    lits = []
    for line in open(path):
        if line.startswith("v"):
            lits += [int(x) for x in line.split()[1:] if x != "0"]
    nreal = sum(var_counts(n1, n2, n3, r))
    bits = [0] * nreal
    for l in lits:
        if 1 <= abs(l) <= nreal:
            bits[abs(l) - 1] = 1 if l > 0 else 0
    return bits


def triples(bits, na, nb, r):
    out = []
    for m in range(r):
        al = tuple(bits[m * 4:(m + 1) * 4])
        be = tuple(bits[na + m * 4:na + (m + 1) * 4])
        ga = tuple(bits[na + nb + m * 4:na + nb + (m + 1) * 4])
        out.append((al, be, ga))
    return sorted(out)


def rk(x):
    """rank of a 2x2 bit matrix (row-major 4-tuple) over F2"""
    a, b, c, d = x
    if not any(x):
        return 0
    return 2 if (a & d) ^ (b & c) else 1


def main():
    na, nb, ng = var_counts(2, 2, 2, 7)
    wb = model_bits(os.path.join(HERE, "brent_2x2x7_hs.out"), 2, 2, 2, 7)
    bad = verify_bits(wb, 2, 2, 2, 7)
    assert bad == 0, f"rank-7 witness violates {bad} Brent equations"
    print("gate 1 ok: rank-7 witness satisfies all 64 Brent equations")

    al, be, ga = strassen()
    sb = scheme_to_bits(al, be, ga, 2, 2, 2, 7)
    assert verify_bits(sb, 2, 2, 2, 7) == 0
    swapcols = lambda a: (a[1], a[0], a[3], a[2])   # alpha -> alpha J
    swaprows = lambda b: (b[2], b[3], b[0], b[1])   # beta  -> J beta
    st = triples(sb, na, nb, 7)
    st_j = sorted((swapcols(a), swaprows(b), g) for a, b, g in st)
    wt = triples(wb, na, nb, 7)
    assert wt != st, "unexpected: witness is literally Strassen"
    assert wt == st_j, "witness is NOT Strassen under A->AJ, B->JB"
    sig = lambda t: sorted((rk(a), rk(b), rk(g)) for a, b, g in t)
    assert sig(wt) == sig(st) == [(1, 1, 1)] * 6 + [(2, 2, 2)]
    print("gate 2 ok: witness == Strassen under A->AJ, B->JB "
          "(k-swap), rank types 6x(1,1,1)+1x(2,2,2)")

    out = open(os.path.join(HERE, "brent_2x2x6_hs.out")).read()
    err = open(os.path.join(HERE, "brent_2x2x6_hs.err")).read()
    assert "s UNSATISFIABLE" in out, "rank-6 not reported UNSAT"
    assert "dsr-trim VERIFIED UNSAT" in err, "rank-6 proof not verified"
    assert "ignored in certified mode" in err, "GE units not ignored"
    print("gate 3 ok: rank-6 UNSAT, dsr-trim verified against the input "
          "formula, certified mode (GE-forced units ignored)")

    # 4. independent dsr-trim run on the saved certificate (brent_2x2x6.sr,
    #    gitignored) against brent_2x2x6.cnf, outside the sat pipeline
    ind = os.path.join(HERE, "brent_2x2x6_dsrtrim.out")
    txt = open(ind).read()
    assert "s VERIFIED UNSAT" in txt, "independent dsr-trim did not verify"
    assert "776 variables" in txt and "2880 clauses" in txt
    print("gate 4 ok: independent dsr-trim on the saved SR certificate: "
          "VERIFIED UNSAT against the 776-var / 2880-clause input")


if __name__ == "__main__":
    main()
