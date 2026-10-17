#!/usr/bin/env python3
"""Independent checker for <4x4x4:47> mod-2 programs in PLinOpt format.

A scheme is three sparse matrices (PLinOpt .sms, 1-based "i j v" lines,
header "rows cols M", terminated by "0 0 0"): L (47x16) and R (47x16)
map the row-major entries of A and B to the 47 product operands, and
P (16x47) maps the 47 products to the row-major entries of C:
    Vect(C) = P . ((L . Vect(A)) (.) (R . Vect(B)))      over F_2.
Each matrix comes with a straight-line program (.slp, lines
"v:=t1+t2+...;" over inputs i<k> and earlier variables; outputs o<j>).

Checks, all from scratch:
  * every SLP computes exactly its matrix (row j of the matrix = o<j>
    as a set of inputs, mod 2), and its XOR count = sum(#terms - 1);
  * (L, R, P) multiplies 4x4 matrices: all 256 pairs of basis matrices
    (E_a, E_b) give Vect(E_a E_b) mod 2 -- bilinearity makes this a proof.

Usage: x47check.py PREFIX          (reads PREFIX_{L,R,P}.{sms,slp})
       x47check.py L.sms R.sms P.sms L.slp R.slp P.slp
Prints per-side XOR counts and the total; exits nonzero on any failure.
"""
import re
import sys

N = 4
NN = N * N


def read_sms(path):
    """Return (rows, cols, list of row bitmasks over columns), mod 2."""
    with open(path) as f:
        tok = f.readline().split()
        rows, cols = int(tok[0]), int(tok[1])
        mask = [0] * rows
        for line in f:
            t = line.split()
            if not t:
                continue
            i, j, v = int(t[0]), int(t[1]), int(t[2])
            if i == 0 and j == 0:
                break
            if not (1 <= i <= rows and 1 <= j <= cols):
                raise ValueError(f"{path}: entry out of range: {line!r}")
            if v % 2:
                mask[i - 1] ^= 1 << (j - 1)
    return rows, cols, mask


TERM = re.compile(r"[A-Za-z_][A-Za-z_0-9]*")


def run_slp(path, n_in):
    """Evaluate an all-'+' SLP over F_2; return ({output index: mask}, xors)."""
    env = {f"i{k}": 1 << k for k in range(n_in)}
    outs, xors = {}, 0
    with open(path) as f:
        text = f.read()
    for stmt in text.split(";"):
        stmt = stmt.strip()
        if not stmt:
            continue
        lhs, rhs = stmt.split(":=")
        lhs, rhs = lhs.strip(), rhs.strip()
        if re.search(r"[^A-Za-z_0-9+\s]", rhs):
            raise ValueError(f"{path}: unsupported expression {stmt!r}")
        terms = TERM.findall(rhs)
        if not terms:
            raise ValueError(f"{path}: empty right-hand side {stmt!r}")
        val = 0
        for t in terms:
            if t not in env:
                raise ValueError(f"{path}: {t} used before assignment in {stmt!r}")
            val ^= env[t]
        xors += len(terms) - 1
        env[lhs] = val
        m = re.fullmatch(r"o(\d+)", lhs)
        if m:
            outs[int(m.group(1))] = val
    return outs, xors


def check_side(name, sms, slp):
    rows, cols, mask = read_sms(sms)
    outs, xors = run_slp(slp, cols)
    bad = [j for j in range(rows) if outs.get(j, 0) != mask[j]]
    # rows that are zero need no output; everything else must be produced
    bad = [j for j in bad if not (mask[j] == 0 and j not in outs)]
    if bad:
        raise SystemExit(f"FAIL {name}: outputs {bad[:8]} differ from {sms}")
    return rows, cols, mask, xors


def brent(L, R, P, r):
    """All 256 basis pairs: P((L e_a) * (R e_b)) == Vect(E_a E_b) mod 2."""
    for a in range(NN):
        for b in range(NN):
            prods = 0
            for k in range(r):
                if (L[k] >> a) & 1 and (R[k] >> b) & 1:
                    prods |= 1 << k
            got = 0
            for c in range(NN):
                if bin(P[c] & prods).count("1") % 2:
                    got |= 1 << c
            ai, aj = divmod(a, N)
            bi, bj = divmod(b, N)
            want = 1 << (ai * N + bj) if aj == bi else 0
            if got != want:
                return False, (a, b)
    return True, None


def main(argv):
    if len(argv) == 2:
        p = argv[1]
        files = [f"{p}_{s}.{e}" for e in ("sms", "slp") for s in "LRP"]
    elif len(argv) == 7:
        files = argv[1:]
    else:
        raise SystemExit(__doc__)
    sL, sR, sP, pL, pR, pP = files
    rL, cL, L, xL = check_side("L", sL, pL)
    rR, cR, R, xR = check_side("R", sR, pR)
    rP, cP, P, xP = check_side("P", sP, pP)
    if not (cL == cR == NN and rL == rR == cP and rP == NN):
        raise SystemExit(f"FAIL shapes: L {rL}x{cL}, R {rR}x{cR}, P {rP}x{cP}")
    ok, where = brent(L, R, P, rL)
    if not ok:
        raise SystemExit(f"FAIL Brent: basis pair {where}")
    print(f"OK rank {rL}: L {xL} + R {xR} + P {xP} = {xL + xR + xP} XORs "
          f"(Brent 256/256 basis pairs)")


if __name__ == "__main__":
    main(sys.argv)
