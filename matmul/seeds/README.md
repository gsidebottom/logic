# seeds/ — known 3x3x3 r=23 schemes as 621-bit strings

Each `.bits` file is one 621-character 0/1 line in the `brent.py` variable
order for n1=n2=n3=3, r=23:

- vars 0..206: `alpha[m][a][b]` at `m*9 + a*3 + b`
- vars 207..413: `beta[m][c][d]` at `207 + m*9 + c*3 + d`
- vars 414..620: `gamma[m][p][q]` at `414 + m*9 + p*3 + q`, where
  `gamma[m][p][q]=1` means product m contributes to `C[p][q]`, `C = A*B`
  (NOT transposed).

Bit = 1 iff the source scheme's integer coefficient is odd (mod-2 reduction).

## Source

Kauers/Heule/Seidl 3x3 matrix-multiplication solution repository:
https://www.algebra.uni-linz.ac.at/research/matrix-multiplication/
(files at `schemes/<rank-pattern>/<name>.tab`), fetched 2026-07-02.

- `laderman.bits`, `smirnov.bits`, `oh-kim-moon.bits`,
  `courtois-bard-hulme.bits`: the four classics (`schemes/classic/`).
- `db-<name>.bits`: 20 found schemes, one from each of 20 different
  rank-pattern directories chosen to spread across the whole rank-signature
  range (leading counts 4..17). Names are globally unique in the database,
  so the directory is omitted; the invariant string in the name
  (`i<..>w<..>c<..>-<idx>`) identifies the scheme.

## Convention notes (determined empirically)

Both the site's `.tab` (third 3x3 block of each product) and `.exp` (third
factor `(cXY ...)`) formats list the C tensor TRANSPOSED: an entry `cXY`
means the product contributes to `C[Y][X]`. Reading gamma transposed gives
0 violated Brent equations for every file; reading it directly gives 36
violations. Cross-checks: for each classic, `.tab` and `.exp` parse to the
same scheme, and the site's `laderman` canonicalizes identically to the
embedded `brent.laderman()` (canon.py: "2 schemes read, 0 INVALID,
1 distinct").

## Verification

Every file passes

    python3 canon.py 3 3 3 23 seeds/<name>.bits
    # -> 1 schemes read, 0 INVALID, 1 distinct after summand sorting

and all 24 together are mutually distinct:

    cat seeds/*.bits | python3 canon.py 3 3 3 23
    # -> 24 schemes read, 0 INVALID, 24 distinct after summand sorting
