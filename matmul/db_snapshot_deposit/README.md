# HKS 3×3×23 matrix-multiplication scheme database — archival snapshot

**Archived at: https://doi.org/10.5281/zenodo.21209925**

This is a **verbatim mirror** of the scheme database published by
**Marijn J. H. Heule, Manuel Kauers, and Martina Seidl** as the
data artifact accompanying their work on multiplying 3×3 matrices
with 23 multiplications. It is redistributed **for archival
permanence and reproducibility only**; all credit for the schemes
belongs to the original authors. If you use these schemes, cite the
HKS papers below, not this mirror.

## The artifact

| field | value |
|---|---|
| file | `schemes.tgz` |
| size | 43,134,227 bytes |
| sha256 | `4bc8132644504a917e3c076f64df8e6619fb67c55670179853ae5fdb1583074f` |
| contents | 17,376 `.tab` scheme files (mutually inequivalent {−1,0,1} rank-23 schemes) |
| original URL | http://www.algebra.uni-linz.ac.at/research/matrix-multiplication/schemes.tgz |
| snapshot date | Last-Modified 2020-08-07 (as fetched) |

Verify after download:

```bash
shasum -a 256 schemes.tgz
# expect: 4bc8132644504a917e3c076f64df8e6619fb67c55670179853ae5fdb1583074f
tar tzf schemes.tgz | grep -c '\.tab$'   # expect: 17376
```

## Why this mirror exists

The original host (`www.algebra.uni-linz.ac.at`) serves plain http
with a self-signed certificate on https, and its availability has
been intermittent. Two research notes classify new rank-23 schemes
for inequivalence against this exact corpus:

- *53 New Integer Schemes for 3×3 Matrix Multiplication with 23
  Products*
- *Exact Input-Side Minimization and 56-Addition Schemes on Two New
  Classes for Rank-23 3×3 Matrix Multiplication*

Both pin their novelty claims to the sha256 above. This deposit
guarantees the corpus remains retrievable and content-verifiable
regardless of the original host. Tooling that consumes it:
`matmul/dbcheck.py` in https://github.com/gsidebottom/logic.

## Original references (please cite these for the schemes)

- M. Heule, M. Kauers, J. Seidl. *Local Search for Fast Matrix
  Multiplication.* SAT 2019 (arXiv:1903.11391).
- M. Heule, M. Kauers, J. Seidl. *New ways to multiply 3×3-matrices.*
  J. Symbolic Computation 104 (2021), 899–916 (arXiv:1905.10192).
- Database home:
  http://www.algebra.uni-linz.ac.at/research/matrix-multiplication/
