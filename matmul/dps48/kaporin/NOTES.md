# Kaporin (4,4,4;48) complex scheme — coefficients FOUND

Retrieved 2026-07-07.

## What is here

| file | what it is |
|---|---|
| `test444r48.for` | **Kaporin's own Fortran verification program containing the complete scheme**: all 192 seed coefficients (12 complex 4x4 matrices, full double precision) + the generator structure that expands them into the 48 rank-one terms, + Brent-residual check. 16,675 bytes, ASCII/CRLF, sha1 `4e2aeeb9343e1d33de10fe75b116bd644192d95e`. |
| `doklady_semianalytical_brent_ru.pdf` | Kaporin, "Chislenno-analiticheskoe reshenie uravnenii Brenta" (Semi-analytical solution of Brent equations), Doklady RAN Mat. Inf. Prots. Upr. 518:1 (2024) 29–34, DOI 10.31857/S2686954324040056. Russian, free full text. Defines the parameterization (Theorems 1–2, eqs (4)–(17)) that the Fortran file instantiates, and cites the Fortran file as its ref [8]. |
| `provenance_cloudmailru_folder.json` | cloud.mail.ru API listing of the public share (file name, size, mtime, mail.ru hash) — provenance record. |

## Provenance

- `test444r48.for` downloaded from Kaporin's public share **https://cloud.mail.ru/public/Yfij/ErDxopqBh** (single file in share; mtime 2024-05-04). The share is the literal reference [8] of the Doklady paper:
  > Kaporin I. *Verifying the correctness of the (4,4,4;48) matrix multiplication scheme with complex coefficients exact up to the floating point tolerance*, 2024. URL: https://cloud.mail.ru/public/Yfij/ErDxopqBh
- Actual fetch URL (mail.ru weblink dispatcher, may expire): `https://cloclo52.cloud.mail.ru/public/.../g/no/Yfij/ErDxopqBh`; re-derive via `https://cloud.mail.ru/api/v2/dispatcher?weblink=Yfij%2FErDxopqBh` (`weblink_get` entry) if needed.
- Doklady PDF from `https://journals.rcsi.science/2686-9543/article/download/269374/248379`.

The paper the task cited — Kaporin, "Finding complex-valued solutions of Brent equations using nonlinear least squares", Comput. Math. Math. Phys. **64**:9 (2024) 1881–1891, DOI 10.1134/S0965542524701021 (Russian: Zh. Vychisl. Mat. Mat. Fiz. 64:9, 1578–1588, DOI 10.31857/S0044466924090015) — is the method paper (the NLS solver + parameterizations). The Doklady paper is a condensed companion announcing the same (4,4,4;48) and (2,4,5;32) results and pointing to the coefficient file. **No arXiv preprint of either exists** (Kaporin has no arXiv author page; searches for "Kaporin Brent" on arXiv return only third-party citations).

## Format of `test444r48.for` (ground truth = the code itself)

Brent form used (eq (1) of the Doklady paper): the 48-term decomposition satisfies, for all 1 <= i1,i2,j1,j2,k1,k2 <= 4,

```
delta(i2-j1) delta(j2-k1) delta(k2-i1) = sum_{l=1}^{48} (X_l)_{i2,i1} (Y_l)_{j2,j1} (Z_l)_{k2,k1}
```

The 48 terms are indexed by pairs (t, s), t = 1..12 ("seed"), s = 1..4 ("phase"):

- Seeds: `x(1:4,1:4,t)`, t = 1..12 — the 192 complex coefficients listed in the file (Fortran `x(i2,i1,t)`, i.e. first index is the row index i2 of the Brent variable pair (i2,i1)).
- Phase matrices: `z(i,j,s) = (d(i)/d(j))**(s-1)` with `d = [1, i, -1, -i]`, i.e. `z(i,j,s) = i^{(i-j)(s-1)}` — elementwise 4th-root-of-unity scalings (Omega_4 = i; eqs (7)–(8) of the paper, p = 4, q = 12, r = pq = 48).
- Cyclic symmetry: permutation `ip` = (1)(2)(3)(4 5 6)(7 8 9)(10 11 12) — i.e. q = q' + 3q'' = 3 + 3*3 (3 fixed seeds, 3 three-cycles), matching Table 2, row p=4 of the Doklady paper.
- Term (t,s):
  - `(X)_{i2,i1} = z(i2,i1,s) * x(i2,i1, t)`
  - `(Y)_{j2,j1} = z(j2,j1,s) * x(j2,j1, ip(t))`
  - `(Z)_{k2,k1} = z(k2,k1,s) * x(k2,k1, ip(ip(t)))`

So the whole scheme is generated from the 12 seed matrices by (a) the order-3 cyclic tensor symmetry sigma acting through `ip`, and (b) the diagonal root-of-unity sandwich group of order p=4. Note eq (7) in the paper writes the phase exponent as (i1-i2)s while the code uses (i2-i1)(s-1); the code is self-consistent (it checks itself) — treat the code as authoritative.

The program computes the full Brent residual over all 4^6 = 4096 equations; author-reported outputs (comment block at end of file):
```
g95:   ||x||_C, ||err|| = 0.6291035812497071   2.19e-15
fl32:                     0.6291035812497071   5.85e-15
ifl:                      0.629103581249707    5.81e-15
ftn95:                    0.629103581250       4.44e-15
```

Integrity check done here (parse only, per task instructions — no verification/conversion): all 192 assignments `x(i2,i1,t)` present for t = 1..12, i1,i2 = 1..4.

## Exactness

- **The published coefficients are numerical (IEEE double), not exact.** Residual ||f||_2 ~ 2e-15 (machine precision for this problem size). Max coefficient modulus 0.6291..., i.e. the solution is nicely bounded (||x||_inf < 1), which is what makes the doubles trustworthy to ~15-16 digits.
- The Doklady paper (end of Sec. 3) states that equivalence transformations should yield explicit expressions of the elements as **algebraic numbers**, and that **for this p=4 scheme, 144 of the 192 seed components have been so identified** — but the algebraic forms themselves are NOT published anywhere I could find.
- Spot-checks here confirm recognizable algebraic values at full double precision, e.g.:
  - `x(1,1,1) = -1/4 - i*sqrt(3)/4` (a scaled 6th root of unity),
  - `x(2,2,1) = (sqrt(3)-1)/8 - i*(sqrt(3)+1)/8`,
  - `x(2,2,2) = (1+i)/4`, `x(3,3,2) = 1/2`, `x(4,4,2) = (1-i)/4`,
  - `x(2,2,3) = -2^(-5/3)*(1+i)` and `x(4,4,3) = 2^(-5/3)*(-1+i)` — **cube roots of 2 appear**, so the field is bigger than a cyclotomic field.
  - Many entries are numerically zero (~1e-17): whole columns of some seeds (a sparsity pattern), and seeds 10–12 satisfy `x(3,3,t) = x(1,1,t)`.
- Note: Table 2 of the Doklady paper lists ||x||_inf = 0.75 (p=4) / 0.77 (p=2) for the runs reported there; the file's solution has ||x||_inf = 0.6291, i.e. it is a (presumably refined) instance, not byte-identical to the Table 2 run.
- Related: arXiv **2602.13171** (Moran–Schwartz–Yuan, Feb 2026, "Complex to Rational Fast Matrix Multiplication") proves **no real scheme is De-Groote-equivalent to Kaporin's (4,4,4;48) complex scheme** — so don't expect a rationalization of *this* scheme; the known rational rank-48 schemes (arXiv 2506.13242, 2603.18699, AlphaEvolve appendix of 2602.13171) descend from the DeepMind/AlphaEvolve complex scheme, a different lineage.

## Where I looked (search log)

- arXiv: no Kaporin preprints (author page 404; keyword searches return only citing papers).
- SpringerLink CMMP 64(9) 1881–1891: paywalled (redirects to idp.springer.com auth).
- Math-Net.Ru: zvmmf11823 (method paper) and danma547 (Doklady) metadata pages exist; no free full text for zvmmf (moratorium); Kaporin person page = person34916.
- jdigitaldiagnostics.com mirror: unreachable (timeouts/DNS fail) from here.
- journals.rcsi.science: hosts the Doklady full text (saved here); the zvmmf article ID 665187 does not resolve there.
- cloud.mail.ru share from Doklady ref [8]: **hit** (the file above).
- ResearchGate not needed after the direct hit.

## Contact

- Author email (from Doklady paper footnote): **igorkaporin@mail.ru** (I. E. Kaporin, FRC CSC RAS = Federal Research Center "Computer Science and Control", Moscow — note: FRC CSC RAS, not INM RAS). Ask him for: the algebraic forms of the 144 identified components, and the (2,4,5;32) scheme file if wanted.

## Reconstruction confidence

High. `test444r48.for` is the author's own self-verifying artifact: 12 seed matrices at full double precision + exact integer/root-of-unity generator data (`d`, `z`, `ip`) + the expansion loop spelled out in code, with author-reported residuals ~2e-15 on four compilers. Expanding to the explicit 48 x (16+16+16) coefficient tensor is a 20-line script (deliberately not done here per task scope). The only thing NOT recoverable from what's saved is the exact-algebraic closed form of all entries (only ~144/192 known to Kaporin, unpublished).
