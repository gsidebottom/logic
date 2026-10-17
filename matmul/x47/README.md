# x47 — XOR count of rank-47 ⟨4×4×4⟩ schemes over F₂

Goal: a rank-47 mod-2 scheme for 4×4 matrix multiplication whose three
linear maps cost fewer than **170 XORs** in total, the best known count
(PLinOpt `data/4x4x4_47_mod_2_{L,R,P}`, cited by Dumas, Pernet,
Sedoglavic, Stapleton, Tichavský, arXiv:2609.12027).

A scheme is L (47×16, A side), R (47×16, B side) and P (16×47, output
side) with Vect(C) = P·((L·Vect(A)) ⊙ (R·Vect(B))), row-major vectors.
Cost = XOR(L) + XOR(R) + XOR(P), and by the transposition principle
XOR(P) = XOR(Pᵀ) + 31.

## Current best: 168 = 44 + 44 + 80 (`best/x168/`)

The reference scheme itself (`ref/`, PLinOpt's 170) with programs from
`xor47` (randomized Boyar–Peralta, P side through its transpose).
Checked by `x47check.py` (each program computes its matrix; the scheme
passes all 256 basis-pair Brent checks) and by PLinOpt's
`SLPchecker -q 2`.

## Tools

- `../../src/bin/xor47.rs`: `xor47 bp|scheme|orbit`. Boyar–Peralta
  with exact distances from a 2¹⁶ table, `--slack/--p` randomized tie
  breaking, `--pilot W` lookahead, unused-gate removal, PLinOpt-syntax
  output, Tellegen transposition for P. `orbit` searches the scheme's
  symmetry orbit (A→XAY⁻¹, B→YBZ⁻¹ over GL(4,2), plus the six
  cyclic/transpose slot symmetries) by coordinate descent with random
  restarts, every point Brent-gated.
- `x47check.py`: independent checker (counts, matrices, Brent).
- `scheme47.py`: .bits ↔ sms conversion, Brent check, class invariant
  (rank-triple multiset up to slot permutation).

## Classes tried (best orbit point found)

| class | given | best | sides L + R + P |
|---|---|---|---|
| PLinOpt reference (`seeds/ref47`) | 168 | 168 | 44 + 44 + 80 |
| AlphaTensor 47 (`seeds/at47`) | 179 | 169 | 45 + 49 + 75 |
| Kauers–Moosbauer 47 (`seeds/km47`) | 186 | 169 | 44 + 49 + 76 |

All three are flip-isolated (no two products share a factor), so plain
flip walks cannot leave them; a rank-47 walk with up-and-down excursions
(`flip 4 4 4 --walk --rank 47`, max excess 2) found nothing new in 5 min.
