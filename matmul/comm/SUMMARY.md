# Commutative (non-bilinear) schemes for zkML constraint counting

Source of the lead: Lacelle's matmul catalog (arXiv:2606.13408,
github.com/solven-eu/matmulcatalog) tracks a commutative axis
(Waksman/Makarov/Rosowski) separately because it does not lift to block
recursion. The zkML observation: an R1CS/AIR multiplication gate
multiplies two ARBITRARY linear forms over the witness — and scalar
witness entries commute — so commutative schemes are legal wherever the
tile entries are field scalars (i.e. at the leaf/flat level, which is
exactly how the benchair tilechip works).

## Verified constructions (rosowski.py — implemented from the formulas,
## gated by exact evaluation over Z and mod BabyBear; NOT imported)

| shape | commutative | NC best (catalog) | B-only products |
|---|---:|---:|---:|
| <3,3,3> (Alg 1)  |  21 | 23 (Laderman)        | 3  |
| <4,4,4> (Thm 2)  |  46 | 48 (DPS, Q) / 49 (Z) | 6  |
| <4,4,8> (Thm 2)  |  86 | 96 (Dronperminov-ZT) | 14 |
| <16,4,4> (Thm 2) | 166 | 192 (4x48 blocked)   | 6  |

Thm 2 (n even) is DIVISIONS-FREE: valid over any commutative ring,
including Z and BabyBear (verified mod P directly).

## The amortization structure (the real prize)

Rosowski products split into families; the S-family involves ONLY
B-entries. In a blocked activation-times-weights product X*W, each
W-tile multiplies many X-tiles (T = rows(X)/tile), and the S-products
depend only on the W-tile: computed once, reused across all T. So the
per-tile multiplication-constraint count under weight reuse:

  <4,4,4>: 46 standalone -> 40 + 6/T  -> 40    (vs 48: -16.7%)
  <3,3,3>: 21 standalone -> 18 + 3/T  -> 18    (vs 23: -21.7%)
  <4,4,8>: 86 standalone -> 72 + 14/T -> 72    (vs 96: -25.0%)

## Caveats (honest scope)

- Non-bilinear => NO block recursion. Applies at the flat/leaf tile
  level only; block levels of a recursive scheme stay non-commutative.
- Constraint COUNT is priced here; the mixed A/W linear forms make
  constraint rows somewhat denser, and the zkML paper's density tax
  (rank-48 losing 17.6x wall-clock at n=64 despite fewer constraints)
  says wall-clock must be MEASURED on the tilechip before adoption.
- Witness-generation cost is unchanged in kind (same products computed
  by the prover); the win is in constraints/AIR rows.

Bonus catalog cross-checks: <2,2,3> NC = 11 (confirming the earlier
web-extraction error), catalog <3,3,3> adds column is +95 raw nonzeros
(vs our optimized 55-add SLP — different metric, our result would slot
into their addition tracking).
