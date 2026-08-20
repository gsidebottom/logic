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

## MEASURED: tilechip verdict (2026-08-19)

The tilechip prototype (`matmul/benchair/src/bin/tilechip.rs`,
`rosowski46_schedule`) settles it for the 4x4 tile-interface chip.
Setup: the 48 io ops ride one-per-compute-row, so rows/tile is floored
at max(rpt, 48) + 48 = 96 regardless of product count — rank-48 sits
exactly on that floor, and rosowski-46 pads to the same 96 rows.
The commutative mixed A|B linear forms need lr_w = 32 (vs 16),
i.e. 32-term lsum/rsum constraints and preprocessed width 135 vs 103.
Gates: schedule selfcheck (reproduces A*B on random tiles), honest
proof accepted, all 4 tamper classes rejected — for all three
schedules.

    2^14: rank48 1651 t/s, rosowski46 1611 t/s  (0.976x)
    2^16: rank48 1607 t/s, rosowski46 1532 t/s  (0.953x)
    2^18: rank48 1564 t/s, rosowski46 1536 t/s  (0.982x)
    (rank48/naive: 1.166-1.169x, matching the 112/96 = 1.167x
     row prediction at every height)

**Verdict: at the 4x4 tile size, Rosowski LOSES 2-5%.** Below 48
products the io floor makes further product reduction worthless, and
the doubled linear-form width is pure cost. Rank-48 bilinear is the
optimum for this geometry.

The amortized-40 variant (S-products shared across activation tiles)
was analyzed and NOT built: reading a shared S-product through the
memory argument costs one memory row per use — at least as much as
the single compute row it saves — so sharing cannot win in this
row-cost model either. The 40/18/72 numbers above price
constraint-COUNT models (R1CS-style), not tilechip rows.

**Where commutative wins rows: bigger tiles.** The io floor is
2*3n^2 rows (3n^2 io carriers + 3n^2 memory rows) and scales n^2,
while products scale ~n^3/2 commutative — so at 8x8 the floor stops
binding: naive 512 products -> 704 rows/tile;
bilinear Strassen^2-343 -> 535; Rosowski Thm 2 gives
8*(64+8+8-1)/2 = 316 -> 508 rows/tile (1.39x over naive, 1.05x over
rank-343, before the width tax of ~2-5% measured here). An 8x8
tilechip is the natural follow-up if tile-size flexibility is on the
table.

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
