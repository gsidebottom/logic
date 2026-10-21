/-
Copyright (c) 2026 Greg Sidebottom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Greg Sidebottom
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# A 201-operation rank-48 scheme computes 4×4 matrix multiplication

Machine-checked correctness of a rank-48 scheme for `4×4` matrix
multiplication with coefficients in `ℤ[1/2]`, whose three linear programs
use 55 + 57 + 89 = 201 operations
(53 + 55 + 89 additions/subtractions and 2 + 2 + 0 halvings;
copies are free).  Generated from
`matmul/dps48/cand48/p005_201n_{L,R,P}.slp` by `matmul/dps48/lean_gen48_201.py`.

The statement is over an arbitrary **commutative ring** `R` with an
element `h` satisfying `2 * h = 1` -- i.e. any ring in which 2 is
invertible: `ℤ[1/2]`-algebras, and every field of characteristic ≠ 2.
The hypotheses are the exact straight-line programs: `al*` are the
55 operations forming the left factors (a halving `t := u/2` is
`t = u * h`), `bl*` the 57 forming the right factors, `m*` the 48
products (each with its `A`-factor on the left), `cl*` the 89
operations combining them.  Each wire is first shown equal to a canonical
linear form in the inputs (`ring`, or `linear_combination … * h2` where
halves recombine), then each of the 16 outputs equals `∑ₜ aᵢₜ bₜⱼ` by
`linear_combination` of `2 * h = 1` with a coefficient polynomial computed
by the generator (exact division by `2h - 1`).
-/

namespace Matmul48_201

variable {R : Type _} [CommRing R]

/-- Each of the 16 outputs equals the corresponding entry of `A * B`, in any
commutative ring where `2 * h = 1`. -/
theorem correct (h : R) (h2 : 2 * h = 1)
    (a00 a01 a02 a03 a10 a11 a12 a13 a20 a21 a22 a23 a30 a31 a32 a33 b00
     b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33 : R)
    (al1 al2 al3 al4 al5 al6 al7 al8 al9 al10 al11 al12 al13 al14 al15
     al16 al17 al18 al19 al20 al21 al22 al23 al24 al25 al26 al27 al28
     al29 al30 al31 al32 al33 al34 al35 al36 al37 al38 al39 al40 al41
     al42 al43 al44 al45 al46 al47 al48 al49 al50 al51 al52 al53 al54
     al55 bl1 bl2 bl3 bl4 bl5 bl6 bl7 bl8 bl9 bl10 bl11 bl12 bl13 bl14
     bl15 bl16 bl17 bl18 bl19 bl20 bl21 bl22 bl23 bl24 bl25 bl26 bl27
     bl28 bl29 bl30 bl31 bl32 bl33 bl34 bl35 bl36 bl37 bl38 bl39 bl40
     bl41 bl42 bl43 bl44 bl45 bl46 bl47 bl48 bl49 bl50 bl51 bl52 bl53
     bl54 bl55 bl56 bl57 m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13
     m14 m15 m16 m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30
     m31 m32 m33 m34 m35 m36 m37 m38 m39 m40 m41 m42 m43 m44 m45 m46 m47
     cl1 cl2 cl3 cl4 cl5 cl6 cl7 cl8 cl9 cl10 cl11 cl12 cl13 cl14 cl15
     cl16 cl17 cl18 cl19 cl20 cl21 cl22 cl23 cl24 cl25 cl26 cl27 cl28
     cl29 cl30 cl31 cl32 cl33 cl34 cl35 cl36 cl37 cl38 cl39 cl40 cl41
     cl42 cl43 cl44 cl45 cl46 cl47 cl48 cl49 cl50 cl51 cl52 cl53 cl54
     cl55 cl56 cl57 cl58 cl59 cl60 cl61 cl62 cl63 cl64 cl65 cl66 cl67
     cl68 cl69 cl70 cl71 cl72 cl73 cl74 cl75 cl76 cl77 cl78 cl79 cl80
     cl81 cl82 cl83 cl84 cl85 cl86 cl87 cl88 cl89 : R)
    (hal1 : al1 = a21 - a22)
    (hal2 : al2 = a30 - a33)
    (hal3 : al3 = a12 - a11)
    (hal4 : al4 = a13 + al3)
    (hal5 : al5 = a00 - a01)
    (hal6 : al6 = a02 + a03)
    (hal7 : al7 = a10 - a11)
    (hal8 : al8 = a23 - a20)
    (hal9 : al9 = a32 + a33)
    (hal10 : al10 = al9 - a31)
    (hal11 : al11 = a03 - a13)
    (hal12 : al12 = a21 - a31)
    (hal13 : al13 = a02 - a22)
    (hal14 : al14 = al12 * h)
    (hal15 : al15 = al14 + al9)
    (hal16 : al16 = al14 - al7)
    (hal17 : al17 = al14 - a22)
    (hal18 : al18 = al11 * h)
    (hal19 : al19 = al18 - al8)
    (hal20 : al20 = al13 - a32)
    (hal21 : al21 = al18 - al6)
    (hal22 : al22 = al13 - a12)
    (hal23 : al23 = al19 - a20)
    (hal24 : al24 = a21 - al14)
    (hal25 : al25 = a10 + al16)
    (hal26 : al26 = al15 + al21)
    (hal27 : al27 = al5 + al24)
    (hal28 : al28 = al4 + al18)
    (hal29 : al29 = al26 - al28)
    (hal30 : al30 = al22 + al25)
    (hal31 : al31 = al17 - al26)
    (hal32 : al32 = al30 + al26)
    (hal33 : al33 = a00 - al27)
    (hal34 : al34 = al31 - al20)
    (hal35 : al35 = al29 - al25)
    (hal36 : al36 = al32 + al23)
    (hal37 : al37 = al31 + al23)
    (hal38 : al38 = al29 + al33)
    (hal39 : al39 = al32 + al34)
    (hal40 : al40 = a30 + al34)
    (hal41 : al41 = al30 - al33)
    (hal42 : al42 = al16 + al40)
    (hal43 : al43 = al27 - al42)
    (hal44 : al44 = al43 + al34)
    (hal45 : al45 = al19 - al42)
    (hal46 : al46 = al43 - al40)
    (hal47 : al47 = al45 + al25)
    (hal48 : al48 = al46 - al45)
    (hal49 : al49 = al14 - al45)
    (hal50 : al50 = al2 + al46)
    (hal51 : al51 = al48 + al42)
    (hal52 : al52 = al48 + al33)
    (hal53 : al53 = al18 - al51)
    (hal54 : al54 = al48 + al24)
    (hal55 : al55 = al51 + al23)
    (hbl1 : bl1 = b01 + b11)
    (hbl2 : bl2 = b21 + bl1)
    (hbl3 : bl3 = b00 + b10)
    (hbl4 : bl4 = b32 - b22)
    (hbl5 : bl5 = b02 + b12)
    (hbl6 : bl6 = b00 + b30)
    (hbl7 : bl7 = b03 + b33)
    (hbl8 : bl8 = b03 + b13)
    (hbl9 : bl9 = bl6 - b20)
    (hbl10 : bl10 = b23 + bl8)
    (hbl11 : bl11 = b21 - b31)
    (hbl12 : bl12 = b01 - b03)
    (hbl13 : bl13 = b20 + b22)
    (hbl14 : bl14 = b32 + b33)
    (hbl15 : bl15 = bl14 - b31)
    (hbl16 : bl16 = bl14 - b30)
    (hbl17 : bl17 = bl11 - b01)
    (hbl18 : bl18 = bl12 * h)
    (hbl19 : bl19 = bl13 * h)
    (hbl20 : bl20 = b20 - bl19)
    (hbl21 : bl21 = bl7 + bl18)
    (hbl22 : bl22 = b12 + bl18)
    (hbl23 : bl23 = bl19 - b21)
    (hbl24 : bl24 = bl15 - bl23)
    (hbl25 : bl25 = bl17 + bl18)
    (hbl26 : bl26 = bl23 - bl1)
    (hbl27 : bl27 = bl10 - bl20)
    (hbl28 : bl28 = bl6 - bl19)
    (hbl29 : bl29 = b32 - bl19)
    (hbl30 : bl30 = bl22 - bl5)
    (hbl31 : bl31 = bl8 - bl27)
    (hbl32 : bl32 = bl28 - bl21)
    (hbl33 : bl33 = bl29 - bl32)
    (hbl34 : bl34 = bl24 + bl32)
    (hbl35 : bl35 = bl30 - bl33)
    (hbl36 : bl36 = bl24 + bl31)
    (hbl37 : bl37 = bl25 + bl32)
    (hbl38 : bl38 = bl23 + bl37)
    (hbl39 : bl39 = bl34 - bl30)
    (hbl40 : bl40 = bl16 - bl33)
    (hbl41 : bl41 = bl37 - bl31)
    (hbl42 : bl42 = bl34 - bl40)
    (hbl43 : bl43 = bl3 - bl40)
    (hbl44 : bl44 = bl43 - bl27)
    (hbl45 : bl45 = bl44 - bl22)
    (hbl46 : bl46 = bl26 + bl44)
    (hbl47 : bl47 = bl43 + bl46)
    (hbl48 : bl48 = bl45 - bl31)
    (hbl49 : bl49 = bl47 - bl45)
    (hbl50 : bl50 = bl46 + bl40)
    (hbl51 : bl51 = bl47 - b10)
    (hbl52 : bl52 = bl49 - bl44)
    (hbl53 : bl53 = bl49 + bl19)
    (hbl54 : bl54 = bl45 + bl20)
    (hbl55 : bl55 = bl52 + bl18)
    (hbl56 : bl56 = bl52 - bl30)
    (hbl57 : bl57 = bl49 - bl23)
    (hm0 : m0 = al1 * bl48)
    (hm1 : m1 = al2 * bl42)
    (hm2 : m2 = al4 * bl15)
    (hm3 : m3 = al51 * bl21)
    (hm4 : m4 = al35 * bl2)
    (hm5 : m5 = al52 * bl3)
    (hm6 : m6 = al36 * bl38)
    (hm7 : m7 = a10 * bl56)
    (hm8 : m8 = al15 * bl49)
    (hm9 : m9 = a02 * bl4)
    (hm10 : m10 = al47 * bl50)
    (hm11 : m11 = al27 * bl22)
    (hm12 : m12 = al6 * b32)
    (hm13 : m13 = al53 * b33)
    (hm14 : m14 = al28 * bl24)
    (hm15 : m15 = a00 * bl5)
    (hm16 : m16 = al43 * bl25)
    (hm17 : m17 = al54 * b10)
    (hm18 : m18 = al48 * bl43)
    (hm19 : m19 = al49 * bl51)
    (hm20 : m20 = al8 * bl16)
    (hm21 : m21 = al16 * bl52)
    (hm22 : m22 = al37 * bl6)
    (hm23 : m23 = al9 * bl53)
    (hm24 : m24 = al29 * bl26)
    (hm25 : m25 = a22 * bl54)
    (hm26 : m26 = al44 * bl17)
    (hm27 : m27 = al17 * bl45)
    (hm28 : m28 = al10 * bl57)
    (hm29 : m29 = al55 * bl7)
    (hm30 : m30 = a30 * bl39)
    (hm31 : m31 = al45 * bl46)
    (hm32 : m32 = al38 * bl1)
    (hm33 : m33 = al19 * bl33)
    (hm34 : m34 = al30 * bl27)
    (hm35 : m35 = al7 * bl55)
    (hm36 : m36 = al20 * bl9)
    (hm37 : m37 = al31 * bl28)
    (hm38 : m38 = al39 * bl41)
    (hm39 : m39 = al40 * bl34)
    (hm40 : m40 = al5 * b12)
    (hm41 : m41 = a20 * bl35)
    (hm42 : m42 = al3 * bl36)
    (hm43 : m43 = al21 * bl29)
    (hm44 : m44 = al41 * bl8)
    (hm45 : m45 = al22 * bl10)
    (hm46 : m46 = al50 * bl11)
    (hm47 : m47 = al32 * bl37)
    (hcl1 : cl1 = m43 + m12)
    (hcl2 : cl2 = m9 - m12)
    (hcl3 : cl3 = cl2 + m40)
    (hcl4 : cl4 = m11 - cl3)
    (hcl5 : cl5 = m15 - cl3)
    (hcl6 : cl6 = m3 + m13)
    (hcl7 : cl7 = m29 + m13)
    (hcl8 : cl8 = cl4 + m31)
    (hcl9 : cl9 = cl8 + m19)
    (hcl10 : cl10 = m21 + m35)
    (hcl11 : cl11 = m27 + cl6)
    (hcl12 : cl12 = cl11 + m25)
    (hcl13 : cl13 = cl2 - cl12)
    (hcl14 : cl14 = cl9 + cl13)
    (hcl15 : cl15 = cl10 - cl14)
    (hcl16 : cl16 = cl12 + cl15)
    (hcl17 : cl17 = m17 + cl16)
    (hcl18 : cl18 = cl17 - m18)
    (hcl19 : cl19 = m20 - cl18)
    (hcl20 : cl20 = m25 + m0)
    (hcl21 : cl21 = cl18 - cl20)
    (hcl22 : cl22 = m33 + cl19)
    (hcl23 : cl23 = cl1 - cl15)
    (hcl24 : cl24 = m8 - cl14)
    (hcl25 : cl25 = cl24 - m23)
    (hcl26 : cl26 = m16 + cl25)
    (hcl27 : cl27 = m34 + cl22)
    (hcl28 : cl28 = cl25 - cl22)
    (hcl29 : cl29 = cl28 + cl23)
    (hcl30 : cl30 = cl23 - m47)
    (hcl31 : cl31 = cl13 + cl29)
    (hcl32 : cl32 = m46 - cl26)
    (hcl33 : cl33 = m26 - cl26)
    (hcl34 : cl34 = cl18 + cl32)
    (hcl35 : cl35 = cl6 + cl1)
    (hcl36 : cl36 = cl35 + cl31)
    (hcl37 : cl37 = m37 + cl4)
    (hcl38 : cl38 = cl37 + cl31)
    (hcl39 : cl39 = m39 + cl36)
    (hcl40 : cl40 = m24 + cl36)
    (hcl41 : cl41 = m28 - m23)
    (hcl42 : cl42 = cl41 + cl34)
    (hcl43 : cl43 = cl34 - m1)
    (hcl44 : cl44 = cl43 + cl39)
    (hcl45 : cl45 = cl27 - m45)
    (hcl46 : cl46 = m4 + cl40)
    (hcl47 : cl47 = cl44 - cl17)
    (hcl48 : cl48 = cl47 + m5)
    (hcl49 : cl49 = m10 - cl8)
    (hcl50 : cl50 = cl49 + cl45)
    (hcl51 : cl51 = cl50 + cl44)
    (hcl52 : cl52 = cl51 - cl46)
    (hcl53 : cl53 = m14 - cl4)
    (hcl54 : cl54 = cl53 + cl29)
    (hcl55 : cl55 = cl54 + cl32)
    (hcl56 : cl56 = m21 + m7)
    (hcl57 : cl57 = cl56 - cl46)
    (hcl58 : cl58 = cl57 - cl45)
    (hcl59 : cl59 = cl55 - m42)
    (hcl60 : cl60 = cl10 - m2)
    (hcl61 : cl61 = cl60 + cl55)
    (hcl62 : cl62 = cl59 + cl45)
    (hcl63 : cl63 = m36 - cl16)
    (hcl64 : cl64 = cl63 - cl38)
    (hcl65 : cl65 = cl38 - m22)
    (hcl66 : cl66 = cl44 + cl64)
    (hcl67 : cl67 = cl33 - cl64)
    (hcl68 : cl68 = cl42 + cl33)
    (hcl69 : cl69 = cl65 + cl7)
    (hcl70 : cl70 = cl42 - cl61)
    (hcl71 : cl71 = cl61 - cl46)
    (hcl72 : cl72 = cl59 + cl21)
    (hcl73 : cl73 = cl21 - cl7)
    (hcl74 : cl74 = m32 + cl40)
    (hcl75 : cl75 = cl74 + cl32)
    (hcl76 : cl76 = cl75 + cl70)
    (hcl77 : cl77 = m30 - cl39)
    (hcl78 : cl78 = cl77 + cl67)
    (hcl79 : cl79 = cl27 - m44)
    (hcl80 : cl80 = cl79 + cl72)
    (hcl81 : cl81 = cl19 - m41)
    (hcl82 : cl82 = cl81 + cl69)
    (hcl83 : cl83 = m38 - cl67)
    (hcl84 : cl84 = cl83 + cl72)
    (hcl85 : cl85 = cl84 + cl30)
    (hcl86 : cl86 = m6 - cl9)
    (hcl87 : cl87 = cl86 + cl70)
    (hcl88 : cl88 = cl87 + cl69)
    (hcl89 : cl89 = cl88 + cl30)
    :
    cl48 = a00 * b00 + a01 * b10 + a02 * b20 + a03 * b30 ∧
    cl76 = a00 * b01 + a01 * b11 + a02 * b21 + a03 * b31 ∧
    cl5 = a00 * b02 + a01 * b12 + a02 * b22 + a03 * b32 ∧
    cl80 = a00 * b03 + a01 * b13 + a02 * b23 + a03 * b33 ∧
    cl52 = a10 * b00 + a11 * b10 + a12 * b20 + a13 * b30 ∧
    cl71 = a10 * b01 + a11 * b11 + a12 * b21 + a13 * b31 ∧
    cl58 = a10 * b02 + a11 * b12 + a12 * b22 + a13 * b32 ∧
    cl62 = a10 * b03 + a11 * b13 + a12 * b23 + a13 * b33 ∧
    cl65 = a20 * b00 + a21 * b10 + a22 * b20 + a23 * b30 ∧
    cl89 = a20 * b01 + a21 * b11 + a22 * b21 + a23 * b31 ∧
    cl82 = a20 * b02 + a21 * b12 + a22 * b22 + a23 * b32 ∧
    cl73 = a20 * b03 + a21 * b13 + a22 * b23 + a23 * b33 ∧
    cl66 = a30 * b00 + a31 * b10 + a32 * b20 + a33 * b30 ∧
    cl68 = a30 * b01 + a31 * b11 + a32 * b21 + a33 * b31 ∧
    cl78 = a30 * b02 + a31 * b12 + a32 * b22 + a33 * b32 ∧
    cl85 = a30 * b03 + a31 * b13 + a32 * b23 + a33 * b33 := by
  have eal1 : al1 = a21 + -(a22) := by
    rw [hal1]; ring
  have eal2 : al2 = a30 + -(a33) := by
    rw [hal2]; ring
  have eal3 : al3 = -(a11) + a12 := by
    rw [hal3]; ring
  have eal4 : al4 = -(a11) + a12 + a13 := by
    rw [hal4, eal3]; ring
  have eal5 : al5 = a00 + -(a01) := by
    rw [hal5]; ring
  have eal6 : al6 = a02 + a03 := by
    rw [hal6]
  have eal7 : al7 = a10 + -(a11) := by
    rw [hal7]; ring
  have eal8 : al8 = -(a20) + a23 := by
    rw [hal8]; ring
  have eal9 : al9 = a32 + a33 := by
    rw [hal9]
  have eal10 : al10 = -(a31) + a32 + a33 := by
    rw [hal10, eal9]; ring
  have eal11 : al11 = a03 + -(a13) := by
    rw [hal11]; ring
  have eal12 : al12 = a21 + -(a31) := by
    rw [hal12]; ring
  have eal13 : al13 = a02 + -(a22) := by
    rw [hal13]; ring
  have eal14 : al14 = h * a21 + -(h * a31) := by
    rw [hal14, eal12]; ring
  have eal15 : al15 = h * a21 + -(h * a31) + a32 + a33 := by
    rw [hal15, eal14, eal9]; ring
  have eal16 : al16 = -(a10) + a11 + h * a21 + -(h * a31) := by
    rw [hal16, eal14, eal7]; ring
  have eal17 : al17 = h * a21 + -(a22) + -(h * a31) := by
    rw [hal17, eal14]; ring
  have eal18 : al18 = h * a03 + -(h * a13) := by
    rw [hal18, eal11]; ring
  have eal19 : al19 = h * a03 + -(h * a13) + a20 + -(a23) := by
    rw [hal19, eal18, eal8]; ring
  have eal20 : al20 = a02 + -(a22) + -(a32) := by
    rw [hal20, eal13]; ring
  have eal21 : al21 = -(a02) + -(h * a03) + -(h * a13) := by
    rw [hal21, eal18, eal6]; linear_combination (a03) * h2
  have eal22 : al22 = a02 + -(a12) + -(a22) := by
    rw [hal22, eal13]; ring
  have eal23 : al23 = h * a03 + -(h * a13) + -(a23) := by
    rw [hal23, eal19]; ring
  have eal24 : al24 = h * a21 + h * a31 := by
    rw [hal24, eal14]; linear_combination (-(a21)) * h2
  have eal25 : al25 = a11 + h * a21 + -(h * a31) := by
    rw [hal25, eal16]; ring
  have eal26 : al26 = -(a02) + -(h * a03) + -(h * a13) + h * a21 + -(h * a31) + a32 + a33 := by
    rw [hal26, eal15, eal21]; ring
  have eal27 : al27 = a00 + -(a01) + h * a21 + h * a31 := by
    rw [hal27, eal5, eal24]; ring
  have eal28 : al28 = h * a03 + -(a11) + a12 + h * a13 := by
    rw [hal28, eal4, eal18]; linear_combination (-(a13)) * h2
  have eal29 : al29 = -(a02) + -(a03) + a11 + -(a12) + -(a13) + h * a21 + -(h * a31) + a32 +
      a33 := by
    rw [hal29, eal26, eal28]; linear_combination (-(a03) + -(a13)) * h2
  have eal30 : al30 = a02 + a11 + -(a12) + h * a21 + -(a22) + -(h * a31) := by
    rw [hal30, eal22, eal25]; ring
  have eal31 : al31 = a02 + h * a03 + h * a13 + -(a22) + -(a32) + -(a33) := by
    rw [hal31, eal17, eal26]; ring
  have eal32 : al32 = -(h * a03) + a11 + -(a12) + -(h * a13) + a21 + -(a22) + -(a31) + a32 +
      a33 := by
    rw [hal32, eal30, eal26]; linear_combination (a21 + -(a31)) * h2
  have eal33 : al33 = a01 + -(h * a21) + -(h * a31) := by
    rw [hal33, eal27]; ring
  have eal34 : al34 = h * a03 + h * a13 + -(a33) := by
    rw [hal34, eal31, eal20]; ring
  have eal35 : al35 = -(a02) + -(a03) + -(a12) + -(a13) + a32 + a33 := by
    rw [hal35, eal29, eal25]; ring
  have eal36 : al36 = a11 + -(a12) + -(a13) + a21 + -(a22) + -(a23) + -(a31) + a32 + a33 := by
    rw [hal36, eal32, eal23]; linear_combination (-(a13)) * h2
  have eal37 : al37 = a02 + a03 + -(a22) + -(a23) + -(a32) + -(a33) := by
    rw [hal37, eal31, eal23]; linear_combination (a03) * h2
  have eal38 : al38 = a01 + -(a02) + -(a03) + a11 + -(a12) + -(a13) + -(a31) + a32 + a33 := by
    rw [hal38, eal29, eal33]; linear_combination (-(a31)) * h2
  have eal39 : al39 = a11 + -(a12) + a21 + -(a22) + -(a31) + a32 := by
    rw [hal39, eal32, eal34]; ring
  have eal40 : al40 = h * a03 + h * a13 + a30 + -(a33) := by
    rw [hal40, eal34]; ring
  have eal41 : al41 = -(a01) + a02 + a11 + -(a12) + a21 + -(a22) := by
    rw [hal41, eal30, eal33]; linear_combination (a21) * h2
  have eal42 : al42 = h * a03 + -(a10) + a11 + h * a13 + h * a21 + a30 + -(h * a31) + -(a33) := by
    rw [hal42, eal16, eal40]; ring
  have eal43 : al43 = a00 + -(a01) + -(h * a03) + a10 + -(a11) + -(h * a13) + -(a30) + a31 +
      a33 := by
    rw [hal43, eal27, eal42]; linear_combination (a31) * h2
  have eal44 : al44 = a00 + -(a01) + a10 + -(a11) + -(a30) + a31 := by
    rw [hal44, eal43, eal34]; ring
  have eal45 : al45 = a10 + -(a11) + -(a13) + a20 + -(h * a21) + -(a23) + -(a30) + h * a31 +
      a33 := by
    rw [hal45, eal19, eal42]; linear_combination (-(a13)) * h2
  have eal46 : al46 = a00 + -(a01) + -(a03) + a10 + -(a11) + -(a13) + (-2) * a30 + a31 +
      (2) * a33 := by
    rw [hal46, eal43, eal40]; linear_combination (-(a03) + -(a13)) * h2
  have eal47 : al47 = a10 + -(a13) + a20 + -(a23) + -(a30) + a33 := by
    rw [hal47, eal45, eal25]; ring
  have eal48 : al48 = a00 + -(a01) + -(a03) + -(a20) + h * a21 + a23 + -(a30) + h * a31 + a33 := by
    rw [hal48, eal46, eal45]; linear_combination (-(a31)) * h2
  have eal49 : al49 = -(a10) + a11 + a13 + -(a20) + a21 + a23 + a30 + -(a31) + -(a33) := by
    rw [hal49, eal14, eal45]; linear_combination (a21 + -(a31)) * h2
  have eal50 : al50 = a00 + -(a01) + -(a03) + a10 + -(a11) + -(a13) + -(a30) + a31 + a33 := by
    rw [hal50, eal2, eal46]; ring
  have eal51 : al51 = a00 + -(a01) + -(h * a03) + -(a10) + a11 + h * a13 + -(a20) + a21 + a23 := by
    rw [hal51, eal48, eal42]; linear_combination (a03 + a21) * h2
  have eal52 : al52 = a00 + -(a03) + -(a20) + a23 + -(a30) + a33 := by
    rw [hal52, eal48, eal33]; ring
  have eal53 : al53 = -(a00) + a01 + a03 + a10 + -(a11) + -(a13) + a20 + -(a21) + -(a23) := by
    rw [hal53, eal18, eal51]; linear_combination (a03 + -(a13)) * h2
  have eal54 : al54 = a00 + -(a01) + -(a03) + -(a20) + a21 + a23 + -(a30) + a31 + a33 := by
    rw [hal54, eal48, eal24]; linear_combination (a21 + a31) * h2
  have eal55 : al55 = a00 + -(a01) + -(a10) + a11 + -(a20) + a21 := by
    rw [hal55, eal51, eal23]; ring
  have ebl1 : bl1 = b01 + b11 := by
    rw [hbl1]
  have ebl2 : bl2 = b01 + b11 + b21 := by
    rw [hbl2, ebl1]; ring
  have ebl3 : bl3 = b00 + b10 := by
    rw [hbl3]
  have ebl4 : bl4 = -(b22) + b32 := by
    rw [hbl4]; ring
  have ebl5 : bl5 = b02 + b12 := by
    rw [hbl5]
  have ebl6 : bl6 = b00 + b30 := by
    rw [hbl6]
  have ebl7 : bl7 = b03 + b33 := by
    rw [hbl7]
  have ebl8 : bl8 = b03 + b13 := by
    rw [hbl8]
  have ebl9 : bl9 = b00 + -(b20) + b30 := by
    rw [hbl9, ebl6]; ring
  have ebl10 : bl10 = b03 + b13 + b23 := by
    rw [hbl10, ebl8]; ring
  have ebl11 : bl11 = b21 + -(b31) := by
    rw [hbl11]; ring
  have ebl12 : bl12 = b01 + -(b03) := by
    rw [hbl12]; ring
  have ebl13 : bl13 = b20 + b22 := by
    rw [hbl13]
  have ebl14 : bl14 = b32 + b33 := by
    rw [hbl14]
  have ebl15 : bl15 = -(b31) + b32 + b33 := by
    rw [hbl15, ebl14]; ring
  have ebl16 : bl16 = -(b30) + b32 + b33 := by
    rw [hbl16, ebl14]; ring
  have ebl17 : bl17 = -(b01) + b21 + -(b31) := by
    rw [hbl17, ebl11]; ring
  have ebl18 : bl18 = h * b01 + -(h * b03) := by
    rw [hbl18, ebl12]; ring
  have ebl19 : bl19 = h * b20 + h * b22 := by
    rw [hbl19, ebl13]; ring
  have ebl20 : bl20 = h * b20 + -(h * b22) := by
    rw [hbl20, ebl19]; linear_combination (-(b20)) * h2
  have ebl21 : bl21 = h * b01 + h * b03 + b33 := by
    rw [hbl21, ebl7, ebl18]; linear_combination (-(b03)) * h2
  have ebl22 : bl22 = h * b01 + -(h * b03) + b12 := by
    rw [hbl22, ebl18]; ring
  have ebl23 : bl23 = h * b20 + -(b21) + h * b22 := by
    rw [hbl23, ebl19]; ring
  have ebl24 : bl24 = -(h * b20) + b21 + -(h * b22) + -(b31) + b32 + b33 := by
    rw [hbl24, ebl15, ebl23]; ring
  have ebl25 : bl25 = -(h * b01) + -(h * b03) + b21 + -(b31) := by
    rw [hbl25, ebl17, ebl18]; linear_combination (b01) * h2
  have ebl26 : bl26 = -(b01) + -(b11) + h * b20 + -(b21) + h * b22 := by
    rw [hbl26, ebl23, ebl1]; ring
  have ebl27 : bl27 = b03 + b13 + -(h * b20) + h * b22 + b23 := by
    rw [hbl27, ebl10, ebl20]; ring
  have ebl28 : bl28 = b00 + -(h * b20) + -(h * b22) + b30 := by
    rw [hbl28, ebl6, ebl19]; ring
  have ebl29 : bl29 = -(h * b20) + -(h * b22) + b32 := by
    rw [hbl29, ebl19]; ring
  have ebl30 : bl30 = h * b01 + -(b02) + -(h * b03) := by
    rw [hbl30, ebl22, ebl5]; ring
  have ebl31 : bl31 = h * b20 + -(h * b22) + -(b23) := by
    rw [hbl31, ebl8, ebl27]; ring
  have ebl32 : bl32 = b00 + -(h * b01) + -(h * b03) + -(h * b20) + -(h * b22) + b30 + -(b33) := by
    rw [hbl32, ebl28, ebl21]; ring
  have ebl33 : bl33 = -(b00) + h * b01 + h * b03 + -(b30) + b32 + b33 := by
    rw [hbl33, ebl29, ebl32]; ring
  have ebl34 : bl34 = b00 + -(h * b01) + -(h * b03) + -(b20) + b21 + -(b22) + b30 + -(b31) +
      b32 := by
    rw [hbl34, ebl24, ebl32]; linear_combination (-(b20) + -(b22)) * h2
  have ebl35 : bl35 = b00 + -(b02) + -(b03) + b30 + -(b32) + -(b33) := by
    rw [hbl35, ebl30, ebl33]; linear_combination (-(b03)) * h2
  have ebl36 : bl36 = b21 + -(b22) + -(b23) + -(b31) + b32 + b33 := by
    rw [hbl36, ebl24, ebl31]; linear_combination (-(b22)) * h2
  have ebl37 : bl37 = b00 + -(b01) + -(b03) + -(h * b20) + b21 + -(h * b22) + b30 + -(b31) +
      -(b33) := by
    rw [hbl37, ebl25, ebl32]; linear_combination (-(b01) + -(b03)) * h2
  have ebl38 : bl38 = b00 + -(b01) + -(b03) + b30 + -(b31) + -(b33) := by
    rw [hbl38, ebl23, ebl37]; ring
  have ebl39 : bl39 = b00 + -(b01) + b02 + -(b20) + b21 + -(b22) + b30 + -(b31) + b32 := by
    rw [hbl39, ebl34, ebl30]; linear_combination (-(b01)) * h2
  have ebl40 : bl40 = b00 + -(h * b01) + -(h * b03) := by
    rw [hbl40, ebl16, ebl33]; ring
  have ebl41 : bl41 = b00 + -(b01) + -(b03) + -(b20) + b21 + b23 + b30 + -(b31) + -(b33) := by
    rw [hbl41, ebl37, ebl31]; linear_combination (-(b20)) * h2
  have ebl42 : bl42 = -(b20) + b21 + -(b22) + b30 + -(b31) + b32 := by
    rw [hbl42, ebl34, ebl40]; ring
  have ebl43 : bl43 = h * b01 + h * b03 + b10 := by
    rw [hbl43, ebl3, ebl40]; ring
  have ebl44 : bl44 = h * b01 + -(h * b03) + b10 + -(b13) + h * b20 + -(h * b22) + -(b23) := by
    rw [hbl44, ebl43, ebl27]; linear_combination (b03) * h2
  have ebl45 : bl45 = b10 + -(b12) + -(b13) + h * b20 + -(h * b22) + -(b23) := by
    rw [hbl45, ebl44, ebl22]; ring
  have ebl46 : bl46 = -(h * b01) + -(h * b03) + b10 + -(b11) + -(b13) + b20 + -(b21) + -(b23) := by
    rw [hbl46, ebl26, ebl44]; linear_combination (b01 + b20) * h2
  have ebl47 : bl47 = (2) * b10 + -(b11) + -(b13) + b20 + -(b21) + -(b23) := by
    rw [hbl47, ebl43, ebl46]; ring
  have ebl48 : bl48 = b10 + -(b12) + -(b13) := by
    rw [hbl48, ebl45, ebl31]; ring
  have ebl49 : bl49 = b10 + -(b11) + b12 + h * b20 + -(b21) + h * b22 := by
    rw [hbl49, ebl47, ebl45]; linear_combination (-(b20)) * h2
  have ebl50 : bl50 = b00 + -(b01) + -(b03) + b10 + -(b11) + -(b13) + b20 + -(b21) + -(b23) := by
    rw [hbl50, ebl46, ebl40]; linear_combination (-(b01) + -(b03)) * h2
  have ebl51 : bl51 = b10 + -(b11) + -(b13) + b20 + -(b21) + -(b23) := by
    rw [hbl51, ebl47]; ring
  have ebl52 : bl52 = -(h * b01) + h * b03 + -(b11) + b12 + b13 + -(b21) + b22 + b23 := by
    rw [hbl52, ebl49, ebl44]; linear_combination (b22) * h2
  have ebl53 : bl53 = b10 + -(b11) + b12 + b20 + -(b21) + b22 := by
    rw [hbl53, ebl49, ebl19]; linear_combination (b20 + b22) * h2
  have ebl54 : bl54 = b10 + -(b12) + -(b13) + b20 + -(b22) + -(b23) := by
    rw [hbl54, ebl45, ebl20]; linear_combination (b20 + -(b22)) * h2
  have ebl55 : bl55 = -(b11) + b12 + b13 + -(b21) + b22 + b23 := by
    rw [hbl55, ebl52, ebl18]; ring
  have ebl56 : bl56 = -(b01) + b02 + b03 + -(b11) + b12 + b13 + -(b21) + b22 + b23 := by
    rw [hbl56, ebl52, ebl30]; linear_combination (-(b01) + b03) * h2
  have ebl57 : bl57 = b10 + -(b11) + b12 := by
    rw [hbl57, ebl49, ebl23]; ring
  have ecl1 : cl1 = m12 + m43 := by
    rw [hcl1]; ring
  have ecl2 : cl2 = m9 + -(m12) := by
    rw [hcl2]; ring
  have ecl3 : cl3 = m9 + -(m12) + m40 := by
    rw [hcl3, ecl2]
  have ecl4 : cl4 = -(m9) + m11 + m12 + -(m40) := by
    rw [hcl4, ecl3]; ring
  have ecl5 : cl5 = -(m9) + m12 + m15 + -(m40) := by
    rw [hcl5, ecl3]; ring
  have ecl6 : cl6 = m3 + m13 := by
    rw [hcl6]
  have ecl7 : cl7 = m13 + m29 := by
    rw [hcl7]; ring
  have ecl8 : cl8 = -(m9) + m11 + m12 + m31 + -(m40) := by
    rw [hcl8, ecl4]; ring
  have ecl9 : cl9 = -(m9) + m11 + m12 + m19 + m31 + -(m40) := by
    rw [hcl9, ecl8]; ring
  have ecl10 : cl10 = m21 + m35 := by
    rw [hcl10]
  have ecl11 : cl11 = m3 + m13 + m27 := by
    rw [hcl11, ecl6]; ring
  have ecl12 : cl12 = m3 + m13 + m25 + m27 := by
    rw [hcl12, ecl11]; ring
  have ecl13 : cl13 = -(m3) + m9 + -(m12) + -(m13) + -(m25) + -(m27) := by
    rw [hcl13, ecl2, ecl12]; ring
  have ecl14 : cl14 = -(m3) + m11 + -(m13) + m19 + -(m25) + -(m27) + m31 + -(m40) := by
    rw [hcl14, ecl9, ecl13]; ring
  have ecl15 : cl15 = m3 + -(m11) + m13 + -(m19) + m21 + m25 + m27 + -(m31) + m35 + m40 := by
    rw [hcl15, ecl10, ecl14]; ring
  have ecl16 : cl16 = (2) * m3 + -(m11) + (2) * m13 + -(m19) + m21 + (2) * m25 + (2) * m27 +
      -(m31) + m35 + m40 := by
    rw [hcl16, ecl12, ecl15]; ring
  have ecl17 : cl17 = (2) * m3 + -(m11) + (2) * m13 + m17 + -(m19) + m21 + (2) * m25 + (2) * m27 +
      -(m31) + m35 + m40 := by
    rw [hcl17, ecl16]; ring
  have ecl18 : cl18 = (2) * m3 + -(m11) + (2) * m13 + m17 + -(m18) + -(m19) + m21 + (2) * m25 +
      (2) * m27 + -(m31) + m35 + m40 := by
    rw [hcl18, ecl17]; ring
  have ecl19 : cl19 = (-2) * m3 + m11 + (-2) * m13 + -(m17) + m18 + m19 + m20 + -(m21) +
      (-2) * m25 + (-2) * m27 + m31 + -(m35) + -(m40) := by
    rw [hcl19, ecl18]; ring
  have ecl20 : cl20 = m0 + m25 := by
    rw [hcl20]; ring
  have ecl21 : cl21 = -(m0) + (2) * m3 + -(m11) + (2) * m13 + m17 + -(m18) + -(m19) + m21 + m25 +
      (2) * m27 + -(m31) + m35 + m40 := by
    rw [hcl21, ecl18, ecl20]; ring
  have ecl22 : cl22 = (-2) * m3 + m11 + (-2) * m13 + -(m17) + m18 + m19 + m20 + -(m21) +
      (-2) * m25 + (-2) * m27 + m31 + m33 + -(m35) + -(m40) := by
    rw [hcl22, ecl19]; ring
  have ecl23 : cl23 = -(m3) + m11 + m12 + -(m13) + m19 + -(m21) + -(m25) + -(m27) + m31 + -(m35) +
      -(m40) + m43 := by
    rw [hcl23, ecl1, ecl15]; ring
  have ecl24 : cl24 = m3 + m8 + -(m11) + m13 + -(m19) + m25 + m27 + -(m31) + m40 := by
    rw [hcl24, ecl14]; ring
  have ecl25 : cl25 = m3 + m8 + -(m11) + m13 + -(m19) + -(m23) + m25 + m27 + -(m31) + m40 := by
    rw [hcl25, ecl24]; ring
  have ecl26 : cl26 = m3 + m8 + -(m11) + m13 + m16 + -(m19) + -(m23) + m25 + m27 + -(m31) +
      m40 := by
    rw [hcl26, ecl25]; ring
  have ecl27 : cl27 = (-2) * m3 + m11 + (-2) * m13 + -(m17) + m18 + m19 + m20 + -(m21) +
      (-2) * m25 + (-2) * m27 + m31 + m33 + m34 + -(m35) + -(m40) := by
    rw [hcl27, ecl22]; ring
  have ecl28 : cl28 = (3) * m3 + m8 + (-2) * m11 + (3) * m13 + m17 + -(m18) + (-2) * m19 + -(m20) +
      m21 + -(m23) + (3) * m25 + (3) * m27 + (-2) * m31 + -(m33) + m35 + (2) * m40 := by
    rw [hcl28, ecl25, ecl22]; ring
  have ecl29 : cl29 = (2) * m3 + m8 + -(m11) + m12 + (2) * m13 + m17 + -(m18) + -(m19) + -(m20) +
      -(m23) + (2) * m25 + (2) * m27 + -(m31) + -(m33) + m40 + m43 := by
    rw [hcl29, ecl28, ecl23]; ring
  have ecl30 : cl30 = -(m3) + m11 + m12 + -(m13) + m19 + -(m21) + -(m25) + -(m27) + m31 + -(m35) +
      -(m40) + m43 + -(m47) := by
    rw [hcl30, ecl23]; ring
  have ecl31 : cl31 = m3 + m8 + m9 + -(m11) + m13 + m17 + -(m18) + -(m19) + -(m20) + -(m23) + m25 +
      m27 + -(m31) + -(m33) + m40 + m43 := by
    rw [hcl31, ecl13, ecl29]; ring
  have ecl32 : cl32 = -(m3) + -(m8) + m11 + -(m13) + -(m16) + m19 + m23 + -(m25) + -(m27) + m31 +
      -(m40) + m46 := by
    rw [hcl32, ecl26]; ring
  have ecl33 : cl33 = -(m3) + -(m8) + m11 + -(m13) + -(m16) + m19 + m23 + -(m25) + m26 + -(m27) +
      m31 + -(m40) := by
    rw [hcl33, ecl26]; ring
  have ecl34 : cl34 = m3 + -(m8) + m13 + -(m16) + m17 + -(m18) + m21 + m23 + m25 + m27 + m35 +
      m46 := by
    rw [hcl34, ecl18, ecl32]; ring
  have ecl35 : cl35 = m3 + m12 + m13 + m43 := by
    rw [hcl35, ecl6, ecl1]; ring
  have ecl36 : cl36 = (2) * m3 + m8 + m9 + -(m11) + m12 + (2) * m13 + m17 + -(m18) + -(m19) +
      -(m20) + -(m23) + m25 + m27 + -(m31) + -(m33) + m40 + (2) * m43 := by
    rw [hcl36, ecl35, ecl31]; ring
  have ecl37 : cl37 = -(m9) + m11 + m12 + m37 + -(m40) := by
    rw [hcl37, ecl4]; ring
  have ecl38 : cl38 = m3 + m8 + m12 + m13 + m17 + -(m18) + -(m19) + -(m20) + -(m23) + m25 + m27 +
      -(m31) + -(m33) + m37 + m43 := by
    rw [hcl38, ecl37, ecl31]; ring
  have ecl39 : cl39 = (2) * m3 + m8 + m9 + -(m11) + m12 + (2) * m13 + m17 + -(m18) + -(m19) +
      -(m20) + -(m23) + m25 + m27 + -(m31) + -(m33) + m39 + m40 + (2) * m43 := by
    rw [hcl39, ecl36]; ring
  have ecl40 : cl40 = (2) * m3 + m8 + m9 + -(m11) + m12 + (2) * m13 + m17 + -(m18) + -(m19) +
      -(m20) + -(m23) + m24 + m25 + m27 + -(m31) + -(m33) + m40 + (2) * m43 := by
    rw [hcl40, ecl36]; ring
  have ecl41 : cl41 = -(m23) + m28 := by
    rw [hcl41]; ring
  have ecl42 : cl42 = m3 + -(m8) + m13 + -(m16) + m17 + -(m18) + m21 + m25 + m27 + m28 + m35 +
      m46 := by
    rw [hcl42, ecl41, ecl34]; ring
  have ecl43 : cl43 = -(m1) + m3 + -(m8) + m13 + -(m16) + m17 + -(m18) + m21 + m23 + m25 + m27 +
      m35 + m46 := by
    rw [hcl43, ecl34]; ring
  have ecl44 : cl44 = -(m1) + (3) * m3 + m9 + -(m11) + m12 + (3) * m13 + -(m16) + (2) * m17 +
      (-2) * m18 + -(m19) + -(m20) + m21 + (2) * m25 + (2) * m27 + -(m31) + -(m33) + m35 + m39 +
      m40 + (2) * m43 + m46 := by
    rw [hcl44, ecl43, ecl39]; ring
  have ecl45 : cl45 = (-2) * m3 + m11 + (-2) * m13 + -(m17) + m18 + m19 + m20 + -(m21) +
      (-2) * m25 + (-2) * m27 + m31 + m33 + m34 + -(m35) + -(m40) + -(m45) := by
    rw [hcl45, ecl27]; ring
  have ecl46 : cl46 = (2) * m3 + m4 + m8 + m9 + -(m11) + m12 + (2) * m13 + m17 + -(m18) + -(m19) +
      -(m20) + -(m23) + m24 + m25 + m27 + -(m31) + -(m33) + m40 + (2) * m43 := by
    rw [hcl46, ecl40]; ring
  have ecl47 : cl47 = -(m1) + m3 + m9 + m12 + m13 + -(m16) + m17 + (-2) * m18 + -(m20) + -(m33) +
      m39 + (2) * m43 + m46 := by
    rw [hcl47, ecl44, ecl17]; ring
  have ecl48 : cl48 = -(m1) + m3 + m5 + m9 + m12 + m13 + -(m16) + m17 + (-2) * m18 + -(m20) +
      -(m33) + m39 + (2) * m43 + m46 := by
    rw [hcl48, ecl47]; ring
  have ecl49 : cl49 = m9 + m10 + -(m11) + -(m12) + -(m31) + m40 := by
    rw [hcl49, ecl8]; ring
  have ecl50 : cl50 = (-2) * m3 + m9 + m10 + -(m12) + (-2) * m13 + -(m17) + m18 + m19 + m20 +
      -(m21) + (-2) * m25 + (-2) * m27 + m33 + m34 + -(m35) + -(m45) := by
    rw [hcl50, ecl49, ecl45]; ring
  have ecl51 : cl51 = -(m1) + m3 + (2) * m9 + m10 + -(m11) + m13 + -(m16) + m17 + -(m18) + -(m31) +
      m34 + m39 + m40 + (2) * m43 + -(m45) + m46 := by
    rw [hcl51, ecl50, ecl44]; ring
  have ecl52 : cl52 = -(m1) + -(m3) + -(m4) + -(m8) + m9 + m10 + -(m12) + -(m13) + -(m16) + m19 +
      m20 + m23 + -(m24) + -(m25) + -(m27) + m33 + m34 + m39 + -(m45) + m46 := by
    rw [hcl52, ecl51, ecl46]; ring
  have ecl53 : cl53 = m9 + -(m11) + -(m12) + m14 + m40 := by
    rw [hcl53, ecl4]; ring
  have ecl54 : cl54 = (2) * m3 + m8 + m9 + (-2) * m11 + (2) * m13 + m14 + m17 + -(m18) + -(m19) +
      -(m20) + -(m23) + (2) * m25 + (2) * m27 + -(m31) + -(m33) + (2) * m40 + m43 := by
    rw [hcl54, ecl53, ecl29]; ring
  have ecl55 : cl55 = m3 + m9 + -(m11) + m13 + m14 + -(m16) + m17 + -(m18) + -(m20) + m25 + m27 +
      -(m33) + m40 + m43 + m46 := by
    rw [hcl55, ecl54, ecl32]; ring
  have ecl56 : cl56 = m7 + m21 := by
    rw [hcl56]; ring
  have ecl57 : cl57 = (-2) * m3 + -(m4) + m7 + -(m8) + -(m9) + m11 + -(m12) + (-2) * m13 + -(m17) +
      m18 + m19 + m20 + m21 + m23 + -(m24) + -(m25) + -(m27) + m31 + m33 + -(m40) + (-2) * m43 := by
    rw [hcl57, ecl56, ecl46]; ring
  have ecl58 : cl58 = -(m4) + m7 + -(m8) + -(m9) + -(m12) + (2) * m21 + m23 + -(m24) + m25 + m27 +
      -(m34) + m35 + (-2) * m43 + m45 := by
    rw [hcl58, ecl57, ecl45]; ring
  have ecl59 : cl59 = m3 + m9 + -(m11) + m13 + m14 + -(m16) + m17 + -(m18) + -(m20) + m25 + m27 +
      -(m33) + m40 + -(m42) + m43 + m46 := by
    rw [hcl59, ecl55]; ring
  have ecl60 : cl60 = -(m2) + m21 + m35 := by
    rw [hcl60, ecl10]; ring
  have ecl61 : cl61 = -(m2) + m3 + m9 + -(m11) + m13 + m14 + -(m16) + m17 + -(m18) + -(m20) + m21 +
      m25 + m27 + -(m33) + m35 + m40 + m43 + m46 := by
    rw [hcl61, ecl60, ecl55]; ring
  have ecl62 : cl62 = -(m3) + m9 + -(m13) + m14 + -(m16) + m19 + -(m21) + -(m25) + -(m27) + m31 +
      m34 + -(m35) + -(m42) + m43 + -(m45) + m46 := by
    rw [hcl62, ecl59, ecl45]; ring
  have ecl63 : cl63 = (-2) * m3 + m11 + (-2) * m13 + m19 + -(m21) + (-2) * m25 + (-2) * m27 + m31 +
      -(m35) + m36 + -(m40) := by
    rw [hcl63, ecl16]; ring
  have ecl64 : cl64 = (-3) * m3 + -(m8) + m11 + -(m12) + (-3) * m13 + -(m17) + m18 + (2) * m19 +
      m20 + -(m21) + m23 + (-3) * m25 + (-3) * m27 + (2) * m31 + m33 + -(m35) + m36 + -(m37) +
      -(m40) + -(m43) := by
    rw [hcl64, ecl63, ecl38]; ring
  have ecl65 : cl65 = m3 + m8 + m12 + m13 + m17 + -(m18) + -(m19) + -(m20) + -(m22) + -(m23) +
      m25 + m27 + -(m31) + -(m33) + m37 + m43 := by
    rw [hcl65, ecl38]; ring
  have ecl66 : cl66 = -(m1) + -(m8) + m9 + -(m16) + m17 + -(m18) + m19 + m23 + -(m25) + -(m27) +
      m31 + m36 + -(m37) + m39 + m43 + m46 := by
    rw [hcl66, ecl44, ecl64]; ring
  have ecl67 : cl67 = (2) * m3 + m12 + (2) * m13 + -(m16) + m17 + -(m18) + -(m19) + -(m20) + m21 +
      (2) * m25 + m26 + (2) * m27 + -(m31) + -(m33) + m35 + -(m36) + m37 + m43 := by
    rw [hcl67, ecl33, ecl64]; ring
  have ecl68 : cl68 = (-2) * m8 + m11 + (-2) * m16 + m17 + -(m18) + m19 + m21 + m23 + m26 + m28 +
      m31 + m35 + -(m40) + m46 := by
    rw [hcl68, ecl42, ecl33]; ring
  have ecl69 : cl69 = m3 + m8 + m12 + (2) * m13 + m17 + -(m18) + -(m19) + -(m20) + -(m22) +
      -(m23) + m25 + m27 + m29 + -(m31) + -(m33) + m37 + m43 := by
    rw [hcl69, ecl65, ecl7]; ring
  have ecl70 : cl70 = m2 + -(m8) + -(m9) + m11 + -(m14) + m20 + m28 + m33 + -(m40) + -(m43) := by
    rw [hcl70, ecl42, ecl61]; ring
  have ecl71 : cl71 = -(m2) + -(m3) + -(m4) + -(m8) + -(m12) + -(m13) + m14 + -(m16) + m19 + m21 +
      m23 + -(m24) + m31 + m35 + -(m43) + m46 := by
    rw [hcl71, ecl61, ecl46]; ring
  have ecl72 : cl72 = -(m0) + (3) * m3 + m9 + (-2) * m11 + (3) * m13 + m14 + -(m16) + (2) * m17 +
      (-2) * m18 + -(m19) + -(m20) + m21 + (2) * m25 + (3) * m27 + -(m31) + -(m33) + m35 +
      (2) * m40 + -(m42) + m43 + m46 := by
    rw [hcl72, ecl59, ecl21]; ring
  have ecl73 : cl73 = -(m0) + (2) * m3 + -(m11) + m13 + m17 + -(m18) + -(m19) + m21 + m25 +
      (2) * m27 + -(m29) + -(m31) + m35 + m40 := by
    rw [hcl73, ecl21, ecl7]; ring
  have ecl74 : cl74 = (2) * m3 + m8 + m9 + -(m11) + m12 + (2) * m13 + m17 + -(m18) + -(m19) +
      -(m20) + -(m23) + m24 + m25 + m27 + -(m31) + m32 + -(m33) + m40 + (2) * m43 := by
    rw [hcl74, ecl40]; ring
  have ecl75 : cl75 = m3 + m9 + m12 + m13 + -(m16) + m17 + -(m18) + -(m20) + m24 + m32 + -(m33) +
      (2) * m43 + m46 := by
    rw [hcl75, ecl74, ecl32]; ring
  have ecl76 : cl76 = m2 + m3 + -(m8) + m11 + m12 + m13 + -(m14) + -(m16) + m17 + -(m18) + m24 +
      m28 + m32 + -(m40) + m43 + m46 := by
    rw [hcl76, ecl75, ecl70]; ring
  have ecl77 : cl77 = (-2) * m3 + -(m8) + -(m9) + m11 + -(m12) + (-2) * m13 + -(m17) + m18 + m19 +
      m20 + m23 + -(m25) + -(m27) + m30 + m31 + m33 + -(m39) + -(m40) + (-2) * m43 := by
    rw [hcl77, ecl39]; ring
  have ecl78 : cl78 = -(m8) + -(m9) + m11 + -(m16) + m21 + m23 + m25 + m26 + m27 + m30 + m35 +
      -(m36) + m37 + -(m39) + -(m40) + -(m43) := by
    rw [hcl78, ecl77, ecl67]; ring
  have ecl79 : cl79 = (-2) * m3 + m11 + (-2) * m13 + -(m17) + m18 + m19 + m20 + -(m21) +
      (-2) * m25 + (-2) * m27 + m31 + m33 + m34 + -(m35) + -(m40) + -(m44) := by
    rw [hcl79, ecl27]; ring
  have ecl80 : cl80 = -(m0) + m3 + m9 + -(m11) + m13 + m14 + -(m16) + m17 + -(m18) + m27 + m34 +
      m40 + -(m42) + m43 + -(m44) + m46 := by
    rw [hcl80, ecl79, ecl72]; ring
  have ecl81 : cl81 = (-2) * m3 + m11 + (-2) * m13 + -(m17) + m18 + m19 + m20 + -(m21) +
      (-2) * m25 + (-2) * m27 + m31 + -(m35) + -(m40) + -(m41) := by
    rw [hcl81, ecl19]; ring
  have ecl82 : cl82 = -(m3) + m8 + m11 + m12 + -(m21) + -(m22) + -(m23) + -(m25) + -(m27) + m29 +
      -(m33) + -(m35) + m37 + -(m40) + -(m41) + m43 := by
    rw [hcl82, ecl81, ecl69]; ring
  have ecl83 : cl83 = (-2) * m3 + -(m12) + (-2) * m13 + m16 + -(m17) + m18 + m19 + m20 + -(m21) +
      (-2) * m25 + -(m26) + (-2) * m27 + m31 + m33 + -(m35) + m36 + -(m37) + m38 + -(m43) := by
    rw [hcl83, ecl67]; ring
  have ecl84 : cl84 = -(m0) + m3 + m9 + (-2) * m11 + -(m12) + m13 + m14 + m17 + -(m18) + -(m26) +
      m27 + m36 + -(m37) + m38 + (2) * m40 + -(m42) + m46 := by
    rw [hcl84, ecl83, ecl72]; ring
  have ecl85 : cl85 = -(m0) + m9 + -(m11) + m14 + m17 + -(m18) + m19 + -(m21) + -(m25) + -(m26) +
      m31 + -(m35) + m36 + -(m37) + m38 + m40 + -(m42) + m43 + m46 + -(m47) := by
    rw [hcl85, ecl84, ecl30]; ring
  have ecl86 : cl86 = m6 + m9 + -(m11) + -(m12) + -(m19) + -(m31) + m40 := by
    rw [hcl86, ecl9]; ring
  have ecl87 : cl87 = m2 + m6 + -(m8) + -(m12) + -(m14) + -(m19) + m20 + m28 + -(m31) + m33 +
      -(m43) := by
    rw [hcl87, ecl86, ecl70]; ring
  have ecl88 : cl88 = m2 + m3 + m6 + (2) * m13 + -(m14) + m17 + -(m18) + (-2) * m19 + -(m22) +
      -(m23) + m25 + m27 + m28 + m29 + (-2) * m31 + m37 := by
    rw [hcl88, ecl87, ecl69]; ring
  have ecl89 : cl89 = m2 + m6 + m11 + m12 + m13 + -(m14) + m17 + -(m18) + -(m19) + -(m21) +
      -(m22) + -(m23) + m28 + m29 + -(m31) + -(m35) + m37 + -(m40) + m43 + -(m47) := by
    rw [hcl89, ecl88, ecl30]; ring
  have pm0 : m0 = (a21 + -(a22)) * (b10 + -(b12) + -(b13)) := by
    rw [hm0, eal1, ebl48]
  have pm1 : m1 = (a30 + -(a33)) * (-(b20) + b21 + -(b22) + b30 + -(b31) + b32) := by
    rw [hm1, eal2, ebl42]
  have pm2 : m2 = (-(a11) + a12 + a13) * (-(b31) + b32 + b33) := by
    rw [hm2, eal4, ebl15]
  have pm3 : m3 = (a00 + -(a01) + -(h * a03) + -(a10) + a11 + h * a13 + -(a20) + a21 +
      a23) * (h * b01 + h * b03 + b33) := by
    rw [hm3, eal51, ebl21]
  have pm4 : m4 = (-(a02) + -(a03) + -(a12) + -(a13) + a32 + a33) * (b01 + b11 + b21) := by
    rw [hm4, eal35, ebl2]
  have pm5 : m5 = (a00 + -(a03) + -(a20) + a23 + -(a30) + a33) * (b00 + b10) := by
    rw [hm5, eal52, ebl3]
  have pm6 : m6 = (a11 + -(a12) + -(a13) + a21 + -(a22) + -(a23) + -(a31) + a32 + a33) * (b00 +
      -(b01) + -(b03) + b30 + -(b31) + -(b33)) := by
    rw [hm6, eal36, ebl38]
  have pm7 : m7 = (a10) * (-(b01) + b02 + b03 + -(b11) + b12 + b13 + -(b21) + b22 + b23) := by
    rw [hm7, ebl56]
  have pm8 : m8 = (h * a21 + -(h * a31) + a32 + a33) * (b10 + -(b11) + b12 + h * b20 + -(b21) +
      h * b22) := by
    rw [hm8, eal15, ebl49]
  have pm9 : m9 = (a02) * (-(b22) + b32) := by
    rw [hm9, ebl4]
  have pm10 : m10 = (a10 + -(a13) + a20 + -(a23) + -(a30) + a33) * (b00 + -(b01) + -(b03) + b10 +
      -(b11) + -(b13) + b20 + -(b21) + -(b23)) := by
    rw [hm10, eal47, ebl50]
  have pm11 : m11 = (a00 + -(a01) + h * a21 + h * a31) * (h * b01 + -(h * b03) + b12) := by
    rw [hm11, eal27, ebl22]
  have pm12 : m12 = (a02 + a03) * (b32) := by
    rw [hm12, eal6]
  have pm13 : m13 = (-(a00) + a01 + a03 + a10 + -(a11) + -(a13) + a20 + -(a21) +
      -(a23)) * (b33) := by
    rw [hm13, eal53]
  have pm14 : m14 = (h * a03 + -(a11) + a12 + h * a13) * (-(h * b20) + b21 + -(h * b22) + -(b31) +
      b32 + b33) := by
    rw [hm14, eal28, ebl24]
  have pm15 : m15 = (a00) * (b02 + b12) := by
    rw [hm15, ebl5]
  have pm16 : m16 = (a00 + -(a01) + -(h * a03) + a10 + -(a11) + -(h * a13) + -(a30) + a31 +
      a33) * (-(h * b01) + -(h * b03) + b21 + -(b31)) := by
    rw [hm16, eal43, ebl25]
  have pm17 : m17 = (a00 + -(a01) + -(a03) + -(a20) + a21 + a23 + -(a30) + a31 + a33) * (b10) := by
    rw [hm17, eal54]
  have pm18 : m18 = (a00 + -(a01) + -(a03) + -(a20) + h * a21 + a23 + -(a30) + h * a31 +
      a33) * (h * b01 + h * b03 + b10) := by
    rw [hm18, eal48, ebl43]
  have pm19 : m19 = (-(a10) + a11 + a13 + -(a20) + a21 + a23 + a30 + -(a31) + -(a33)) * (b10 +
      -(b11) + -(b13) + b20 + -(b21) + -(b23)) := by
    rw [hm19, eal49, ebl51]
  have pm20 : m20 = (-(a20) + a23) * (-(b30) + b32 + b33) := by
    rw [hm20, eal8, ebl16]
  have pm21 : m21 = (-(a10) + a11 + h * a21 + -(h * a31)) * (-(h * b01) + h * b03 + -(b11) + b12 +
      b13 + -(b21) + b22 + b23) := by
    rw [hm21, eal16, ebl52]
  have pm22 : m22 = (a02 + a03 + -(a22) + -(a23) + -(a32) + -(a33)) * (b00 + b30) := by
    rw [hm22, eal37, ebl6]
  have pm23 : m23 = (a32 + a33) * (b10 + -(b11) + b12 + b20 + -(b21) + b22) := by
    rw [hm23, eal9, ebl53]
  have pm24 : m24 = (-(a02) + -(a03) + a11 + -(a12) + -(a13) + h * a21 + -(h * a31) + a32 +
      a33) * (-(b01) + -(b11) + h * b20 + -(b21) + h * b22) := by
    rw [hm24, eal29, ebl26]
  have pm25 : m25 = (a22) * (b10 + -(b12) + -(b13) + b20 + -(b22) + -(b23)) := by
    rw [hm25, ebl54]
  have pm26 : m26 = (a00 + -(a01) + a10 + -(a11) + -(a30) + a31) * (-(b01) + b21 + -(b31)) := by
    rw [hm26, eal44, ebl17]
  have pm27 : m27 = (h * a21 + -(a22) + -(h * a31)) * (b10 + -(b12) + -(b13) + h * b20 +
      -(h * b22) + -(b23)) := by
    rw [hm27, eal17, ebl45]
  have pm28 : m28 = (-(a31) + a32 + a33) * (b10 + -(b11) + b12) := by
    rw [hm28, eal10, ebl57]
  have pm29 : m29 = (a00 + -(a01) + -(a10) + a11 + -(a20) + a21) * (b03 + b33) := by
    rw [hm29, eal55, ebl7]
  have pm30 : m30 = (a30) * (b00 + -(b01) + b02 + -(b20) + b21 + -(b22) + b30 + -(b31) + b32) := by
    rw [hm30, ebl39]
  have pm31 : m31 = (a10 + -(a11) + -(a13) + a20 + -(h * a21) + -(a23) + -(a30) + h * a31 +
      a33) * (-(h * b01) + -(h * b03) + b10 + -(b11) + -(b13) + b20 + -(b21) + -(b23)) := by
    rw [hm31, eal45, ebl46]
  have pm32 : m32 = (a01 + -(a02) + -(a03) + a11 + -(a12) + -(a13) + -(a31) + a32 + a33) * (b01 +
      b11) := by
    rw [hm32, eal38, ebl1]
  have pm33 : m33 = (h * a03 + -(h * a13) + a20 + -(a23)) * (-(b00) + h * b01 + h * b03 + -(b30) +
      b32 + b33) := by
    rw [hm33, eal19, ebl33]
  have pm34 : m34 = (a02 + a11 + -(a12) + h * a21 + -(a22) + -(h * a31)) * (b03 + b13 +
      -(h * b20) + h * b22 + b23) := by
    rw [hm34, eal30, ebl27]
  have pm35 : m35 = (a10 + -(a11)) * (-(b11) + b12 + b13 + -(b21) + b22 + b23) := by
    rw [hm35, eal7, ebl55]
  have pm36 : m36 = (a02 + -(a22) + -(a32)) * (b00 + -(b20) + b30) := by
    rw [hm36, eal20, ebl9]
  have pm37 : m37 = (a02 + h * a03 + h * a13 + -(a22) + -(a32) + -(a33)) * (b00 + -(h * b20) +
      -(h * b22) + b30) := by
    rw [hm37, eal31, ebl28]
  have pm38 : m38 = (a11 + -(a12) + a21 + -(a22) + -(a31) + a32) * (b00 + -(b01) + -(b03) +
      -(b20) + b21 + b23 + b30 + -(b31) + -(b33)) := by
    rw [hm38, eal39, ebl41]
  have pm39 : m39 = (h * a03 + h * a13 + a30 + -(a33)) * (b00 + -(h * b01) + -(h * b03) + -(b20) +
      b21 + -(b22) + b30 + -(b31) + b32) := by
    rw [hm39, eal40, ebl34]
  have pm40 : m40 = (a00 + -(a01)) * (b12) := by
    rw [hm40, eal5]
  have pm41 : m41 = (a20) * (b00 + -(b02) + -(b03) + b30 + -(b32) + -(b33)) := by
    rw [hm41, ebl35]
  have pm42 : m42 = (-(a11) + a12) * (b21 + -(b22) + -(b23) + -(b31) + b32 + b33) := by
    rw [hm42, eal3, ebl36]
  have pm43 : m43 = (-(a02) + -(h * a03) + -(h * a13)) * (-(h * b20) + -(h * b22) + b32) := by
    rw [hm43, eal21, ebl29]
  have pm44 : m44 = (-(a01) + a02 + a11 + -(a12) + a21 + -(a22)) * (b03 + b13) := by
    rw [hm44, eal41, ebl8]
  have pm45 : m45 = (a02 + -(a12) + -(a22)) * (b03 + b13 + b23) := by
    rw [hm45, eal22, ebl10]
  have pm46 : m46 = (a00 + -(a01) + -(a03) + a10 + -(a11) + -(a13) + -(a30) + a31 + a33) * (b21 +
      -(b31)) := by
    rw [hm46, eal50, ebl11]
  have pm47 : m47 = (-(h * a03) + a11 + -(a12) + -(h * a13) + a21 + -(a22) + -(a31) + a32 +
      a33) * (b00 + -(b01) + -(b03) + -(h * b20) + b21 + -(h * b22) + b30 + -(b31) + -(b33)) := by
    rw [hm47, eal32, ebl37]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ecl48, pm1, pm3, pm5, pm9, pm12, pm13, pm16, pm17, pm18, pm20, pm33, pm39, pm43, pm46]
    linear_combination (a02 * b20 + a02 * b22 + a03 * b00 + (-2) * h * a03 * b01 +
        (-2) * h * a03 * b03 + h * a03 * b20 + a03 * b21 + h * a03 * b22 + a03 * b30 +
        -(a03 * b31) + -(a03 * b32) + -(a03 * b33) + h * a13 * b20 + a13 * b21 + h * a13 * b22 +
        -(a13 * b31) + a13 * b33 + -(h * a21 * b01) + -(h * a21 * b03) + -(a21 * b10) +
        -(h * a31 * b01) + -(h * a31 * b03) + -(a31 * b10)) * h2
  · rw [ecl76, pm2, pm3, pm8, pm11, pm12, pm13, pm14, pm16, pm17, pm18, pm24, pm28, pm32, pm40,
      pm43, pm46]
    linear_combination (a00 * b01 + -(a01 * b01) + -(h * a03 * b01) + -(h * a03 * b03) +
        h * a03 * b20 + h * a03 * b22 + -(a03 * b32) + -(a03 * b33) + h * a13 * b20 +
        h * a13 * b22 + -(a13 * b32) + -(h * a21 * b03) + -(a21 * b10) + a31 * b01 +
        -(h * a31 * b03) + a31 * b12) * h2
  · rw [ecl5, pm9, pm12, pm15, pm40]
    ring
  · rw [ecl80, pm0, pm3, pm9, pm11, pm13, pm14, pm16, pm17, pm18, pm27, pm34, pm40, pm42, pm43,
      pm44, pm46]
    linear_combination (a00 * b03 + -(a01 * b03) + a02 * b22 + -(h * a03 * b01) +
        -(h * a03 * b03) + a03 * b21 + -(a03 * b31) + a11 * b22 + -(a12 * b22) + a13 * b21 +
        -(a13 * b31) + a13 * b33 + -(h * a21 * b01) + a21 * b03 + -(a21 * b12) + -(h * a31 * b01) +
        -(a31 * b10)) * h2
  · rw [ecl52, pm1, pm3, pm4, pm8, pm9, pm10, pm12, pm13, pm16, pm19, pm20, pm23, pm24, pm25, pm27,
      pm33, pm34, pm39, pm45, pm46]
    linear_combination (a02 * b22 + a03 * b21 + -(a03 * b31) + a03 * b32 + a03 * b33 + a10 * b01 +
        a10 * b03 + -(a11 * b01) + -(a11 * b03) + -(a11 * b20) + a12 * b20 + a13 * b00 +
        -(a13 * b01) + (-2) * h * a13 * b01 + -(a13 * b03) + (-2) * h * a13 * b03 + a13 * b21 +
        a13 * b30 + -(a13 * b31) + -(a13 * b33) + a20 * b01 + a20 * b03 + -(a21 * b10) +
        a21 * b11 + a21 * b13 + -(a21 * b20) + (-2) * h * a21 * b20 + a21 * b21 + a21 * b23 +
        a22 * b20 + -(a22 * b22) + -(a23 * b01) + -(a23 * b03) + -(a30 * b01) + -(a30 * b03) +
        a31 * b10 + -(a31 * b11) + -(a31 * b13) + a31 * b20 + (2) * h * a31 * b20 + -(a31 * b21) +
        -(a31 * b23) + -(a32 * b20) + -(a32 * b22) + a33 * b01 + a33 * b03 + -(a33 * b20) +
        -(a33 * b22)) * h2
  · rw [ecl71, pm2, pm3, pm4, pm8, pm12, pm13, pm14, pm16, pm19, pm21, pm23, pm24, pm31, pm35,
      pm43, pm46]
    linear_combination (-(h * a03 * b20) + a03 * b21 + -(h * a03 * b22) + -(a03 * b31) +
        a03 * b32 + a03 * b33 + a10 * b01 + -(a11 * b01) + -(h * a13 * b01) + -(h * a13 * b03) +
        -(h * a13 * b20) + a13 * b21 + -(h * a13 * b22) + -(a13 * b31) + a13 * b32 +
        h * a21 * b03 + -(a21 * b10) + a21 * b11 + a21 * b13 + -(a21 * b20) + -(h * a21 * b20) +
        a21 * b21 + -(h * a21 * b22) + a21 * b23 + -(h * a31 * b03) + a31 * b10 + -(a31 * b11) +
        -(a31 * b13) + a31 * b20 + h * a31 * b20 + -(a31 * b21) + h * a31 * b22 + -(a31 * b23) +
        -(a32 * b20) + -(a32 * b22) + -(a33 * b20) + -(a33 * b22)) * h2
  · rw [ecl58, pm4, pm7, pm8, pm9, pm12, pm21, pm23, pm24, pm25, pm27, pm34, pm35, pm43, pm45]
    linear_combination (-(a02 * b22) + -(h * a03 * b20) + -(h * a03 * b22) + a03 * b32 +
        a10 * b01 + -(a10 * b03) + -(a11 * b01) + a11 * b03 + -(a11 * b22) + a12 * b22 +
        -(h * a13 * b20) + -(h * a13 * b22) + a13 * b32 + -(h * a21 * b01) + h * a21 * b03 +
        (-2) * h * a21 * b22 + -(a22 * b20) + a22 * b22 + h * a31 * b01 + -(h * a31 * b03) +
        (2) * h * a31 * b22 + -(a32 * b20) + -(a32 * b22) + -(a33 * b20) + -(a33 * b22)) * h2
  · rw [ecl62, pm3, pm9, pm13, pm14, pm16, pm19, pm21, pm25, pm27, pm31, pm34, pm35, pm42, pm43,
      pm45, pm46]
    linear_combination (a02 * b22 + a03 * b21 + -(a03 * b31) + a03 * b33 + a10 * b03 +
        -(a11 * b03) + a11 * b22 + -(a12 * b22) + -(h * a13 * b01) + -(h * a13 * b03) + a13 * b21 +
        -(a13 * b31) + h * a21 * b01 + -(a21 * b10) + a21 * b11 + a21 * b13 + -(a21 * b20) +
        -(h * a21 * b20) + a21 * b21 + h * a21 * b22 + a21 * b23 + a22 * b20 + -(a22 * b22) +
        -(h * a31 * b01) + a31 * b10 + -(a31 * b11) + -(a31 * b13) + a31 * b20 + h * a31 * b20 +
        -(a31 * b21) + -(h * a31 * b22) + -(a31 * b23)) * h2
  · rw [ecl65, pm3, pm8, pm12, pm13, pm17, pm18, pm19, pm20, pm22, pm23, pm25, pm27, pm31, pm33,
      pm37, pm43]
    linear_combination (a03 * b00 + -(h * a03 * b01) + -(h * a03 * b03) + a03 * b30 +
        -(a03 * b32) + -(a03 * b33) + h * a13 * b01 + h * a13 * b03 + a13 * b33 +
        -(h * a21 * b01) + -(h * a21 * b03) + a21 * b10 + -(a21 * b11) + -(a21 * b13) + a21 * b20 +
        h * a21 * b20 + -(a21 * b21) + -(a21 * b23) + a22 * b22 + (-2) * a31 * b10 + a31 * b11 +
        a31 * b13 + -(a31 * b20) + -(h * a31 * b20) + a31 * b21 + a31 * b23 + a32 * b20 +
        a32 * b22 + a33 * b20 + a33 * b22) * h2
  · rw [ecl89, pm2, pm6, pm11, pm12, pm13, pm14, pm17, pm18, pm19, pm21, pm22, pm23, pm28, pm29,
      pm31, pm35, pm37, pm40, pm43, pm47]
    linear_combination (-(a00 * b03) + a01 * b03 + a03 * b00 + a03 * b30 + -(a03 * b32) +
        -(a03 * b33) + a10 * b03 + -(a11 * b03) + a13 * b00 + -(a13 * b01) + -(a13 * b03) +
        a13 * b30 + -(a13 * b32) + -(a13 * b33) + a20 * b01 + a20 * b03 + -(a21 * b03) +
        (-2) * h * a21 * b03 + -(a21 * b13) + a21 * b20 + -(a21 * b23) + -(a23 * b01) +
        -(a23 * b03) + -(a31 * b10) + a31 * b12 + a31 * b13 + -(a31 * b20) + a31 * b23 +
        a32 * b20 + a32 * b22 + a33 * b20 + a33 * b22) * h2
  · rw [ecl82, pm3, pm8, pm11, pm12, pm21, pm22, pm23, pm25, pm27, pm29, pm33, pm35, pm37, pm40,
      pm41, pm43]
    linear_combination (-(a00 * b03) + a01 * b03 + a03 * b00 + a03 * b30 + -(a03 * b32) +
        a10 * b03 + -(a11 * b03) + h * a21 * b01 + -(a21 * b03) + -(h * a21 * b03) + a21 * b12 +
        h * a21 * b22 + a22 * b20 + -(h * a31 * b22) + a32 * b20 + a32 * b22 + a33 * b20 +
        a33 * b22) * h2
  · rw [ecl73, pm0, pm3, pm11, pm13, pm17, pm18, pm19, pm21, pm25, pm27, pm29, pm31, pm35, pm40]
    linear_combination (a00 * b03 + -(a01 * b03) + -(h * a03 * b01) + -(h * a03 * b03) +
        -(a03 * b33) + -(a10 * b03) + a11 * b03 + h * a13 * b01 + h * a13 * b03 + a13 * b33 +
        (-2) * h * a21 * b01 + a21 * b03 + a21 * b10 + -(a21 * b11) + -(a21 * b12) + -(a21 * b13) +
        a21 * b20 + h * a21 * b20 + -(a21 * b21) + -(h * a21 * b22) + -(a21 * b23) + -(a22 * b20) +
        a22 * b22 + (-2) * a31 * b10 + a31 * b11 + a31 * b13 + -(a31 * b20) + -(h * a31 * b20) +
        a31 * b21 + h * a31 * b22 + a31 * b23) * h2
  · rw [ecl66, pm1, pm8, pm9, pm16, pm17, pm18, pm19, pm23, pm25, pm27, pm31, pm36, pm37, pm39,
      pm43, pm46]
    linear_combination (a02 * b20 + a02 * b22 + -(h * a03 * b01) + -(h * a03 * b03) +
        h * a03 * b20 + a03 * b21 + h * a03 * b22 + -(a03 * b31) + -(h * a13 * b01) +
        -(h * a13 * b03) + h * a13 * b20 + a13 * b21 + h * a13 * b22 + -(a13 * b31) +
        (-2) * a21 * b10 + a21 * b11 + a21 * b13 + -(a21 * b20) + -(h * a21 * b20) + a21 * b21 +
        a21 * b23 + -(a22 * b22) + -(h * a31 * b01) + -(h * a31 * b03) + a31 * b10 + -(a31 * b11) +
        -(a31 * b13) + a31 * b20 + h * a31 * b20 + -(a31 * b21) + -(a31 * b23) + -(a32 * b20) +
        -(a32 * b22) + -(a33 * b20) + -(a33 * b22)) * h2
  · rw [ecl68, pm8, pm11, pm16, pm17, pm18, pm19, pm21, pm23, pm26, pm28, pm31, pm35, pm40, pm46]
    linear_combination (a00 * b01 + -(a01 * b01) + -(h * a03 * b01) + -(h * a03 * b03) +
        a03 * b21 + -(a03 * b31) + a10 * b01 + -(a11 * b01) + -(h * a13 * b01) + -(h * a13 * b03) +
        a13 * b21 + -(a13 * b31) + (-2) * a21 * b10 + a21 * b11 + a21 * b13 + -(a21 * b20) +
        -(h * a21 * b20) + a21 * b21 + -(h * a21 * b22) + a21 * b23 + a31 * b01 +
        (-2) * h * a31 * b03 + a31 * b10 + -(a31 * b11) + a31 * b12 + -(a31 * b13) + a31 * b20 +
        h * a31 * b20 + -(a31 * b21) + h * a31 * b22 + -(a31 * b23) + -(a32 * b20) + -(a32 * b22) +
        -(a33 * b20) + -(a33 * b22)) * h2
  · rw [ecl78, pm8, pm9, pm11, pm16, pm21, pm23, pm25, pm26, pm27, pm30, pm35, pm36, pm37, pm39,
      pm40, pm43]
    linear_combination (a00 * b01 + -(a01 * b01) + -(a02 * b20) + -(a02 * b22) + -(h * a03 * b20) +
        -(h * a03 * b22) + a10 * b01 + -(a11 * b01) + -(h * a13 * b20) + -(h * a13 * b22) +
        -(h * a21 * b22) + a22 * b22 + a31 * b01 + h * a31 * b01 + -(h * a31 * b03) + a31 * b12 +
        h * a31 * b22) * h2
  · rw [ecl85, pm0, pm9, pm11, pm14, pm17, pm18, pm19, pm21, pm25, pm26, pm31, pm35, pm36, pm37,
      pm38, pm40, pm42, pm43, pm46, pm47]
    linear_combination (-(a00 * b01) + a01 * b01 + a02 * b20 + a02 * b22 + a03 * b21 +
        -(a03 * b31) + -(a10 * b01) + a11 * b01 + a11 * b20 + a11 * b22 + -(a12 * b20) +
        -(a12 * b22) + a13 * b21 + -(a13 * b31) + -(a21 * b10) + a21 * b11 + -(a21 * b12) +
        a21 * b21 + -(a22 * b20) + -(a22 * b22) + a30 * b01 + a30 * b03 + -(a31 * b01) +
        (-2) * h * a31 * b01 + -(a31 * b11) + -(a31 * b21) + -(a33 * b01) + -(a33 * b03)) * h2

end Matmul48_201
