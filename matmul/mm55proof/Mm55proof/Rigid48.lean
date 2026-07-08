/-
Copyright (c) 2026 Greg Sidebottom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Greg Sidebottom
-/
import Std.Data.HashSet

/-!
# Rigidity of the rational rank-48 4×4 scheme under solved flip moves

The Dumas–Pernet–Sedoglavic rational `⟨4×4×4:48⟩` decomposition (the
only known rank-48 class with real points) is **flip-isolated**: no two
of its 48 rank-one summands share a factor, up to scalar, in any slot.
Exploration therefore proceeds by *splits* (replace a summand by two
whose slot factors sum to it — over ℚ this manufactures a shared
factor against any chosen partner) followed by *solved flips*: flip
moves whose scalar λ is chosen so that a factor of one summand becomes
proportional to the corresponding factor of a third (a "coincidence").
Two summands proportional in two slots merge — a *reduction* — and a
reduction to 47 summands would be a world record in characteristic 0.

**Theorem (this file).** Starting from the seed, the graph generated
by one split (any ordered pair of summands, any slot; scalar μ = 1 —
see the scope note) followed by arbitrary sequences of solved flips
(dyadic λ) is finite, and no state in it admits a reduction sweep
ending below 49 summands except back to the seed itself.

The proof is by verified computation (`native_decide`): the component
is enumerated exhaustively — visited states are deduplicated on FULL
canonical forms, not hashes — with the decomposition property
(`checkDecomp`, all 4096 Brent equations over exact dyadic arithmetic)
re-verified at every visited state, and saturation (fuel not
exhausted) asserted as part of the decided proposition.

Scope notes: (1) split scalars: the coincidence spans do not involve
the split scalar (the split part inherits the other two factors of the
split summand unchanged), so μ = 1 loses no generality for the
*existence* of coincidences; the formal statement here is for μ = 1.
(2) shared factors in the `c` slot are detected by exact equality of
the gauge representation (the `a`/`b` slots are fully canonical, so
there equality captures proportionality). (3) arithmetic is exact and
unbounded — no magnitude caps appear anywhere in this file.
-/

set_option maxHeartbeats 1600000

namespace Rigid48

/-- a dyadic vector: `2^exp * nums`, sixteen integer entries. -/
structure V16 where
  nums : List Int
  exp : Int
deriving BEq, Repr, Inhabited

/-- a rank-one summand `a ⊗ b ⊗ c` (the scalar lives in `c`). -/
structure Summand where
  a : V16
  b : V16
  c : V16
deriving BEq, Repr, Inhabited

/-- trailing zero bits of a positive natural (fueled, total). -/
def tzero : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, n => if n == 0 || n % 2 == 1 then 0 else 1 + tzero f (n / 2)

/-- pull common factors of two out of the entries into the exponent. -/
def V16.normalize (v : V16) : V16 :=
  if v.nums.all (· == 0) then ⟨v.nums, 0⟩
  else
    let tz := v.nums.foldl
      (fun acc x => if x == 0 then acc
        else min acc (tzero 64 x.natAbs)) 1000
    ⟨v.nums.map (fun x => x / ((2 : Int) ^ tz)), v.exp + tz⟩

/-- full canonical form: `v = sign · 2^exp · g · prim` with `g` odd
positive, `prim` primitive (content 1) and leading entry positive.
Returns `(prim, sign, exp, g)`. -/
def V16.canon (v : V16) : V16 × Bool × Int × Int :=
  let v := v.normalize
  let neg := match v.nums.find? (· != 0) with
    | some x => x < 0
    | none => false
  let nums := if neg then v.nums.map (- ·) else v.nums
  let g : Int := nums.foldl (fun a x => Int.ofNat (Int.gcd a x)) 0
  let g := if g == 0 then 1 else g
  (⟨nums.map (· / g), 0⟩, neg, v.exp, g)

def V16.isZero (v : V16) : Bool := v.nums.all (· == 0)

/-- `self + (-1)^neg · 2^k · other`, exact (entries aligned at the
minimum exponent; `Int` is unbounded so this is total). -/
def V16.addScaled (v w : V16) (neg : Bool) (k : Int) : V16 :=
  let oe := w.exp + k
  let e := min v.exp oe
  let sa := (v.exp - e).toNat
  let sb := (oe - e).toNat
  let nums := v.nums.zipWith
    (fun x y =>
      let a := x * ((2 : Int) ^ sa)
      let b := y * ((2 : Int) ^ sb)
      if neg then a - b else a + b) w.nums
  V16.normalize ⟨nums, e⟩

/-- canonical gauge: `a`, `b` fully canonical; sign, exponent and odd
content folded into `c`.  `none` when a factor vanishes. -/
def gauge (a b c : V16) : Option Summand :=
  if a.isZero || b.isZero || c.isZero then none
  else
    let (ca, na, ea, ga) := a.canon
    let (cb, nb, eb, gb) := b.canon
    let c := c.normalize
    let c : V16 := ⟨c.nums.map (· * (ga * gb)), c.exp + ea + eb⟩
    let c := if na != nb then ⟨c.nums.map (- ·), c.exp⟩ else c
    some ⟨ca, cb, c.normalize⟩

/-- slot accessor. -/
def fac (t : Summand) : Nat → V16
  | 0 => t.a
  | 1 => t.b
  | _ => t.c

def withFac (t : Summand) (slot : Nat) (v : V16) : Summand :=
  match slot with
  | 0 => ⟨v, t.b, t.c⟩
  | 1 => ⟨t.a, v, t.c⟩
  | _ => ⟨t.a, t.b, v⟩

/-! ## The matmul tensor and decomposition checking -/

/-- dyadic scalar addition on `(num, exp)` pairs. -/
def dadd : Int × Int → Int × Int → Int × Int
  | (n1, e1), (n2, e2) =>
    let e := min e1 e2
    (n1 * ((2 : Int) ^ (e1 - e).toNat) + n2 * ((2 : Int) ^ (e2 - e).toNat), e)

/-- all 4096 Brent equations of `⟨4,4,4⟩`, exactly.  Convention: with
`x = 4·ar + ac`, `y = 4·br + bc`, `z = 4·cr + cc`, the tensor entry is
1 iff `ac = br ∧ ar = cr ∧ bc = cc`. -/
def checkDecomp (s : List Summand) : Bool := Id.run do
  for x in List.range 16 do
    for y in List.range 16 do
      for z in List.range 16 do
        let mut acc : Int × Int := (0, 0)
        for t in s do
          let v := (t.a.nums.getD x 0) * (t.b.nums.getD y 0)
            * (t.c.nums.getD z 0)
          if v != 0 then
            acc := dadd acc (v, t.a.exp + t.b.exp + t.c.exp)
        let want : Int := if x % 4 == y / 4 && x / 4 == z / 4
          && y % 4 == z % 4 then 1 else 0
        let (n, e) := acc
        -- n·2^e = want  ⟺  (want = 0 ∧ n = 0) ∨ (n = want·2^{-e}, e ≤ 0)
        let ok := if n == 0 then want == 0
          else if e > 0 then false
          else n == want * ((2 : Int) ^ (-e).toNat)
        if !ok then
          return false
  return true

/-! ## Moves -/

/-- `x / y` as `±2^k` when it is one. -/
def dyadicRatio (x y : Int) : Option (Bool × Int) :=
  if x == 0 || y == 0 then none
  else
    let neg := (x < 0) != (y < 0)
    let ax := x.natAbs
    let ay := y.natAbs
    let (big, small, sg) :=
      if ax >= ay then (ax, ay, (1 : Int)) else (ay, ax, -1)
    if big % small != 0 then none
    else
      let q := big / small
      if q &&& (q - 1) != 0 then none
      else some (neg, sg * (tzero 64 q : Int))

/-- solved-flip candidates for the ordered shared pair `(i, j)` in
slot `ss`: transfer slots `t` and λ (dyadic) with
`f_i^t + λ f_j^t ∝ f_m^t` for a third summand `m`.  Exact Cramer over
integers aligned at a common exponent, all sixteen coordinates
verified. -/
def coincidences (s : List Summand) (i j ss : Nat) :
    List (Nat × (Bool × Int) × Nat) := Id.run do
  let others := match ss with
    | 0 => [1, 2]
    | 1 => [0, 2]
    | _ => [0, 1]
  let some ti := s[i]? | return []
  let some tj := s[j]? | return []
  let mut out := []
  for t in others do
    let fi := fac ti t
    let fj := fac tj t
    for m in List.range s.length do
      if m == i || m == j then
        continue
      let some tm := s[m]? | continue
      let fm := fac tm t
      let e := min fi.exp (min fj.exp fm.exp)
      let gi := fi.nums.map (· * ((2 : Int) ^ (fi.exp - e).toNat))
      let gj := fj.nums.map (· * ((2 : Int) ^ (fj.exp - e).toNat))
      let gm := fm.nums.map (· * ((2 : Int) ^ (fm.exp - e).toNat))
      -- pivots p < q with det = gj[p]·(−gm[q]) − gj[q]·(−gm[p]) ≠ 0
      let mut piv : Option (Nat × Nat × Int) := none
      for p in List.range 16 do
        for q in List.range 16 do
          if p < q && piv.isNone then
            let det := gj.getD p 0 * (-(gm.getD q 0))
              - gj.getD q 0 * (-(gm.getD p 0))
            if det != 0 then
              piv := some (p, q, det)
      let some (p, q, det) := piv | continue
      let nl := (-(gi.getD p 0)) * (-(gm.getD q 0))
        - (-(gi.getD q 0)) * (-(gm.getD p 0))
      let nm := gj.getD p 0 * (-(gi.getD q 0))
        - gj.getD q 0 * (-(gi.getD p 0))
      if nl == 0 || nm == 0 then
        continue
      let some lam := dyadicRatio nl det | continue
      let all16 := (List.range 16).all fun x =>
        det * gi.getD x 0 + nl * gj.getD x 0 - nm * gm.getD x 0 == 0
      if all16 then
        out := (t, lam, m) :: out
  return out

/-- flip on the shared slot-`ss` pair `(i, j)` with transfer `t1` for
`i` (identity: `f_i^{t1} += λ f_j^{t1}`, `f_j^{t2} −= λ f_i^{t2}`). -/
def flip (s : List Summand) (i j ss : Nat) (lam : Bool × Int) :
    Option (List Summand) := do
  let ti ← s[i]?
  let tj ← s[j]?
  if i == j || fac ti ss != fac tj ss then none
  else
    let (t1, t2) := match ss with
      | 0 => (1, 2)
      | 1 => (0, 2)
      | _ => (0, 1)
    let (neg, k) := lam
    let bi := (fac ti t1).addScaled (fac tj t1) neg k
    let cj := (fac tj t2).addScaled (fac ti t2) (!neg) k
    if bi.isZero || cj.isZero then none
    else do
      let gi ← gauge (withFac ti t1 bi).a (withFac ti t1 bi).b
        (withFac ti t1 bi).c
      let gj ← gauge (withFac tj t2 cj).a (withFac tj t2 cj).b
        (withFac tj t2 cj).c
      some (s.set i gi |>.set j gj)

/-- split summand `i` against `k` in slot `ss` (scalar 1): the part
`(f_k^{ss}, other factors of i)` replaces `i`; the remainder is
appended.  `none` when the factors are already proportional. -/
def split (s : List Summand) (i k ss : Nat) : Option (List Summand) := do
  let ti ← s[i]?
  let tk ← s[k]?
  if i == k then none
  else
    let rest := (fac ti ss).addScaled (fac tk ss) true 0
    if rest.isZero then none
    else do
      let part := fac tk ss
      let s1 ← gauge (withFac ti ss part).a (withFac ti ss part).b
        (withFac ti ss part).c
      let s2 ← gauge (withFac ti ss rest).a (withFac ti ss rest).b
        (withFac ti ss rest).c
      some ((s.set i s1) ++ [s2])

/-- one reduction: any pair proportional in two slots merges on the
third.  `a`/`b` are canonical so equality is proportionality there;
`c` comparisons use the full canon. -/
def reduceOnce (s : List Summand) : Option (List Summand) := Id.run do
  let n := s.length
  for i in List.range n do
    for j in List.range n do
      if i < j then
        let some ti := s[i]? | continue
        let some tj := s[j]? | continue
        -- pattern ab: merge on c
        if ti.a == tj.a && ti.b == tj.b then
          let c := tj.c.addScaled ti.c false 0
          if c.isZero then
            return some ((s.eraseIdx j).eraseIdx i)
          match gauge tj.a tj.b c with
          | some m => return some (((s.eraseIdx j).eraseIdx i) ++ [m])
          | none => pure ()
        -- pattern ac: merge on b
        let (pci, nci, eci, gci) := ti.c.canon
        let (pcj, ncj, ecj, gcj) := tj.c.canon
        if ti.a == tj.a && pci == pcj then
          let bi : V16 := ⟨ti.b.nums.map (· * gci), ti.b.exp + eci⟩
          let bj : V16 := ⟨tj.b.nums.map (· * gcj), tj.b.exp + ecj⟩
          let b := bi.addScaled bj (nci != ncj) 0
          let b := if nci then ⟨b.nums.map (- ·), b.exp⟩ else b
          if b.isZero then
            return some ((s.eraseIdx j).eraseIdx i)
          match gauge tj.a b ⟨pci.nums, 0⟩ with
          | some m => return some (((s.eraseIdx j).eraseIdx i) ++ [m])
          | none => pure ()
        -- pattern bc: merge on a
        if ti.b == tj.b && pci == pcj then
          let ai : V16 := ⟨ti.a.nums.map (· * gci), ti.a.exp + eci⟩
          let aj : V16 := ⟨tj.a.nums.map (· * gcj), tj.a.exp + ecj⟩
          let a := ai.addScaled aj (nci != ncj) 0
          let a := if nci then ⟨a.nums.map (- ·), a.exp⟩ else a
          if a.isZero then
            return some ((s.eraseIdx j).eraseIdx i)
          match gauge a tj.b ⟨pci.nums, 0⟩ with
          | some m => return some (((s.eraseIdx j).eraseIdx i) ++ [m])
          | none => pure ()
  return none

/-- reduction sweep to fixpoint (with fuel; each step removes at least
one summand so `s.length` fuel suffices). -/
def reduceSweep (s : List Summand) : List Summand :=
  go s.length s
where
  go : Nat → List Summand → List Summand
  | 0, s => s
  | n + 1, s =>
    match reduceOnce s with
    | some r => go n r
    | none => s

/-! ## Canonical scheme keys (collision-free dedup) -/

def V16.key (v : V16) : List Int := v.exp :: v.nums

def sKey (t : Summand) : List Int :=
  t.a.key ++ t.b.key ++ t.c.key

def lexLe : List Int → List Int → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
    if x < y then true else if y < x then false else lexLe xs ys

def schemeKey (s : List Summand) : List (List Int) :=
  (s.map sKey).mergeSort lexLe

/-! ## The exhaustive exploration -/

/-- successors of a state: every solved flip on every shared pair. -/
def successors (st : List Summand) : List (List Summand) := Id.run do
  let n := st.length
  let mut out := []
  for ss in List.range 3 do
    let (t1, _t2) : Nat × Nat := match ss with
      | 0 => (1, 2)
      | 1 => (0, 2)
      | _ => (0, 1)
    for x in List.range n do
      for y in List.range n do
        if x < y then
          match st[x]?, st[y]? with
          | some tx, some ty =>
            if fac tx ss == fac ty ss then
              for (oi, oj) in [(x, y), (y, x)] do
                for (t, lam, _m) in coincidences st oi oj ss do
                  -- transfer slot t1 is `flip (oi, oj)`; slot t2 is the
                  -- role-swapped flip with λ negated
                  let fl := if t == t1 then flip st oi oj ss lam
                    else flip st oj oi ss (!lam.fst, lam.snd)
                  match fl with
                  | some st2 => out := st2 :: out
                  | none => pure ()
          | _, _ => pure ()
  return out

structure St where
  work : List (List Summand)
  seen : Std.HashSet (List (List Int))
  visited : Nat
  allValid : Bool
  noBad : Bool

/-- fuel-recursive exhaustive exploration (total, hence usable by
`native_decide`).  Returns `none` when the fuel ran out before the
component closed. -/
def exploreGo (seedKey : List (List Int)) : Nat → St → Option St
  | 0, st => if st.work.isEmpty then some st else none
  | fuel + 1, st =>
    match st.work with
    | [] => some st
    | cur :: rest =>
      let valid := checkDecomp cur
      let r := reduceSweep cur
      let bad := r.length < 49 &&
        !(r.length == 48 && schemeKey r == seedKey)
      let (work', seen') := (successors cur).foldl
        (fun (acc : List (List Summand) × Std.HashSet (List (List Int)))
             st2 =>
          let key := schemeKey st2
          if acc.2.contains key then acc
          else (st2 :: acc.1, acc.2.insert key))
        (rest, st.seen)
      exploreGo seedKey fuel
        ⟨work', seen', st.visited + 1,
         st.allValid && valid, st.noBad && !bad⟩

structure Outcome' where
  visited : Nat
  saturated : Bool
  allValid : Bool
  noBadReduction : Bool
deriving Repr, DecidableEq

def explore (seed : List Summand) (fuel : Nat) : Outcome' := Id.run do
  let seedKey := schemeKey seed
  let mut frontier : List (List Summand) := []
  let mut seen : Std.HashSet (List (List Int)) := {}
  for ss in List.range 3 do
    for i in List.range 48 do
      for k in List.range 48 do
        match split seed i k ss with
        | some st =>
          let key := schemeKey st
          if !seen.contains key then
            seen := seen.insert key
            frontier := st :: frontier
        | none => pure ()
  match exploreGo seedKey fuel ⟨frontier, seen, 0, true, true⟩ with
  | some st => return ⟨st.visited, true, st.allValid, st.noBad⟩
  | none => return ⟨0, false, false, false⟩

def seed : List Summand := [
  ⟨⟨[1, -1, -1, -1, 1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 1, -1, 1, 0, -1], -2⟩⟩,
  ⟨⟨[1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0], 0⟩, ⟨[0, 1, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0], 0⟩, ⟨[1, 0, 0, 1, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0], -1⟩⟩,
  ⟨⟨[0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, -1, 0], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], 0⟩, ⟨[0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, -1, 1, 0], -1⟩⟩,
  ⟨⟨[0, 0, 1, 1, 0, 0, 1, 1, 0, 0, -1, 1, 0, 0, -1, 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, -1, 0], 0⟩, ⟨[0, 2, -1, -1, 0, 2, -1, -1, 0, 0, -1, 1, 0, 0, -1, 1], -2⟩⟩,
  ⟨⟨[1, 1, 1, -1, -1, -1, -1, 1, 1, 1, 1, -1, 1, 1, 1, -1], 0⟩, ⟨[1, 0, -1, -1, 1, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1], -2⟩⟩,
  ⟨⟨[1, 1, -1, 1, -1, -1, 1, -1, -1, -1, 1, -1, 1, 1, -1, 1], 0⟩, ⟨[0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1], 0⟩, ⟨[0, 0, 0, 0, 1, -1, 1, 0, 0, 0, 0, 0, -1, 1, -1, 0], -2⟩⟩,
  ⟨⟨[0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, -1], 0⟩, ⟨[0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0], 0⟩, ⟨[0, -1, 0, 1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0], -1⟩⟩,
  ⟨⟨[1, 1, 1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1, 1], 0⟩, ⟨[1, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], -2⟩⟩,
  ⟨⟨[0, 0, 1, 1, 0, 0, -1, -1, 1, -1, 0, 0, 1, -1, 0, 0], 0⟩, ⟨[1, 1, -1, -1, -1, -1, 1, 1, -1, 1, 1, 1, -1, 1, 1, 1], 0⟩, ⟨[-1, 1, 1, -1, 1, -1, -1, 1, -1, 1, -1, -1, -1, 1, -1, -1], -3⟩⟩,
  ⟨⟨[1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0], 0⟩, ⟨[0, 1, 1, 1, 0, 0, 0, 0, 0, -1, -1, -1, 0, 0, 0, 0], 0⟩, ⟨[1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0], -1⟩⟩,
  ⟨⟨[1, 1, 1, -1, -1, -1, -1, 1, -1, -1, -1, 1, 1, 1, 1, -1], 0⟩, ⟨[0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1, 0, -1], 0⟩, ⟨[0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], -2⟩⟩,
  ⟨⟨[0, 1, 0, 1, -1, 0, 1, 0, 0, 1, 0, 1, -1, 0, 1, 0], 0⟩, ⟨[1, 1, 1, -1, -1, 1, 1, 1, -1, -1, -1, 1, -1, 1, 1, 1], 0⟩, ⟨[-2, 2, -1, -1, 0, 0, -1, 1, -2, 2, -1, -1, 0, 0, -1, 1], -3⟩⟩,
  ⟨⟨[0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 1, 0], 0⟩, ⟨[1, 0, -1, -1, 0, 0, 0, 0, -1, 0, 1, 1, 0, 0, 0, 0], 0⟩, ⟨[0, -1, 1, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], -1⟩⟩,
  ⟨⟨[0, 0, 1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, -1, 0, 1, 0], 0⟩, ⟨[0, 1, -1, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0], -1⟩⟩,
  ⟨⟨[1, 0, 1, 0, 1, 0, -1, 0, -1, 0, -1, 0, 1, 0, -1, 0], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0], 0⟩, ⟨[-1, 1, -1, -1, 1, 1, -1, 1, 1, -1, 1, 1, 1, 1, -1, 1], -2⟩⟩,
  ⟨⟨[1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1], 0⟩, ⟨[1, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0], 0⟩, ⟨[1, -1, 1, 0, 0, 0, 0, 0, 1, -1, 1, 0, 0, 0, 0, 0], -2⟩⟩,
  ⟨⟨[1, 1, 0, 0, 1, 1, 0, 0, -1, 1, 0, 0, -1, 1, 0, 0], 0⟩, ⟨[0, 1, 1, 0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], 0⟩, ⟨[0, 0, 1, -1, 0, 0, 1, -1, -2, 0, -1, -1, -2, 0, -1, -1], -2⟩⟩,
  ⟨⟨[1, -1, -1, -1, 1, -1, -1, -1, -1, 1, 1, 1, -1, 1, 1, 1], 0⟩, ⟨[0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0], 0⟩, ⟨[0, 0, 0, 0, -1, 1, 0, -1, 0, 0, 0, 0, 1, -1, 0, 1], -2⟩⟩,
  ⟨⟨[0, 1, 0, 1, -1, 0, 1, 0, 0, -1, 0, -1, 1, 0, -1, 0], 0⟩, ⟨[1, -1, -1, -1, 1, 1, -1, 1, -1, 1, 1, 1, 1, 1, -1, 1], 0⟩, ⟨[0, 0, -1, 1, -2, 2, -1, -1, 0, 0, 1, -1, 2, -2, 1, 1], -3⟩⟩,
  ⟨⟨[1, -1, 1, 1, 1, -1, 1, 1, -1, 1, -1, -1, -1, 1, -1, -1], 0⟩, ⟨[0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, -1, 0, 1, 0], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], -2⟩⟩,
  ⟨⟨[0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 1, 0], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 1, -1, 0], -1⟩⟩,
  ⟨⟨[1, 0, 1, 0, 0, -1, 0, 1, 1, 0, 1, 0, 0, -1, 0, 1], 0⟩, ⟨[1, 1, 1, -1, -1, 1, 1, 1, 1, 1, 1, -1, 1, -1, -1, -1], 0⟩, ⟨[0, 0, 1, -1, 0, 0, -1, -1, 0, 0, 1, -1, 0, 0, -1, -1], -3⟩⟩,
  ⟨⟨[0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 0, 0, 1, 0, -1, -1, 0, 0, 0, 0, 1, 0, -1, -1], 0⟩, ⟨[0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0, 1, 0, -1], -1⟩⟩,
  ⟨⟨[1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, 1, -1, 1, 1], 0⟩, ⟨[1, 0, -1, -1, -1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0], 0⟩, ⟨[0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], -2⟩⟩,
  ⟨⟨[1, 1, 0, 0, -1, -1, 0, 0, 0, 0, 1, -1, 0, 0, 1, -1], 0⟩, ⟨[1, 1, -1, -1, 1, 1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1], 0⟩, ⟨[-1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, 1, -1, 1, -1, 1], -3⟩⟩,
  ⟨⟨[1, -1, 1, 1, 1, -1, 1, 1, 1, -1, 1, 1, -1, 1, -1, -1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0], -2⟩⟩,
  ⟨⟨[0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0], 0⟩, ⟨[0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0], -1⟩⟩,
  ⟨⟨[0, 0, 1, 1, 0, 0, 1, 1, 1, -1, 0, 0, -1, 1, 0, 0], 0⟩, ⟨[1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], 0⟩, ⟨[1, -1, 1, 1, 1, -1, 1, 1, 1, -1, -1, 1, -1, 1, 1, -1], -3⟩⟩,
  ⟨⟨[1, -1, -1, -1, -1, 1, 1, 1, -1, 1, 1, 1, -1, 1, 1, 1], 0⟩, ⟨[0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 0⟩, ⟨[-1, 1, 0, -1, 1, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], -2⟩⟩,
  ⟨⟨[0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, -1, 0], 0⟩, ⟨[0, -1, 0, 1, 0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], -1⟩⟩,
  ⟨⟨[0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0], 0⟩, ⟨[1, 0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], 0⟩, ⟨[-1, 0, -1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], -1⟩⟩,
  ⟨⟨[1, 0, 1, 0, 0, -1, 0, 1, -1, 0, -1, 0, 0, 1, 0, -1], 0⟩, ⟨[1, -1, -1, -1, 1, 1, -1, 1, 1, -1, -1, -1, -1, -1, 1, -1], 0⟩, ⟨[0, 0, -1, -1, 0, 0, 1, -1, 0, 0, 1, 1, 0, 0, -1, 1], -3⟩⟩,
  ⟨⟨[1, 1, -1, 1, -1, -1, 1, -1, -1, -1, 1, -1, -1, -1, 1, -1], 0⟩, ⟨[0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, 0, 1, -1, 1, 0], -2⟩⟩,
  ⟨⟨[0, 0, 1, 1, 0, 0, -1, -1, 0, 0, -1, 1, 0, 0, 1, -1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, -1, 0, -1], 0⟩, ⟨[0, 0, 1, -1, 0, 0, -1, 1, 0, -2, 1, 1, 0, 2, -1, -1], -2⟩⟩,
  ⟨⟨[1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, -1, 0, 0, -1, 1], 0⟩, ⟨[1, -1, -1, -1, 1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1], 0⟩, ⟨[1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, 1, -1, 1, -1, -1], -3⟩⟩,
  ⟨⟨[1, -1, 1, 1, 1, -1, 1, 1, 1, -1, 1, 1, 1, -1, 1, 1], 0⟩, ⟨[0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0], -2⟩⟩,
  ⟨⟨[0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0], 0⟩, ⟨[0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1], 0⟩, ⟨[0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1, 0, -1, 0], -1⟩⟩,
  ⟨⟨[0, 1, 0, 1, 0, 1, 0, -1, 0, 1, 0, 1, 0, -1, 0, 1], 0⟩, ⟨[0, 0, 0, 0, 1, 0, -1, -1, 0, 0, 0, 0, 0, -1, -1, -1], 0⟩, ⟨[-1, 1, -1, -1, 1, 1, 1, -1, -1, 1, -1, -1, -1, -1, -1, 1], -2⟩⟩,
  ⟨⟨[0, 1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0], 0⟩, ⟨[0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0], 0⟩, ⟨[1, 0, 1, 0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0], -1⟩⟩,
  ⟨⟨[1, 1, 0, 0, -1, -1, 0, 0, -1, 1, 0, 0, 1, -1, 0, 0], 0⟩, ⟨[1, 0, 0, -1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], 0⟩, ⟨[2, 0, 1, 1, -2, 0, -1, -1, 0, 0, -1, 1, 0, 0, 1, -1], -2⟩⟩,
  ⟨⟨[1, -1, -1, -1, 1, -1, -1, -1, 1, -1, -1, -1, 1, -1, -1, -1], 0⟩, ⟨[0, 1, 1, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0], 0⟩, ⟨[-1, 1, 0, -1, 0, 0, 0, 0, -1, 1, 0, -1, 0, 0, 0, 0], -2⟩⟩,
  ⟨⟨[0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, -1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 1, 0, 0, -1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, -1, 0, 1], -1⟩⟩,
  ⟨⟨[1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], 0⟩, ⟨[0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1], -1⟩⟩,
  ⟨⟨[1, 0, 1, 0, 1, 0, -1, 0, 1, 0, 1, 0, -1, 0, 1, 0], 0⟩, ⟨[1, 0, -1, -1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], 0⟩, ⟨[1, 1, -1, 1, -1, 1, -1, -1, 1, 1, -1, 1, 1, -1, 1, 1], -2⟩⟩,
  ⟨⟨[1, 1, -1, 1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0], 0⟩, ⟨[-1, 1, -1, 0, -1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0], -2⟩⟩,
  ⟨⟨[1, 1, 1, -1, 1, 1, 1, -1, 1, 1, 1, -1, -1, -1, -1, 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, -1, -1, -1], 0⟩, ⟨[0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], -2⟩⟩,
  ⟨⟨[1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0], 0⟩, ⟨[1, 0, -1, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, -1, 0, 0, -1], -1⟩⟩,
  ⟨⟨[0, 1, 0, 1, 0, 1, 0, -1, 0, -1, 0, -1, 0, 1, 0, -1], 0⟩, ⟨[0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], 0⟩, ⟨[1, 1, 1, -1, -1, 1, -1, -1, -1, -1, -1, 1, -1, 1, -1, -1], -2⟩⟩
]

/-! ## The theorems -/

/-- the seed is a genuine decomposition of the 4×4 matmul tensor. -/
theorem seed_valid : checkDecomp seed = true := by native_decide

/-- **Rigidity of the DPS rank-48 scheme under solved moves.**
The exploration closes on a component of exactly 7,408 states
(`saturated`), every state re-verifies as an exact decomposition of
the 4×4 matmul tensor (`allValid`), and no reduction sweep anywhere
in the component lands below 49 summands except the trivial return to
the seed (`noBadReduction`).  In particular no rank-47 scheme — which
would be a characteristic-0 record — is reachable from the seed by
one split and any sequence of solved flips. -/
theorem rigid : explore seed 20000 = ⟨7408, true, true, true⟩ := by
  native_decide

-- Axiom audit: `native_decide` proofs rest on `Lean.ofReduceBool`
-- (trust in the Lean compiler) in addition to the standard axioms.
#print axioms rigid
#print axioms seed_valid

end Rigid48
