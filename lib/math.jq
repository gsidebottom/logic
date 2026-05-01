# === deps ===
# expr.jq
# === end deps ===
# w-1, w-2, .. 0
def width(w): range(w-1;-1;-1);

# call [bit_position;bit_value] | f for each bit in . as a number w wide.  bit_value is true or false
def bits(w; f):
  . as $n |
  width(w) |
  [., (($n / pow(2; .)) | floor) % 2 == 1] | f
;

# name_(w-1)^(w-1)+...+name_0 = num
def v_eq(name;num;w):
    num |
    bits(w;lit(name;.[0];.[1]))
;
def test_x_eq_5: prod(v_eq("x"; 5; 3)) == "x_2 x_1' x_0";

# ─── Bit-vector comparisons ────────────────────────────────────────────────
#
# `v_le`, `v_lt`, `v_ge`, `v_gt` compare the unsigned integer
# represented by the bit-vector `name_(w-1) name_(w-2) ... name_0`
# against the constant `num`.  They produce a propositional formula
# (a string in the codebase's expression syntax) that is true exactly
# when the comparison holds.
#
# The recurrence is the standard MSB-first one, accumulated LSB-first
# via `reduce`.  Letting `n_i = bit i of num` and `b_i = name_i`:
#
#   v_le:  if n_i = 1: f := ¬b_i ∨ f      (equal here OR strictly less below)
#          if n_i = 0: f := ¬b_i ∧ f      (must be 0 here, recurse)
#   v_ge:  if n_i = 1: g := b_i ∧ g
#          if n_i = 0: g := b_i ∨ g
#   v_lt = v_le(num - 1)        (with the obvious edge cases)
#   v_gt = v_ge(num + 1)
#
# The reduction's seed is "1" (the empty comparison is trivially
# true), and `b_or` / `b_and` simplify away the `0` and `1` constants
# as the formula grows so the output stays compact.

# bit i (0-indexed from LSB) of num
def num_bit(num; i): (num / pow(2; i)) | floor | . % 2;

# Does the formula `.` have a top-level OR?  A top-level OR is a
# `" + "` substring at bracket depth zero — anything bracketed is
# at depth ≥ 1 and doesn't count.  Used by `b_and` below to decide
# whether to wrap an operand in parens before juxtaposing.
def has_top_or:
  . as $s |
  ($s | length) as $n |
  reduce range(0; $n) as $i (
    {d: 0, found: false};
    if .found then .
    elif $s[$i:$i+1] == "(" then .d += 1
    elif $s[$i:$i+1] == ")" then .d -= 1
    elif ($i + 3) <= $n and $s[$i:$i+3] == " + " and .d == 0 then .found = true
    else .
    end
  ) | .found
;

# OR with constant simplification: x∨1=1, x∨0=x, x∨y otherwise.
def b_or(x; y):
  if x == "1" or y == "1" then "1"
  elif x == "0" then y
  elif y == "0" then x
  else sum(x, y)
  end
;

# AND with constant simplification.  Brackets each operand only
# when it has a top-level OR — otherwise juxtaposition would
# misparse since `+` has lower precedence than juxtaposition.
def b_and(x; y):
  if x == "0" or y == "0" then "0"
  elif x == "1" then y
  elif y == "1" then x
  else
    (if (x | has_top_or) then br(x) else x end) as $xx |
    (if (y | has_top_or) then br(y) else y end) as $yy |
    prod($xx, $yy)
  end
;

# Boolean formula: name_(w-1)..name_0 ≤ num  (unsigned bit-vector).
# Returns "0" when num < 0 (no unsigned value can be ≤ a negative)
# and "1" when num ≥ 2^w (every w-bit value qualifies).
def v_le(name; num; w):
  if num < 0 then "0"
  elif num >= pow(2; w) then "1"
  else
    reduce range(0; w) as $i ("1";
      . as $f |
      lit(name; $i; false) as $nb |
      if num_bit(num; $i) == 1 then b_or($nb; $f)
      else b_and($nb; $f)
      end
    )
  end
;
def test_v_le_5_3: v_le("x"; 5; 3) == "x_2' + x_1'";

# Boolean formula: name_(w-1)..name_0 < num.
def v_lt(name; num; w):
  if num <= 0 then "0"
  else v_le(name; num - 1; w)
  end
;
def test_v_lt_5_3: v_lt("x"; 5; 3) == "x_2' + x_1' x_0'";

# Boolean formula: name_(w-1)..name_0 ≥ num.
# Returns "1" for num ≤ 0 and "0" for num > 2^w-1.
def v_ge(name; num; w):
  if num <= 0 then "1"
  elif num > (pow(2; w) - 1) then "0"
  else
    reduce range(0; w) as $i ("1";
      . as $g |
      lit(name; $i; true) as $b |
      if num_bit(num; $i) == 1 then b_and($b; $g)
      else b_or($b; $g)
      end
    )
  end
;
def test_v_ge_5_3: v_ge("x"; 5; 3) == "x_2 (x_1 + x_0)";

# Boolean formula: name_(w-1)..name_0 > num.
def v_gt(name; num; w):
  if num < 0 then "1"
  elif num >= (pow(2; w) - 1) then "0"
  else v_ge(name; num + 1; w)
  end
;
def test_v_gt_5_3: v_gt("x"; 5; 3) == "x_2 x_1";

# Edge cases: extremes degrade to the constants "0" / "1".
def test_v_le_neg:        v_le("x"; -1; 3) == "0";
def test_v_le_max:        v_le("x"; 8;  3) == "1";
def test_v_lt_zero:       v_lt("x"; 0;  3) == "0";
def test_v_ge_zero:       v_ge("x"; 0;  3) == "1";
def test_v_ge_overshoot:  v_ge("x"; 8;  3) == "0";
def test_v_gt_max:        v_gt("x"; 7;  3) == "0";
def test_v_gt_neg:        v_gt("x"; -1; 3) == "1";

# ─── Bit-vector addition ───────────────────────────────────────────────────
#
# `plus(a; b; c; w)` produces a propositional formula that holds iff
# the unsigned w-bit integers represented by a, b, c satisfy
#   a + b = c
# *as integers* (i.e. the sum doesn't overflow w bits).
#
# No auxiliary carry variables are introduced.  Each carry bit is
# expressed inline via the closed form
#   carry_i = ⋁_{j=0..i-1} (a_j ∧ b_j ∧ ⋀_{k=j+1..i-1} (a_k ∨ b_k))
# which gives O(w^3) formula size — much better than the
# exponential blowup of recursively expanding the standard
# `carry_{i+1} = a_i b_i + carry_i (a_i + b_i)` recurrence.
#
# The formula is the conjunction of:
#   * for each bit i in [0, w-1]:  c_i ⇔ a_i ⊕ b_i ⊕ carry_i
#   * a "no overflow" constraint:  ¬carry_w
#
# Each per-bit equality is bracketed because `=` (the formula
# language's `iff`) and `⊕` both have lower precedence than
# juxtaposition (AND).  The carry sub-expression is also bracketed
# inside its `⊕` neighbour for the same reason — XOR binds tighter
# than the OR (`+`) at the top of the carry expression.

# Carry into bit `i` of a + b, expressed in terms of a_0..a_{i-1}
# and b_0..b_{i-1} only.  Returns the constant "0" for i ≤ 0.
def carry_at(a; b; i):
  if i <= 0 then "0"
  else
    [
      range(0; i) as $j |
      lit(a; $j; true) as $aj |
      lit(b; $j; true) as $bj |
      # generate at j AND propagators for k in (j+1)..(i-1)
      reduce range($j + 1; i) as $k
        ( b_and($aj; $bj);
          b_and(.; b_or(lit(a; $k; true); lit(b; $k; true)))
        )
    ] |
    if   length == 0 then "0"
    elif length == 1 then .[0]
    else reduce .[1:][] as $t (.[0]; b_or(.; $t))
    end
  end
;

# c_i ⇔ a_i ⊕ b_i ⊕ carry_at(a, b, i), as a propositional formula.
# Brackets the carry sub-expression to keep the XOR / OR precedence
# right (XOR binds tighter than OR; without parens, OR-terms in the
# carry would escape the XOR chain).
def sum_bit_eq(a; b; c; i):
  carry_at(a; b; i) as $carry |
  lit(a; i; true) as $ai |
  lit(b; i; true) as $bi |
  lit(c; i; true) as $ci |
  if   $carry == "0" then "\($ci) = \($ai) ⊕ \($bi)"
  elif $carry == "1" then "\($ci) = \($ai) ⊕ \($bi) ⊕ 1"
  else                    "\($ci) = \($ai) ⊕ \($bi) ⊕ (\($carry))"
  end
;

# a_(w-1)..a_0  +  b_(w-1)..b_0  =  c_(w-1)..c_0   (unsigned, no overflow).
# No extra variables introduced — every carry is inlined via `carry_at`.
def plus(a; b; c; w):
  if w <= 0 then "1"
  else
    [ range(0; w) | sum_bit_eq(a; b; c; .) | "(\(.))" ] as $eqs |
    carry_at(a; b; w) as $carry_w |
    (
      if   $carry_w == "0" then $eqs
      elif $carry_w == "1" then $eqs + ["0"]
      else                      $eqs + ["(\($carry_w))'"]
      end
    ) |
    prod(.[])
  end
;

# a == b as w-bit unsigned bit-vectors.  Bitwise: ⋀_i (a_i ⇔ b_i).
# Returns "1" for w=0 (the empty equality is vacuously true).
def eq(a; b; w):
  if w <= 0 then "1"
  else
    [ range(0; w) | "(\(lit(a; .; true)) = \(lit(b; .; true)))" ] |
    prod(.[])
  end
;
def test_eq_w0: eq("a"; "b"; 0) == "1";
def test_eq_w1: eq("a"; "b"; 1) == "(a_0 = b_0)";
def test_eq_w2: eq("a"; "b"; 2) == "(a_0 = b_0) (a_1 = b_1)";
def test_eq_w3: eq("a"; "b"; 3) == "(a_0 = b_0) (a_1 = b_1) (a_2 = b_2)";

# a + 1 = b, where a and b are w-bit unsigned bit-vectors.  No
# extra variables; specializes `plus` to the constant 1 (b₀ = 1,
# bᵢ = 0 for i ≥ 1) so the carry into bit i collapses from the
# closed form
#   carry_i = ⋁_j (a_j ∧ b_j ∧ ⋀_k (a_k ∨ b_k))
# to just  a_0 ∧ a_1 ∧ … ∧ a_{i-1}  (only j=0 contributes; the
# propagator factors (a_k ∨ 0) collapse to a_k).
#
# Result:
#   * Bit 0:        b_0 ⇔ ¬a_0
#   * Bit i ≥ 1:    b_i ⇔ a_i ⊕ (a_0 ∧ … ∧ a_{i-1})
#   * No-overflow:  ¬(a_0 ∧ … ∧ a_{w-1})
#
# w = 0 is unsatisfiable (1 doesn't fit in zero bits) → "0".
def plus1(a; b; w):
  if w <= 0 then "0"
  else
    # AND of a_0..a_{i-1}; for i=1 it's just a_0.
    def and_a_bits($i):
      reduce range(1; $i) as $k
        ( lit(a; 0; true);
          b_and(.; lit(a; $k; true))
        )
    ;
    [
      # Bit 0: b_0 ⇔ ¬a_0
      "(\(lit(b; 0; true)) = \(lit(a; 0; false)))"
      ,
      # Bit i ≥ 1: b_i ⇔ a_i ⊕ (a_0 ∧ … ∧ a_{i-1})
      range(1; w) as $i |
      and_a_bits($i) as $carry |
      "(\(lit(b; $i; true)) = \(lit(a; $i; true)) ⊕ \($carry))"
    ] as $eqs |
    and_a_bits(w) as $carry_w |
    ($eqs + ["(\($carry_w))'"]) |
    prod(.[])
  end
;
def test_plus1_w0: plus1("a"; "b"; 0) == "0";
def test_plus1_w1: plus1("a"; "b"; 1) == "(b_0 = a_0') (a_0)'";
def test_plus1_w2: plus1("a"; "b"; 2) == "(b_0 = a_0') (b_1 = a_1 ⊕ a_0) (a_0 a_1)'";
def test_plus1_w3: plus1("a"; "b"; 3) ==
  "(b_0 = a_0') (b_1 = a_1 ⊕ a_0) (b_2 = a_2 ⊕ a_0 a_1) (a_0 a_1 a_2)'";

def test_plus_w0:
  plus("a"; "b"; "c"; 0) == "1"
;
def test_plus_w1:
  plus("a"; "b"; "c"; 1) ==
  "(c_0 = a_0 ⊕ b_0) (a_0 b_0)'"
;
def test_plus_w2:
  plus("a"; "b"; "c"; 2) ==
  "(c_0 = a_0 ⊕ b_0) (c_1 = a_1 ⊕ b_1 ⊕ (a_0 b_0)) (a_0 b_0 (a_1 + b_1) + a_1 b_1)'"
;
def test_plus_w3:
  plus("a"; "b"; "c"; 3) ==
  "(c_0 = a_0 ⊕ b_0)" +
  " (c_1 = a_1 ⊕ b_1 ⊕ (a_0 b_0))" +
  " (c_2 = a_2 ⊕ b_2 ⊕ (a_0 b_0 (a_1 + b_1) + a_1 b_1))" +
  " (a_0 b_0 (a_1 + b_1) (a_2 + b_2) + a_1 b_1 (a_2 + b_2) + a_2 b_2)'"
;


# Every subsequence of `.` whose length is in [0, $maxlen].
def sublists(minlen;maxlen):
  def go($i; $cur):
    $cur,
    if ($cur | length) >= maxlen then empty
    else range($i; length) as $j | go($j+1; $cur + [.[$j]])
    end;
  [
    go(0; []) |
    select(. | length >= minlen)
  ] |
  sort_by([length, .])
;
def test_sublist_one_to_three: 
  ([1,2,3,4] | sublists(1;3)) ==
  [[1],[2],[3],[4],[1,2],[1,3],[1,4],[2,3],[2,4],[3,4],[1,2,3],[1,2,4],[1,3,4],[2,3,4]]
;

# at most n variables in the input list are true
def at_most(n):
    length as $count |
    sublists(n+1;$count) |
    br(prod(map(br(prod(.[])) | c)[]))
;
def test_at_most: [range(4) | vi("x";.)] | at_most(2) ==
  "((x_0 x_1 x_2)' (x_0 x_1 x_3)' (x_0 x_2 x_3)' (x_1 x_2 x_3)' (x_0 x_1 x_2 x_3)')"
;

# tests

# === tests ===
test_x_eq_5,
test_v_le_5_3,
test_v_lt_5_3,
test_v_ge_5_3,
test_v_gt_5_3,
test_v_le_neg,
test_v_le_max,
test_v_lt_zero,
test_v_ge_zero,
test_v_ge_overshoot,
test_v_gt_max,
test_v_gt_neg,
test_plus_w0,
test_plus_w1,
test_plus_w2,
test_plus_w3,
test_eq_w0,
test_eq_w1,
test_eq_w2,
test_eq_w3,
test_plus1_w0,
test_plus1_w1,
test_plus1_w2,
test_plus1_w3