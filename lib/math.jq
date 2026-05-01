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

# OR with constant simplification: x∨1=1, x∨0=x, x∨y otherwise.
def b_or(x; y):
  if x == "1" or y == "1" then "1"
  elif x == "0" then y
  elif y == "0" then x
  else sum(x, y)
  end
;

# AND with constant simplification + defensive bracket on y:
# x∧1=x, x∧0=0, otherwise "x (y)" (y bracketed in case it's an OR).
def b_and(x; y):
  if x == "0" or y == "0" then "0"
  elif x == "1" then y
  elif y == "1" then x
  else prod(x, br(y))
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
def test_v_lt_5_3: v_lt("x"; 5; 3) == "x_2' + x_1' (x_0')";

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
def test_v_gt_5_3: v_gt("x"; 5; 3) == "x_2 (x_1)";

# Edge cases: extremes degrade to the constants "0" / "1".
def test_v_le_neg:        v_le("x"; -1; 3) == "0";
def test_v_le_max:        v_le("x"; 8;  3) == "1";
def test_v_lt_zero:       v_lt("x"; 0;  3) == "0";
def test_v_ge_zero:       v_ge("x"; 0;  3) == "1";
def test_v_ge_overshoot:  v_ge("x"; 8;  3) == "0";
def test_v_gt_max:        v_gt("x"; 7;  3) == "0";
def test_v_gt_neg:        v_gt("x"; -1; 3) == "1";


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
test_v_gt_neg