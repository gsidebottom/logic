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
test_x_eq_5