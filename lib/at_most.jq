# === deps ===
# expr.jq
# === end deps ===
# Negate a literal expressed as a string: "a" → "a'",  "a'" → "a".
# Use this instead of `c` from expr.jq when the input may already be primed.
def neg:
  if endswith("'") then .[:-1] else . + "'" end
;
# at_most_n($n; $xs; $prefix):
#   Encode "at most $n of the literals in $xs are true" using the sequential
#   counter (Sinz 2005).  Returns a CNF formula string in the app's
#   sum/product syntax.
#
#   $xs     — array of literal strings, e.g. ["x_1","x_2","y'"]
#   $prefix — name used for auxiliary counter variables (becomes "<prefix>_i,j")
#
# Sizes:
#   aux variables: ($m-1) * $n      (none when $n is 0 or ≥ $m)
#   clauses:       O($m * $n)
def at_most_n($n; $xs; $prefix):
  ($xs | length) as $m |
  def s($i; $j): "\($prefix)_\($i),\($j)";
  if $n < 0                  then "0"
  elif $m == 0 or $n >= $m   then "1"
  elif $n == 0               then prod($xs[] | neg)
  else
    prod(
      ( range(1; $m) as $i
      | (
          # C1:  (¬xᵢ ∨ s_{i,1})
          br(sum( ($xs[$i-1] | neg), s($i; 1) )),
          # C2:  (¬xᵢ ∨ ¬s_{i-1,j-1} ∨ s_{i,j})    for j=2..n, i≥2
          ( if $i >= 2 then
              range(2; $n + 1) as $j
              | br(sum(
                  ($xs[$i-1] | neg),
                  (s($i-1; $j-1) | neg),
                  s($i; $j)
                ))
            else empty end ),
          # C3:  (¬s_{i-1,j} ∨ s_{i,j})            for j=1..n, i≥2
          ( if $i >= 2 then
              range(1; $n + 1) as $j
              | br(sum( (s($i-1; $j) | neg), s($i; $j) ))
            else empty end ),
          # C4:  (¬xᵢ ∨ ¬s_{i-1,n})                for i=2..m-1
          ( if $i >= 2 then
              br(sum( ($xs[$i-1] | neg), (s($i-1; $n) | neg) ))
            else empty end )
        )
      ),
      # C4 final: (¬xₘ ∨ ¬s_{m-1,n})
      br(sum( ($xs[$m-1] | neg), (s($m-1; $n) | neg) ))
    )
  end
;
# Convenience wrapper: at_most(n; xs) uses prefix "s".
def at_most(n; xs): at_most_n(n; xs; "s");
# === tests ===
  (at_most(0; ["a","b","c"]) == "a' b' c'")
, (at_most(3; ["a","b","c"]) == "1")
, (at_most(2; ["a","b"])     == "1")
, (at_most(-1; ["a"])        == "0")
, (at_most(1; ["a","b"])     == "(a' + s_1,1) (b' + s_1,1')")
,
  ( at_most(2; ["a","b","c","d"])
    | [scan("s_[0-9]+,[0-9]+")] | unique | length
    == 6
  )
,
  ( at_most_n(1; ["x","y"]; "t")
    | test("t_1,1") and (test("s_") | not)
  )
