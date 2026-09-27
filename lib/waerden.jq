# === deps ===
# expr.jq
# === end deps ===
# examples
#  w4_ap(35) (USAT)
#  w4_ap(34) (SAT)
#  w5_ap(178) (UNSAT)
#  w5_ap(177) (SAT)

# waerden's example

def w(j; k; n):
  prod(
    interleave(
        (
          (range(n) + 1) as $d |
          (range(n - ((j-1) * $d)) + 1) as $i |
          br(sum(p("x";$i+(range(j)*$d))))
        )
    ;
        (
          (range(n) + 1) as $d |
          (range(n - ((k-1) * $d)) + 1) as $i |
          br(sum(n("x";$i+(range(k)*$d))))
        )
    )
  )
;

# ── boxes ────────────────────────────────────────────────────────────────────
# Box benchmarks against CaDiCaL (doc/box_backend_design.md §10.1, 2026-09-13):
# w4_ap(35) is UNSAT and w4_ap(34) SAT — one ap4 box per progression, which
# the engine propagates as its two clauses — at CaDiCaL's speed (1.5 / 0.7 ms
# vs 1.3 / 0.45 ms in the UI).  The window formulation w4_win(n; W) is the
# experiment that showed wider boxes do not help this problem.
# the arithmetic progressions of length j inside 1..n, as [start, difference]
def aps(j; n): (range(n) + 1) as $d | (range(n - ((j-1) * $d)) + 1) as $i | [$i, $d];

# the members of the progression [i, d] (length j) as variables x_i, x_{i+d}, …
def ap_vars(j; i; d): i as $i | d as $d | range(j) | "x_\($i + . * $d)";

# w(4;4;n) with every progression a box: ap4(x_i; x_{i+d}; x_{i+2d}; x_{i+3d})
def w4_ap(n): prod(aps(4; n) | "ap4(\([ap_vars(4; .[0]; .[1])] | join(";")))");

# w(5;5;n) with every progression a box: ap5(x_i; x_{i+d}; x_{i+2d}; x_{i+3d}; x_{i+4d})
def w5_ap(n): prod(aps(5; n) | "ap5(\([ap_vars(5; .[0]; .[1])] | join(";")))");

# no monochromatic 4-progression inside a window of W positions x_0 … x_{W-1}
# (the definition of the window boxes: parameters x_0 … x_{W-1})
def win4(W):
  prod(aps(4; W) | . as [$i, $d] |
    br(sum(range(4) | "x_\($i - 1 + . * $d)")),
    br(sum(range(4) | "x_\($i - 1 + . * $d)'")));

# no 4 consecutive equal values in v_0 … v_{L-1} (the definition of the chain
# boxes: a progression's residue class r, r+d, r+2d, … has this shape)
def norun4(L):
  prod(range(L - 3) as $s |
    br(sum(range(4) | "v_\($s + .)")),
    br(sum(range(4) | "v_\($s + .)'")));

# w(4;4;n) as windows of width W (every progression with 3d+1 ≤ W lies in some
# window) plus, for the larger differences, one chain box per residue class
def w4_win(n; W):
  prod(
    (range(n - W + 1) + 1 | "win\(W)(\([range(W) as $k | "x_\(. + $k)"] | join(";")))"),
    (range(n) + 1 | select(3 * . + 1 > W) | . as $d |
      range($d) + 1 | [range(.; n + 1; $d)] | select(length >= 4) |
      "norun4_\(length)(\([.[] | "x_\(.)"] | join(";")))")
  );

# === boxes ===
# ap4(a;b;c;d) := "(a + b + c + d) (a' + b' + c' + d')"
# win7(x_0;x_1;x_2;x_3;x_4;x_5;x_6) := win4(7)
# norun4_4(v_0;v_1;v_2;v_3) := norun4(4)
# norun4_5(v_0;v_1;v_2;v_3;v_4) := norun4(5)
# norun4_6(v_0;v_1;v_2;v_3;v_4;v_5) := norun4(6)
# norun4_7(v_0;v_1;v_2;v_3;v_4;v_5;v_6) := norun4(7)
# norun4_8(v_0;v_1;v_2;v_3;v_4;v_5;v_6;v_7) := norun4(8)
# norun4_9(v_0;v_1;v_2;v_3;v_4;v_5;v_6;v_7;v_8) := norun4(9)
# norun4_10(v_0;v_1;v_2;v_3;v_4;v_5;v_6;v_7;v_8;v_9) := norun4(10)
# norun4_11(v_0;v_1;v_2;v_3;v_4;v_5;v_6;v_7;v_8;v_9;v_10) := norun4(11)
# norun4_12(v_0;v_1;v_2;v_3;v_4;v_5;v_6;v_7;v_8;v_9;v_10;v_11) := norun4(12)
# ap5(a;b;c;d;e) := "(a + b + c + d + e) (a' + b' + c' + d' + e')"
# === end boxes ===
# === tests ===
w4_ap(5) == "ap4(x_1;x_2;x_3;x_4) ap4(x_2;x_3;x_4;x_5)",
win4(5) == "(x_0 + x_1 + x_2 + x_3) (x_0' + x_1' + x_2' + x_3') (x_1 + x_2 + x_3 + x_4) (x_1' + x_2' + x_3' + x_4')",
norun4(5) == "(v_0 + v_1 + v_2 + v_3) (v_0' + v_1' + v_2' + v_3') (v_1 + v_2 + v_3 + v_4) (v_1' + v_2' + v_3' + v_4')",
w4_win(9; 7) == "win7(x_1;x_2;x_3;x_4;x_5;x_6;x_7) win7(x_2;x_3;x_4;x_5;x_6;x_7;x_8) win7(x_3;x_4;x_5;x_6;x_7;x_8;x_9)",
w4_win(9; 4) == "win4(x_1;x_2;x_3;x_4) win4(x_2;x_3;x_4;x_5) win4(x_3;x_4;x_5;x_6) win4(x_4;x_5;x_6;x_7) win4(x_5;x_6;x_7;x_8) win4(x_6;x_7;x_8;x_9) norun4_5(x_1;x_3;x_5;x_7;x_9) norun4_4(x_2;x_4;x_6;x_8)",
w(3;3;8) == "(x_1 + x_2 + x_3) (x_1' + x_2' + x_3') (x_2 + x_3 + x_4) (x_2' + x_3' + x_4') (x_3 + x_4 + x_5) (x_3' + x_4' + x_5') (x_4 + x_5 + x_6) (x_4' + x_5' + x_6') (x_5 + x_6 + x_7) (x_5' + x_6' + x_7') (x_6 + x_7 + x_8) (x_6' + x_7' + x_8') (x_1 + x_3 + x_5) (x_1' + x_3' + x_5') (x_2 + x_4 + x_6) (x_2' + x_4' + x_6') (x_3 + x_5 + x_7) (x_3' + x_5' + x_7') (x_4 + x_6 + x_8) (x_4' + x_6' + x_8') (x_1 + x_4 + x_7) (x_1' + x_4' + x_7') (x_2 + x_5 + x_8) (x_2' + x_5' + x_8')"