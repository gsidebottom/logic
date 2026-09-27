# === deps ===
# expr.jq
# === end deps ===
# examples
#  slp(strassen_out; 8)        (SAT: Strassen's output side in 8 XORs over GF(2))
#  slp(strassen_out; 7)        (UNSAT)
#  slp(slp_window(sun56_cell; [0, 3, 7]); 8)
#  slp(sun56_cell; 29)         (the record cell at its transposition minimum — the open boundary)
#
# Shortest XOR straight-line programs — the SAT-competition benchmark family of
# doc/matmul_cxlb_satcomp.md.  SLP(k): do k XOR additions compute the given
# forms (vectors in GF(2)^n) from the n unit-vector inputs?  UNSAT at k proves
# the integer output side of a matrix-multiplication scheme needs ≥ k+1
# additions.  The encoding is matmul/cxlb.py's (Fuhs–Schneider-Kamp with unit
# inputs), here as boxes:
#   steps t = 0..k-1; step t selects exactly two sources among the n inputs
#   (j = 0..n-1) and the earlier steps (j = n+u for step u): selectors s_t_j,
#   exactly two of them — a chain of cnt2 boxes (running "≥1" / "≥2" bits
#   c_t_j_1 / c_t_j_2, the count never reaching 3);
#   values x_t_i = s_t_i ⊕ ⊕_{u<t} (s_t_{n+u} ∧ x_u_i) — a chain of gx boxes
#   (q = p ⊕ s x) with running parities p_t_i_u; x_0_i is s_0_i itself;
#   outputs: form f equals the value of some step: o_f_t ⇒ (x_t_i = f_i) as
#   imp boxes, at least one o_f_t — an or chain (orb boxes, constant 1 at
#   the end).  Forms of weight 1 are an input already and are dropped.
#   Symmetry breaking (sb, on by default, as in the paper): every step value
#   is nonzero (an or chain), and adjacent independent steps (t+1 does not
#   use step t) have strictly lexicographically increasing values — a chain of
#   lexstep boxes over the bits, bit n-1 most significant, then
#   s_{t+1}_{n+t} ∨ g (the "greater" bit at the end of the chain).
#
# An instance is {n, forms: [[bit_0, …, bit_{n-1}], …]}.

def slp_x(t; i): if t == 0 then "s_0_\(i)" else "x_\(t)_\(i)" end;

# an or over the names (constant 0 allowed) as orb blocks — the running
# disjunction r_<tag>_j — ending in the constant 1: at least one is true
def slp_or_blocks($names; $tag; $j; $carry):
  ($names | length) as $m |
  if $m <= 7
  then "orb(\($carry);\(($names + [range(7 - $m) | "0"]) | join(";"));1)"
  else "orb(\($carry);\($names[0:7] | join(";"));r_\($tag)_\($j))",
       slp_or_blocks($names[7:]; $tag; $j + 1; "r_\($tag)_\($j)")
  end;
def slp_or($names; $tag): slp_or_blocks($names; $tag; 0; "0");

# exactly two of s_t_0 … s_t_{w-1}
def slp_exactly2($t; $w):
  range($w) | . as $j |
  (if $j == 0 then "0;0" else "c_\($t)_\($j - 1)_1;c_\($t)_\($j - 1)_2" end) as $in |
  (if $j == $w - 1 then "1;1" else "c_\($t)_\($j)_1;c_\($t)_\($j)_2" end) as $out |
  "cnt2(\($in);s_\($t)_\($j);\($out))";

# the value bits of step t ≥ 1
def slp_values($t; $n):
  range($n) | . as $i |
  range($t) | . as $u |
  (if $u == 0 then "s_\($t)_\($i)" else "p_\($t)_\($i)_\($u - 1)" end) as $in |
  (if $u == $t - 1 then slp_x($t; $i) else "p_\($t)_\($i)_\($u)" end) as $out |
  "gx(\($in);s_\($t)_\($n + $u);\(slp_x($u; $i));\($out))";

# form f (index) equals the value of some step
def slp_output($f; $form; $n; $k):
  (range($k) | . as $t | range($n) | . as $i |
    "imp(o_\($f)_\($t);\(slp_x($t; $i))\(if $form[$i] == 1 then "" else "'" end))"),
  slp_or([range($k) | "o_\($f)_\(.)"]; "o\($f)");

# symmetry breaking: nonzero step values; adjacent independent steps lex-increasing
def slp_sb($n; $k):
  (range($k) | . as $t | slp_or([range($n) | slp_x($t; .)]; "z\($t)")),
  (range($k - 1) | . as $t |
    (range($n) | ($n - 1 - .) as $i |
      (if $i == $n - 1 then "1;0" else "e_\($t)_\($i + 1);g_\($t)_\($i + 1)" end) as $in |
      "lexstep(\($in);\(slp_x($t; $i));\(slp_x($t + 1; $i));e_\($t)_\($i);g_\($t)_\($i))"),
    "imp(s_\($t + 1)_\($n + $t)';g_\($t)_0)");

# the instance's forms of weight ≥ 2 (an input computes a weight-1 form)
def slp_forms($inst): [$inst.forms[] | select((add) >= 2)];

def slp($inst; $k; $sb):
  $inst.n as $n | slp_forms($inst) as $forms |
  prod(
    (range($k) | . as $t | slp_exactly2($t; $n + $t)),
    (range(1; $k) | slp_values(.; $n)),
    ($forms | to_entries[] | slp_output(.key; .value; $n; $k)),
    (if $sb then slp_sb($n; $k) else empty end)
  );
def slp($inst; $k): slp($inst; $k; true);

# ── instances ────────────────────────────────────────────────────────────────
# Strassen's output side over GF(2): C11 = M1+M4+M5+M7, C12 = M3+M5,
# C21 = M2+M4, C22 = M1+M2+M3+M6 (products 0-based); 8 XORs suffice, 7 do not
def strassen_out: { n: 7, forms: [[1,0,0,1,1,0,1], [0,0,1,0,1,0,0], [0,1,0,1,0,0,0], [1,1,1,0,0,1,0]] };

# a sub-instance: the forms with the given indices, over the inputs they use
def slp_window($inst; $idxs):
  [$inst.forms[$idxs[]]] as $fs |
  [range($inst.n) | select(. as $i | any($fs[]; .[$i] == 1))] as $used |
  { n: ($used | length), forms: [$fs[] | . as $f | [$used[] | $f[.]]] };

# the seed cells of the benchmark (the C side of a 3×3 rank-23 scheme: 9 output
# forms over the 23 products; matmul/cxlb.py --bits … reads the same forms)
def sun56_cell: { n: 23, forms: [
      [0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,1,0,0,0,0,0],
      [0,1,0,0,0,0,0,1,0,1,0,0,1,0,0,0,0,1,0,0,1,0,1],
      [1,0,0,1,1,0,0,1,0,1,0,0,1,0,1,0,0,0,0,0,0,0,0],
      [0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,1,0,0,0],
      [0,1,0,0,0,0,0,1,0,0,0,0,1,0,0,0,1,0,0,1,0,1,1],
      [0,0,1,0,0,1,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,1],
      [0,0,0,0,1,0,0,0,1,1,1,1,0,0,1,1,0,0,0,0,0,0,0],
      [0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0],
      [1,0,0,0,1,1,0,1,0,1,1,0,0,0,1,0,0,0,0,0,0,0,0]
    ] };
def cn120_cell: { n: 23, forms: [
      [0,0,0,1,0,1,0,0,1,0,1,0,0,0,1,0,0,0,0,0,0,0,0],
      [1,0,0,1,0,0,0,0,1,1,0,0,0,0,1,0,1,0,0,0,0,1,0],
      [0,0,0,1,0,0,0,0,1,0,0,1,0,0,1,0,0,0,1,0,0,0,0],
      [1,0,1,1,0,0,0,0,1,0,1,0,0,0,1,1,0,1,0,1,0,0,0],
      [1,0,1,1,1,0,0,0,1,1,0,0,0,0,1,1,0,1,0,0,0,1,0],
      [1,1,1,1,1,0,0,1,1,0,0,0,0,0,1,1,0,1,0,0,0,1,0],
      [0,0,0,0,0,0,1,0,1,0,1,0,0,0,1,0,0,1,0,0,0,0,0],
      [0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,1,0,1,0,0,1,0,0],
      [0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,1]
    ] };
def i19_cell: { n: 23, forms: [
      [1,0,0,0,0,1,0,1,0,1,1,0,1,0,0,0,0,1,1,0,0,0,0],
      [1,0,0,0,1,0,0,0,0,1,0,0,1,0,0,0,0,1,0,0,1,0,0],
      [0,0,1,0,0,1,0,1,0,0,1,1,0,0,0,0,0,0,1,0,0,0,0],
      [1,1,0,0,0,1,0,1,0,1,1,0,1,1,0,0,1,0,1,1,0,0,0],
      [0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,1,0],
      [0,1,0,0,0,1,0,1,0,1,1,1,0,0,0,0,1,0,1,1,0,0,1],
      [0,1,0,0,0,0,0,1,1,0,0,0,0,1,0,0,1,0,0,0,0,0,0],
      [0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,1,0,0,0,0,0,0,0],
      [0,0,0,0,0,0,1,1,0,0,1,1,0,0,0,0,1,0,1,0,0,0,0]
    ] };
def i12_cell: { n: 23, forms: [
      [0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1],
      [0,0,0,1,0,0,0,0,1,1,0,0,0,1,0,1,0,0,0,0,0,0,0],
      [0,0,0,1,0,1,0,0,1,0,0,1,0,1,1,0,1,0,0,0,0,0,0],
      [0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1,0,0,0,1,0],
      [0,1,1,1,1,0,0,1,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0],
      [1,0,0,1,0,0,0,1,0,0,0,1,0,1,0,0,1,1,0,0,0,0,0],
      [0,1,0,0,0,1,1,1,0,0,1,0,0,0,0,0,0,1,0,1,1,0,0],
      [0,1,0,0,1,0,0,1,0,0,0,0,0,0,0,1,1,1,0,1,0,0,0],
      [0,1,0,0,0,1,0,1,0,0,1,0,0,0,1,0,0,1,0,1,0,0,0]
    ] };

# === boxes ===
# gx(p;s;x;q) := "q = p ⊕ s x"
# cnt2(u1;u2;s;v1;v2) := "(v1 = u1 + s) (v2 = u2 + u1 s) (u2 s)'"
# imp(a;b) := "a ⇒ b"
# orb(p;o_1;o_2;o_3;o_4;o_5;o_6;o_7;q) := "q = p + o_1 + o_2 + o_3 + o_4 + o_5 + o_6 + o_7"
# lexstep(e;g;a;b;e2;g2) := "(e2 = e (a = b)) (g2 = g + e a' b)"
# === end boxes ===
# === tests ===
(slp_forms(strassen_out) | length) == 4,
(slp_window(sun56_cell; [0]) | .n) == 3,
(slp_window(sun56_cell; [0, 3, 7]) | .n) == 9,
([slp_exactly2(0; 2)] | join(" ")) == "cnt2(0;0;s_0_0;c_0_0_1;c_0_0_2) cnt2(c_0_0_1;c_0_0_2;s_0_1;1;1)",
([slp_values(2; 1)] | join(" ")) == "gx(s_2_0;s_2_1;s_0_0;p_2_0_0) gx(p_2_0_0;s_2_2;x_1_0;x_2_0)",
([slp_output(0; [1, 0]; 2; 1)] | join(" ")) == "imp(o_0_0;s_0_0) imp(o_0_0;s_0_1') orb(0;o_0_0;0;0;0;0;0;0;1)",
([slp_or([range(9) | "o_\(.)"]; "t")] | join(" ")) == "orb(0;o_0;o_1;o_2;o_3;o_4;o_5;o_6;r_t_0) orb(r_t_0;o_7;o_8;0;0;0;0;0;1)",
([slp_sb(2; 2)] | join(" ")) == "orb(0;s_0_0;s_0_1;0;0;0;0;0;1) orb(0;x_1_0;x_1_1;0;0;0;0;0;1) lexstep(1;0;s_0_1;x_1_1;e_0_1;g_0_1) lexstep(e_0_1;g_0_1;s_0_0;x_1_0;e_0_0;g_0_0) imp(s_1_2';g_0_0)"
