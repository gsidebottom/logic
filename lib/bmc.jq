# === deps ===
# math.jq
# === end deps ===
# bounded model check for
#
# int a[N]; unsigned c;
# c = 0;
# for(i = 0; i < N; i++)
#   if(a[i] == 0)
#     c++;
#
# c_1 = 0 ∧
# c_2 = (a[0] = 0) ? c_1 + 1 : c_1 ∧
# c_3 = (a[1] = 0) ? c_2 + 1 : c_2 ∧
# ...
# c_N+1 = (a[N−1] = 0) ? c_N + 1 : c_N
#
# 4 as $w | 8 as $n | prod(bmc($n;$w), br(v_gt("c\($n)"; $n; $w)))
def bmc(n;w):
  prod(
    br(prod(v_eq("c0"; 0; w))),
    (
      range(n) | 
      . as $i |
      br(
        prod(
         br(imp((vi("a"; $i)|c), plus1("c\($i)"; "c\($i+1)"; w))), 
         br(imp(vi("a"; $i), eq("c\($i)"; "c\($i+1)"; w)))
        )
      )
    )
  )
;
def bmc_test:
  [
    "(c0_1' c0_0')",
    "((a_0' ⇒ (c1_0 = c0_0') (c1_1 = c0_1 ⊕ c0_0) (c0_0 c0_1)') (a_0 ⇒ (c0_0 = c1_0) (c0_1 = c1_1)))",
    "((a_1' ⇒ (c2_0 = c1_0') (c2_1 = c1_1 ⊕ c1_0) (c1_0 c1_1)') (a_1 ⇒ (c1_0 = c2_0) (c1_1 = c2_1)))"
  ] | join(" ") as $result |
  bmc(2;2) == $result
;

# The n-step unrolling with boxes: c starts at zero, then one step per
# a[i] — the two step boxes are the two branches of the `if`.  Used both
# as a formula generator (bmc_w4_n8) and as the definition of the single
# box bmc8_w4 (see the boxes block): the callees' tables are joined and the
# hidden counters projected step by step (never the expanded matrix), so
# the compiled table itself holds the reachable (a, c_n) pairs and "c_n ≤ n"
# is available to propagation without any search.
def bmc_chain_w4(a; c; n):
  prod(
    # c starts at zero
    "v_eq_0_4(\(c)0)",
    (
      range(n) |
      . as $i |
      vi(a; $i) as $a_i |
      # c increments if a[i] == 0
      "a_i_zero_w4(\($a_i);\(c)\($i);\(c)\($i+1))",
      # c does not increment if a[i] != 0
      "a_i_not_zero_w4(\($a_i);\(c)\($i);\(c)\($i+1))"
    )
  )
;
def bmc_chain_w4_test: (bmc_chain_w4("a"; "c"; 1) == "v_eq_0_4(c0) a_i_zero_w4(a_0;c0;c1) a_i_not_zero_w4(a_0;c0;c1)");

# 4 as $w | 8 as $n | prod(bmc($n;$w), br(v_gt("c\($n)"; $n; $w)))
# with boxes: the unrolling, and "c can't count more than 8" — unsatisfiable
def bmc_w4_n8_gt8:
  8 as $n |
  prod(bmc_chain_w4("a"; "c"; $n), v_gt("c\($n)"; $n; 4))
;
def bmc_w4_n8_gt8_test:
  bmc_w4_n8_gt8 == "v_eq_0_4(c0) a_i_zero_w4(a_0;c0;c1) a_i_not_zero_w4(a_0;c0;c1) a_i_zero_w4(a_1;c1;c2) a_i_not_zero_w4(a_1;c1;c2) a_i_zero_w4(a_2;c2;c3) a_i_not_zero_w4(a_2;c2;c3) a_i_zero_w4(a_3;c3;c4) a_i_not_zero_w4(a_3;c3;c4) a_i_zero_w4(a_4;c4;c5) a_i_not_zero_w4(a_4;c4;c5) a_i_zero_w4(a_5;c5;c6) a_i_not_zero_w4(a_5;c5;c6) a_i_zero_w4(a_6;c6;c7) a_i_not_zero_w4(a_6;c6;c7) a_i_zero_w4(a_7;c7;c8) a_i_not_zero_w4(a_7;c7;c8) c8_3 (c8_2 + c8_1 + c8_0)"
;

# bmc_w4_n8 with the unrolling as a single box: bmc8_w4(a;c8) c8_3 (c8_2 + c8_1 + c8_0)
def bmc_w4_n8_gt8_single_box: prod("bmc_w4_n8_box(a;c8)", v_gt("c8"; 8; 4));
def bmc_w4_n8_gt8_single_box_test: bmc_w4_n8_gt8_single_box == "bmc_w4_n8_box(a;c8) c8_3 (c8_2 + c8_1 + c8_0)";

# === boxes ===
# a_i_zero_w4(a_i;c_i;c_ip1) := imp((a_i|c), plus1(c_i; c_ip1; 4))
# a_i_not_zero_w4(a_i;c_i;c_ip1) := imp(a_i, eq(c_i; c_ip1; 4))
# bmc_w4_n8_box(a;c8) := bmc_chain_w4(a; "c"; 8)
# === end boxes ===
# === tests ===
bmc_test
, bmc_w4_n8_gt8_test
, bmc_chain_w4_test
, bmc_w4_n8_gt8_single_box_test