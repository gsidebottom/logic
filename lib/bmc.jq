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

# 4 as $w | 8 as $n | prod(bmc($n;$w), br(v_gt("c\($n)"; $n; $w))) 
# with boxes
def bmc_w4_n8:
  def c(i): "c\(i)";
  8 as $n |
  prod(
    # c starts at zero
    "v_eq_0_4(c0)",
    # c can't count more than 8, this is unsatisfiable
    v_gt(c($n); $n; 4),
    (
      range($n) | 
      . as $i |
      vi("a"; $i) as $a_i |
      # c increments if a[0] == 0
      "a_i_zero_w4(\($a_i);\(c($i));\(c($i+1)))",
      # c does not increment if a[0] != 0
      "a_i_not_zero_w4(\($a_i);\(c($i));\(c($i+1)))"
    )
  )
;

def bmc_w4_n8_test:
  bmc_w4_n8 == "v_eq_0_4(c0) c8_3 (c8_2 + c8_1 + c8_0) a_i_zero_w4(a_0;c0;c1) a_i_not_zero_w4(a_0;c0;c1) a_i_zero_w4(a_1;c1;c2) a_i_not_zero_w4(a_1;c1;c2) a_i_zero_w4(a_2;c2;c3) a_i_not_zero_w4(a_2;c2;c3) a_i_zero_w4(a_3;c3;c4) a_i_not_zero_w4(a_3;c3;c4) a_i_zero_w4(a_4;c4;c5) a_i_not_zero_w4(a_4;c4;c5) a_i_zero_w4(a_5;c5;c6) a_i_not_zero_w4(a_5;c5;c6) a_i_zero_w4(a_6;c6;c7) a_i_not_zero_w4(a_6;c6;c7) a_i_zero_w4(a_7;c7;c8) a_i_not_zero_w4(a_7;c7;c8)"
;

# === boxes ===
# a_i_zero_w4(a_i;c_i;c_ip1) := imp((a_i|c), plus1(c_i; c_ip1; 4))
# a_i_not_zero_w4(a_i;c_i;c_ip1) := imp(a_i, eq(c_i; c_ip1; 4))
# === end boxes ===
# === tests ===
bmc_test
, bmc_w4_n8_test