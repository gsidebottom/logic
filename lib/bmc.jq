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
# 4 as $w | 8 as $n | prod(bnc($n;$w), br(v_gt("c\($n)"; $n; $w)))
def bnc(n;w):
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
# === tests ===
bnc(2;2) == "(c0_1' c0_0') ((a_0' ⇒ (c1_0 = c0_0') (c1_1 = c0_1 ⊕ c0_0) (c0_0 c0_1)') (a_0 ⇒ (c0_0 = c1_0) (c0_1 = c1_1))) ((a_1' ⇒ (c2_0 = c1_0') (c2_1 = c1_1 ⊕ c1_0) (c1_0 c1_1)') (a_1 ⇒ (c1_0 = c2_0) (c1_1 = c2_1)))"