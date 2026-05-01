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
def bnc(n;w):
  prod(
    br(prod(v_eq("c1"; 0; 2))),
    (
      range(n) | 
      br(
        sum(
         br(imp((vi("a"; .)|c), vi("c\(.+2)";0))), 
         br(imp((vi("a"; .)), vi("c\(.+2)";0)))
        )
      )
    )
  )
;
# === tests ===
#bnc(3;4)