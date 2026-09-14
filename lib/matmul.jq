# === deps ===
# expr.jq
# math.jq
# === end deps ===
# examples (2×2 matrix multiplication over GF(2); Strassen: rank 7, and 7 is the rank)
#  mm_boxes(2; 8)                          (SAT)
#  mm_boxes(2; 7)                          (SAT)
#  mm_boxes_sym(2; 6)                      (UNSAT — hence rank ≤ 6 impossible)
#  mm_chain(2; 7)                          (SAT, one 5-column box per product)
#  mm_chain_sym(2; 6)                      (UNSAT, the chain form)
#  mm_cnf_sym(2; 6)                        (UNSAT, the CNF form for CaDiCaL)
#
# The Brent equations of ⟨n,n,n⟩ matrix multiplication with r products over
# GF(2) (doc/rank22_logical_form.tex, here for n = 2): for every index tuple
# (a,b,c,d,p,q) ∈ {1..n}^6,
#     ⊕_{m=1}^{r} α^m_{ab} ∧ β^m_{cd} ∧ γ^m_{pq}  =  [b=c] ∧ [a=p] ∧ [d=q]
# — n^6 equations, n^3 of them with right-hand side 1 (the naive terms
# A_{pk}B_{kq}, generated an odd number of times) and the rest 0 (every
# other cross term cancels).  Variables: a_m_k, b_m_k, c_m_k for product
# m = 1..r and entry k = 0..n²-1 (row-major); the k-th entry of α^m is a_m_k.

# row-major index of entry (i,j) of an n×n matrix
def mm_idx(n; i; j): (i - 1) * n + (j - 1);

# the equations as {e, ka, kb, kc, rhs}: the equation number and the entry
# indices of the three factors (the same for every product m)
def brent_eqs(n):
  [range(n) + 1] as $I |
  [ $I[] as $a | $I[] as $b | $I[] as $c | $I[] as $d | $I[] as $p | $I[] as $q |
    { ka: mm_idx(n; $a; $b), kb: mm_idx(n; $c; $d), kc: mm_idx(n; $p; $q),
      rhs: (if $b == $c and $a == $p and $d == $q then 1 else 0 end) } ]
  | to_entries | map({ e: .key } + .value);

# the three factor variables of product m in equation q, and its term variable
def mm_a(q; m): "a_\(m)_\(q.ka)";
def mm_b(q; m): "b_\(m)_\(q.kb)";
def mm_c(q; m): "c_\(m)_\(q.kc)";
def mm_t(q; m): "t_\(q.e)_\(m)";

# ── box formulations ─────────────────────────────────────────────────────────
# the parity t_1 ⊕ … ⊕ t_r = rhs of equation q as xor boxes of at most k
# inputs: one box when r ≤ k, else a chain of blocks — the first over the
# first k terms with its output q_e_1 a variable, each next one over the
# previous output and k-1 more terms, the last with the constant rhs.  The
# blocks propagate exactly as a single xor{r} table would (a parity forces
# its last unknown, and the block outputs are forced along the chain from
# both ends) at 2^(k-1) rows per box instead of 2^(r-1).
# the blocks from term index lo on (0-based), block number j: the carry in is
# q_e_{j-1} (none for the first block), the carry out q_e_j (the rhs for the last)
def mm_parity_blocks($q; $r; $k; $t; $lo; $j):
  (if $j == 1 then [] else ["q_\($q.e)_\($j - 1)"] end) as $in |
  ($k - ($in | length)) as $take |
  if $r - $lo <= $take
  then "xor\($r - $lo + ($in | length))(\(($in + $t[$lo:]) | join(";"));\($q.rhs))"
  else "xor\($k)(\(($in + $t[$lo:$lo + $take]) | join(";"));q_\($q.e)_\($j))",
       mm_parity_blocks($q; $r; $k; $t; $lo + $take; $j + 1)
  end;
def mm_parity(q; r; k):
  q as $q | r as $r | k as $k |
  [range($r) + 1 | mm_t($q; .)] as $t |
  if $r <= $k then "xor\($r)(\($t | join(";"));\($q.rhs))"
  else mm_parity_blocks($q; $r; $k; $t; 0; 1) end;
# each term as an and3 box and each equation as parity boxes (xor{r} for
# r ≤ 8, else blocks of 8): the engine propagates the parity tables to arc
# consistency — an XOR constraint, not a clause set
def mm_boxes(n; r; k):
  prod(brent_eqs(n)[] | . as $q |
    (range(r) + 1 | "and3(\(mm_a($q; .));\(mm_b($q; .));\(mm_c($q; .));\(mm_t($q; .)))"),
    mm_parity($q; r; k));
def mm_boxes(n; r): mm_boxes(n; r; 8);

# each equation as a chain of xstep boxes (q = p ⊕ a b c), the running parity
# p_e_m an ordinary variable, the first p a constant 0 and the last the
# right-hand side
def mm_chain(n; r):
  prod(brent_eqs(n)[] | . as $q |
    range(r) + 1 | . as $m |
    (if $m == 1 then "0" else "p_\($q.e)_\($m - 1)" end) as $pin |
    (if $m == r then "\($q.rhs)" else "p_\($q.e)_\($m)" end) as $pout |
    "xstep(\($pin);\(mm_a($q; $m));\(mm_b($q; $m));\(mm_c($q; $m));\($pout))");

# ── CNF formulations (for CaDiCaL: exact clauses, no Tseitin of a parity DNF) ─
def cl(lits): br(sum(lits));
# t = a b c as four clauses
def and3_cnf(q; m):
  mm_a(q; m) as $a | mm_b(q; m) as $b | mm_c(q; m) as $c | mm_t(q; m) as $t |
  cl(($t | c), $a), cl(($t | c), $b), cl(($t | c), $c), cl($t, ($a | c), ($b | c), ($c | c));
# q = p ⊕ t as four clauses; with q a constant, the two that survive
def xor2_cnf(p; t; q):
  if q == "1" then cl(p, t), cl((p | c), (t | c))
  elif q == "0" then cl((p | c), t), cl(p, (t | c))
  else cl((q | c), p, t), cl((q | c), (p | c), (t | c)), cl(q, (p | c), t), cl(q, p, (t | c)) end;
# the parity as a chain: p_2 = t_1 ⊕ t_2, p_m = p_{m-1} ⊕ t_m, p_r = rhs
def mm_cnf(n; r):
  prod(brent_eqs(n)[] | . as $q |
    (range(r) + 1 | and3_cnf($q; .)),
    (if r == 1 then cl(if $q.rhs == 1 then mm_t($q; 1) else (mm_t($q; 1) | c) end)
     else (range(2; r + 1) | . as $m |
       (if $m == 2 then mm_t($q; 1) else "p_\($q.e)_\($m - 1)" end) as $p |
       (if $m == r then "\($q.rhs)" else "p_\($q.e)_\($m)" end) as $pq |
       xor2_cnf($p; mm_t($q; $m); $pq))
     end));
# the parity directly: one clause per wrong assignment of the r term variables
def mm_cnf_direct(n; r):
  prod(brent_eqs(n)[] | . as $q |
    (range(r) + 1 | and3_cnf($q; .)),
    (range(pow(2; r)) | . as $v | [range(r) | ($v / pow(2; .) | floor) % 2] as $bits |
      select(($bits | add) % 2 != $q.rhs) |
      cl(range(r) | . as $m | mm_t($q; $m + 1) | if $bits[$m] == 1 then c else . end)));

# ── symmetry breaking ────────────────────────────────────────────────────────
# the products in non-decreasing order of their α vectors (as 4-bit numbers):
# the sum does not depend on the order of its terms, so this keeps
# satisfiability — every scheme has a reordering that obeys it
# (the α vector of an n×n scheme has n² bits: le_4 for 2×2, le_9 for 3×3)
def mm_sym_boxes(n; r): prod(range(1; r) | "le_\(n * n)(a_\(.);a_\(. + 1))");
def mm_sym_boxes(r):    mm_sym_boxes(2; r);
def mm_sym(n; r):       prod(range(1; r) | . as $m | br(le("a_\($m)"; "a_\($m + 1)"; n * n)));
def mm_sym(r):          mm_sym(2; r);
# the formulations with the symmetry breaking attached (what to type in the
# jq filter box for the UNSAT ranks: mm_boxes_sym(2; 6), mm_chain_sym(2; 6))
def mm_boxes_sym(n; r): prod(mm_boxes(n; r), mm_sym_boxes(n; r));
def mm_chain_sym(n; r): prod(mm_chain(n; r), mm_sym_boxes(n; r));
def mm_cnf_sym(n; r):   prod(mm_cnf(n; r), mm_sym(n; r));

# the parity boxes: xor{r}(t_1;…;t_r;d) ≡ t_1 ⊕ … ⊕ t_r = d, defined as a
# chain of xor2 with the running parities hidden — compiled by composition
def xor_chain(r):
  prod(range(2; r + 1) | . as $m |
    (if $m == 2 then "t_1" else "p_\($m - 1)" end) as $p |
    (if $m == r then "d" else "p_\($m)" end) as $q |
    "xor2(\($p);t_\($m);\($q))");

# === boxes ===
# and3(a;b;c;t) := "t = a b c"
# xstep(p;a;b;c;q) := "q = p ⊕ a b c"
# xor2(p;t;q) := "q = p ⊕ t"
# xor3(t_1;t_2;t_3;d) := xor_chain(3)
# xor4(t_1;t_2;t_3;t_4;d) := xor_chain(4)
# xor5(t_1;t_2;t_3;t_4;t_5;d) := xor_chain(5)
# xor6(t_1;t_2;t_3;t_4;t_5;t_6;d) := xor_chain(6)
# xor7(t_1;t_2;t_3;t_4;t_5;t_6;t_7;d) := xor_chain(7)
# xor8(t_1;t_2;t_3;t_4;t_5;t_6;t_7;t_8;d) := xor_chain(8)
# === end boxes ===
# === tests ===
(brent_eqs(2) | length) == 64,
([brent_eqs(2)[] | select(.rhs == 1)] | length) == 8,
(brent_eqs(1)) == [{e: 0, ka: 0, kb: 0, kc: 0, rhs: 1}],
mm_boxes(1; 2) == "and3(a_1_0;b_1_0;c_1_0;t_0_1) and3(a_2_0;b_2_0;c_2_0;t_0_2) xor2(t_0_1;t_0_2;1)",
([mm_parity({e: 5, rhs: 0}; 10; 4)] | join(" ")) == "xor4(t_5_1;t_5_2;t_5_3;t_5_4;q_5_1) xor4(q_5_1;t_5_5;t_5_6;t_5_7;q_5_2) xor4(q_5_2;t_5_8;t_5_9;t_5_10;0)",
([mm_parity({e: 0, rhs: 1}; 5; 4)] | join(" ")) == "xor4(t_0_1;t_0_2;t_0_3;t_0_4;q_0_1) xor2(q_0_1;t_0_5;1)",
(mm_boxes(3; 21) | [scan("xor[0-9]+")] | unique) == ["xor7", "xor8"],
(mm_boxes(3; 21) | [scan("q_[0-9]+_[0-9]+")] | unique | length) == 729 * 2,
mm_chain(1; 2) == "xstep(0;a_1_0;b_1_0;c_1_0;p_0_1) xstep(p_0_1;a_2_0;b_2_0;c_2_0;1)",
mm_cnf(1; 2) == "(t_0_1' + a_1_0) (t_0_1' + b_1_0) (t_0_1' + c_1_0) (t_0_1 + a_1_0' + b_1_0' + c_1_0') (t_0_2' + a_2_0) (t_0_2' + b_2_0) (t_0_2' + c_2_0) (t_0_2 + a_2_0' + b_2_0' + c_2_0') (t_0_1 + t_0_2) (t_0_1' + t_0_2')",
mm_cnf_direct(1; 2) == "(t_0_1' + a_1_0) (t_0_1' + b_1_0) (t_0_1' + c_1_0) (t_0_1 + a_1_0' + b_1_0' + c_1_0') (t_0_2' + a_2_0) (t_0_2' + b_2_0) (t_0_2' + c_2_0) (t_0_2 + a_2_0' + b_2_0' + c_2_0') (t_0_1 + t_0_2) (t_0_1' + t_0_2')",
xor_chain(3) == "xor2(t_1;t_2;p_2) xor2(p_2;t_3;d)",
mm_sym_boxes(3) == "le_4(a_1;a_2) le_4(a_2;a_3)",
mm_sym_boxes(3; 3) == "le_9(a_1;a_2) le_9(a_2;a_3)",
mm_boxes_sym(1; 2) == "and3(a_1_0;b_1_0;c_1_0;t_0_1) and3(a_2_0;b_2_0;c_2_0;t_0_2) xor2(t_0_1;t_0_2;1) le_1(a_1;a_2)",
mm_sym(2) == "(a_1_3' a_2_3 + (a_1_3 = a_2_3) a_1_2' a_2_2 + (a_1_2 = a_2_2) (a_1_3 = a_2_3) a_1_1' a_2_1 + (a_1_1 = a_2_1) (a_1_2 = a_2_2) (a_1_3 = a_2_3) a_1_0' a_2_0 + (a_1_0 = a_2_0) (a_1_1 = a_2_1) (a_1_2 = a_2_2) (a_1_3 = a_2_3))"
