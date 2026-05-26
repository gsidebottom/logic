#!/usr/bin/env python3
"""
Parametric Cook 1976 PHP proof generator.

For PHP-N-M (N pigeons, M holes, N > M), generates:
  - DIMACS CNF (php_N_M.cnf) with pigeon clauses + pairwise mutex.
  - VeriPB PB proof (php_N_M.pbp) using Cook's extension-variable
    construction with recursive reduction.

Recursion:
  PHP-N-M → introduce Q_{i,j}^{layer 1} for i ∈ [1, N-1], j ∈ [1, M-1]
         → derive Q-pigeon + Q-mutex clauses → S_{n-1} = PHP-(N-1)-(M-1)
  Recurse until M-k = 1 (base case PHP-K-1 closes via rup).

Polynomial size O(N^4) per Cook 1976.

Usage:
    cook_php_proof.py <N> <M> <out_dir>
"""
import os
import sys

# ─── CNF generation ─────────────────────────────────────────────────────────

def php_cnf(N, M):
    """PHP-N-M clauses in load order:
       1..N: pigeon clauses; then per hole h, C(N,2) mutex clauses lex pair."""
    def var(i, j): return (i - 1) * M + j
    clauses = []
    for i in range(1, N + 1):
        clauses.append([var(i, j) for j in range(1, M + 1)])
    for k in range(1, M + 1):
        for i in range(1, N + 1):
            for j in range(i + 1, N + 1):
                clauses.append([-var(i, k), -var(j, k)])
    return clauses

# ─── Layer abstraction ──────────────────────────────────────────────────────

class Layer:
    """One reduction layer.  Tracks variable names and ConstraintIDs for:
      - pigeon clauses (one per pigeon at this layer)
      - mutex clauses (C(n_pigeons, 2) per hole at this layer)
    """
    def __init__(self, n_pigeons, n_holes, name_fn, pigeon_ids, mutex_ids):
        self.n_pigeons = n_pigeons
        self.n_holes = n_holes
        self.name = name_fn  # name(i, j) -> str like "x5" or "Q1_2_3"
        self.pigeon = pigeon_ids  # pigeon[i] = ID of pigeon i's clause
        self.mutex = mutex_ids   # mutex[(i, j, k)] = ID with i < j

# ─── Cook reduction (one layer) ─────────────────────────────────────────────

def emit_layer_reduction(layer_in, layer_idx, lines, cur):
    """Reduce layer_in (PHP-n-(n-1)-like; n_pigeons > n_holes) one step.

    Introduces Q vars Q{layer_idx}_{i}_{j} for i ∈ [1, n-1], j ∈ [1, n-2]
    where n = layer_in.n_pigeons.  Requires layer_in.n_pigeons - 1 == new
    layer's n_pigeons and layer_in.n_holes - 1 == new n_holes.

    Returns (cur_after, new_layer).
    """
    n = layer_in.n_pigeons
    M = layer_in.n_holes
    assert n > M, f"need n > M for reduction; got n={n} M={M}"
    new_n = n - 1
    new_M = M - 1

    def P(i, j): return layer_in.name(i, j)
    def NP(i, j): return f"~{P(i, j)}"
    def Q(i, j): return f"Q{layer_idx}_{i}_{j}"
    def NQ(i, j): return f"~{Q(i, j)}"

    q_id = {}  # (i, j) -> first ID of Q's 4 clauses

    # Step 1: introduce Q vars (4 reds each)
    lines.append(f"% === Layer {layer_idx}: reduce PHP-{n}-{M} → PHP-{new_n}-{new_M} ===")
    for i in range(1, n):
        for j in range(1, M):
            q = Q(i, j); nq = NQ(i, j)
            lines.append(f"% Define {q} = P_{{{i},{j}}} ∨ (P_{{{i},{M}}} ∧ P_{{{n},{j}}})")
            lines.append(f"red 1 {q} 1 {NP(i,j)} >= 1 : {q} -> 1 ;")
            lines.append(f"red 1 {q} 1 {NP(i,M)} 1 {NP(n,j)} >= 1 : {q} -> 1 ;")
            lines.append(f"red 1 {nq} 1 {P(i,j)} 1 {P(i,M)} >= 1 : {q} -> 0 ;")
            lines.append(f"red 1 {nq} 1 {P(i,j)} 1 {P(n,j)} >= 1 : {q} -> 0 ;")
            q_id[(i, j)] = cur + 1
            cur += 4

    # Step 2: derive Q-pigeon clauses (Q_{i,1} + ... + Q_{i, M-1} >= 1)
    #
    # For PHP-n-(n-1) with M = n-1, the Q-pigeon clause has M-1 = n-2 lits.
    # We need the resolution chain that derives this from:
    #   - layer_in pigeon clause for i (has M = n-1 lits including P_{i,n-1})
    #   - mutex(i, n, hole n-1) (binary): ~P_{i,M} ∨ ~P_{n,M}
    #   - layer_in pigeon clause for n
    #   - Q-defn clauses for (i, k), k ∈ [1, M-1]: C1, C2 (and we use C1 twice).
    #
    # Generalizing the PHP-4-3 sequence (9 steps for M=3):
    #   E   = pol pigeon_i mutex(i,n,M) + s
    #   F   = pol E pigeon_n + s
    #   for k in 1..M-1:  G_k = pol prev C1_{i,k} + s  → eliminates P_{i,k}
    #   then for k in 1..M-1:  I_k = pol prev C2_{i,k} + s  → eliminates P_{n,k}
    #   K   = pol prev pigeon_i + s  → re-introduces P_{i,*}, eliminates P_{i,M}
    #   for k in 1..M-1:  L_k = pol prev C1_{i,k} + s  → final eliminations
    # Total: 2 + (M-1) + (M-1) + 1 + (M-1) = 3M - 2 steps per pigeon clause.
    # For M=3: 7. Hmm but we used 9 for PHP-4-3.  Let me recount...
    #
    # Actually the PHP-4-3 sequence was:
    #   E, F, G(C1_i1), H(C1_i2), I(C2_i1), J(C2_i2), K(pigeon_i),
    #   L(C1_i1), Mm(C1_i2)
    # That's 9 steps for M-1 = 2 Q-cols.  Matches my formula 3M-2 if we use M = 3? 3*3-2 = 7.  Hmm off.
    #
    # Let me recount more carefully:
    # Step 1: E (pol pigeon_i mutex)
    # Step 2: F (pol E pigeon_n)
    # Steps 3..M (M-1 steps): G, H, ... apply C1_{i,k} for k=1..M-1
    #   (For M=3: steps 3, 4 = G, H using C1_{i,1}, C1_{i,2})
    # Steps M+1..2M-1 (M-1 steps): apply C2_{i,k} for k=1..M-1
    #   (For M=3: steps 5, 6 = I, J using C2_{i,1}, C2_{i,2})
    # Step 2M: K = re-apply pigeon_i (pol J pigeon_i)
    # Steps 2M+1..3M-1 (M-1 steps): apply C1_{i,k} again
    #   (For M=3: steps 7, 8, 9? But we had 9 steps total = L, M = 2 steps.)
    # 2 + (M-1) + (M-1) + 1 + (M-1) = 2 + 3(M-1) + 1 = 3M for M=3: 9. ✓
    #
    # OK formula: total = 3M steps per Q-pigeon clause.
    # For M=3 (PHP-4-3): 9 ✓.
    # For M=4 (PHP-5-4): 12 per pigeon × 4 pigeons = 48.
    #
    # Hmm wait, the formula generalization is suspect. Let me re-derive for
    # PHP-5-4 (M=4) to confirm. The pigeon clause has 4 lits: P_{i,1} +
    # P_{i,2} + P_{i,3} + P_{i,4} >= 1. We want Q_{i,1} + Q_{i,2} + Q_{i,3} >= 1.
    #
    # Step E = pigeon_i + mutex(i, n, h=M): eliminate P_{i,M}
    #   Result: P_{i,1} + P_{i,2} + P_{i,3} + ~P_{n,M} >= 1
    # Step F = E + pigeon_n: eliminate P_{n,M}
    #   Result: P_{i,1} + P_{i,2} + P_{i,3} + P_{n,1} + P_{n,2} + P_{n,3} >= 1
    # Step G_1 = F + C1_{i,1}: eliminate P_{i,1}, introduce Q_{i,1}
    #   Result: Q_{i,1} + P_{i,2} + P_{i,3} + P_{n,1} + P_{n,2} + P_{n,3} >= 1
    # Step G_2 = G_1 + C1_{i,2}: eliminate P_{i,2}, introduce Q_{i,2}
    #   Result: Q_{i,1} + Q_{i,2} + P_{i,3} + P_{n,1} + P_{n,2} + P_{n,3} >= 1
    # Step G_3 = G_2 + C1_{i,3}: eliminate P_{i,3}, introduce Q_{i,3}
    #   Result: Q_{i,1} + Q_{i,2} + Q_{i,3} + P_{n,1} + P_{n,2} + P_{n,3} >= 1
    # Step I_1 = G_3 + C2_{i,1}: eliminate P_{n,1}, introduce Q_{i,1}+~P_{i,M}
    #   C2_{i,1} = Q_{i,1} + ~P_{i,M} + ~P_{n,1}
    #   Sum: Q_{i,1} + Q_{i,2} + Q_{i,3} + P_{n,1} + P_{n,2} + P_{n,3} + Q_{i,1} + ~P_{i,M} + ~P_{n,1} >= 2
    #   = 2 Q_{i,1} + Q_{i,2} + Q_{i,3} + 1 + P_{n,2} + P_{n,3} + ~P_{i,M} >= 2
    #   = 2 Q_{i,1} + Q_{i,2} + Q_{i,3} + ~P_{i,M} + P_{n,2} + P_{n,3} >= 1
    #   Sat: Q_{i,1} + Q_{i,2} + Q_{i,3} + ~P_{i,M} + P_{n,2} + P_{n,3} >= 1
    # Step I_2: + C2_{i,2}: eliminate P_{n,2}, introduce another ~P_{i,M}
    #   Result: Q_{i,1} + Q_{i,2} + Q_{i,3} + ~P_{i,M} + P_{n,3} >= 1 (sat to 1)
    # Step I_3: + C2_{i,3}: eliminate P_{n,3}
    #   Result: Q_{i,1} + Q_{i,2} + Q_{i,3} + ~P_{i,M} >= 1
    # Step K = + pigeon_i: eliminate ~P_{i,M}
    #   pigeon_i = P_{i,1} + P_{i,2} + P_{i,3} + P_{i,4} >= 1 (with P_{i,M}=P_{i,4})
    #   Sum: Q_{i,1} + Q_{i,2} + Q_{i,3} + (~P_{i,M} + P_{i,M}) + P_{i,1} + P_{i,2} + P_{i,3} >= 2
    #   = Q_{i,1} + Q_{i,2} + Q_{i,3} + 1 + P_{i,1} + P_{i,2} + P_{i,3} >= 2
    #   = Q_{i,1} + Q_{i,2} + Q_{i,3} + P_{i,1} + P_{i,2} + P_{i,3} >= 1
    # Steps L_1, L_2, L_3: apply C1_{i,k} again to eliminate P_{i,k}, get final.
    #   L_1: + C1_{i,1} → Q_{i,1} + Q_{i,2} + Q_{i,3} + P_{i,2} + P_{i,3} >= 1 (after sat 2 Q_{i,1})
    #   L_2: + C1_{i,2} → Q_{i,1} + Q_{i,2} + Q_{i,3} + P_{i,3} >= 1
    #   L_3: + C1_{i,3} → Q_{i,1} + Q_{i,2} + Q_{i,3} >= 1 ✓
    #
    # Total steps for M=4: 2 (E, F) + 3 (G_1..G_3 with C1) + 3 (I_1..I_3 with C2)
    #                    + 1 (K) + 3 (L_1..L_3 with C1) = 12 = 3M.
    # ✓ matches formula.
    pigeon_n = layer_in.pigeon[n]
    new_pigeon = {}
    for i in range(1, n):
        pig_i = layer_in.pigeon[i]
        mut_i_n_M = layer_in.mutex[(i, n, M)] if (i, n, M) in layer_in.mutex else layer_in.mutex[(n, i, M)]
        lines.append(f"% Q-pigeon clause for pigeon {i} (layer {layer_idx}, {3*M} pol steps).")
        # E = pigeon_i + mutex(i, n, M)
        lines.append(f"pol {pig_i} {mut_i_n_M} + s ;");  cur += 1; prev = cur
        # F = E + pigeon_n
        lines.append(f"pol {prev} {pigeon_n} + s ;");  cur += 1; prev = cur
        # G_k = prev + C1_{i,k} for k = 1..M-1
        for k in range(1, M):
            c1_ik = q_id[(i, k)]
            lines.append(f"pol {prev} {c1_ik} + s ;");  cur += 1; prev = cur
        # I_k = prev + C2_{i,k} for k = 1..M-1
        for k in range(1, M):
            c2_ik = q_id[(i, k)] + 1
            lines.append(f"pol {prev} {c2_ik} + s ;");  cur += 1; prev = cur
        # K = prev + pigeon_i
        lines.append(f"pol {prev} {pig_i} + s ;");  cur += 1; prev = cur
        # L_k = prev + C1_{i,k} for k = 1..M-1
        for k in range(1, M):
            c1_ik = q_id[(i, k)]
            lines.append(f"pol {prev} {c1_ik} + s ;");  cur += 1; prev = cur
        new_pigeon[i] = prev

    # Step 3: derive Q-mutex clauses.  Same template as PHP-4-3 (7 pol per).
    new_mutex = {}
    for k in range(1, M):
        for i in range(1, n - 1):
            for j in range(i + 1, n):
                c3_i = q_id[(i, k)] + 2;  c4_i = q_id[(i, k)] + 3
                c3_j = q_id[(j, k)] + 2;  c4_j = q_id[(j, k)] + 3
                mut_ij_k = layer_in.mutex[(i, j, k)]
                mut_ij_M = layer_in.mutex[(i, j, M)]
                # mutex with pigeon n; pair (i, n) and (j, n).
                mut_in_k = layer_in.mutex.get((i, n, k), layer_in.mutex.get((n, i, k)))
                mut_jn_k = layer_in.mutex.get((j, n, k), layer_in.mutex.get((n, j, k)))
                lines.append(f"% Q-mutex ~Q_{{{i},{k}}} + ~Q_{{{j},{k}}} (7 pol steps).")
                # Case 1 (2 pol)
                lines.append(f"pol {c4_i} {mut_ij_k} + s ;");  cur += 1; r1 = cur
                lines.append(f"pol {r1} {c4_j} + s ;");  cur += 1; case1 = cur
                # Case 2 (4 pol)
                lines.append(f"pol {c3_i} {mut_in_k} + s ;");  cur += 1; sg = cur
                lines.append(f"pol {sg} {mut_ij_M} + s ;");  cur += 1; sp = cur
                lines.append(f"pol {sp} {c3_j} + s ;");  cur += 1; spp = cur
                lines.append(f"pol {spp} {mut_jn_k} + s ;");  cur += 1; case2 = cur
                # Combine (1 pol)
                lines.append(f"pol {case1} {case2} + s ;");  cur += 1; qm = cur
                new_mutex[(i, j, k)] = qm

    lines.append("")
    new_layer = Layer(new_n, new_M,
                      name_fn=lambda i, j: f"Q{layer_idx}_{i}_{j}",
                      pigeon_ids=new_pigeon, mutex_ids=new_mutex)
    return cur, new_layer

# ─── Closure for innermost layer ────────────────────────────────────────────

def emit_closure(layer, lines, cur):
    """Innermost step.  We arrive here with PHP-K-(K-1) for some K, then
    apply M-1 reductions total until we have PHP-(N-M+1)-1.  But the
    cleanest closure is at PHP-3-2 via 1 red+autoprove (which we know works).

    Strategy:
      - If layer.n_holes == 2 (= PHP-K-2 with K >= 3): apply 1 cyclic-pigeon red
        + rup.  Witness cycles pigeons 1..K (in current layer's names).
      - If layer.n_holes == 1: emit rup directly (BCP from pigeon clauses +
        mutex closes empty).

    Returns updated cur.
    """
    K = layer.n_pigeons
    M = layer.n_holes
    if M == 2 and K >= 3:
        # Cycle pigeons 1..K across both P-vars (= layer's current vars) and... well
        # actually we don't need to cycle anything other than the current-layer vars
        # because previous layers' P vars are already consumed (the derived Q-pigeon
        # and Q-mutex clauses only reference current-layer vars).
        sub = []
        for src in range(1, K + 1):
            dst = 1 if src == K else src + 1
            for h in range(1, M + 1):
                sub.append(f"{layer.name(src, h)} -> {layer.name(dst, h)}")
        lines.append(f"% Closure: PHP-{K}-{M} via cyclic-pigeon red.")
        lines.append(f"red 1 {layer.name(1, 1)} >= 1 : {' '.join(sub)} ;")
        cur += 1
        return cur
    elif M == 1:
        # K pigeons in 1 hole: pigeon clauses force each pigeon in hole 1;
        # any pair-mutex blocks two; immediate empty by RUP.
        lines.append(f"% Closure: PHP-{K}-{M} (K pigeons in 1 hole) trivially UNSAT.")
        return cur
    else:
        raise NotImplementedError(f"closure for PHP-{K}-{M} not implemented")

# ─── Main proof generator ───────────────────────────────────────────────────

def gen_proof(N, M, cnf):
    """Generate the full Cook proof for PHP-N-M.

    Layer 0 (root): use original DIMACS x vars + clause IDs from CNF load.
    Apply M-2 Cook reductions (to PHP-(N-M+2)-2), then closure via cyclic red.
    """
    assert N > M >= 2, f"need N > M >= 2; got N={N} M={M}"

    lines = [
        "pseudo-Boolean proof version 3.0",
        f"% Cook 1976 PHP-{N}-{M} proof via {M-2} Cook reductions + closure.",
        f"f {len(cnf)};",
        ""
    ]
    cur = len(cnf)

    # Build layer 0 (original CNF).
    def x(i, j): return f"x{(i-1)*M + j}"
    pigeon0 = {i: i for i in range(1, N + 1)}
    pairs = [(a, b) for a in range(1, N + 1) for b in range(a + 1, N + 1)]
    mutex0 = {(i, j, k): 1 + N + (k - 1) * len(pairs) + pairs.index((i, j))
              for k in range(1, M + 1)
              for (i, j) in pairs}
    layer0 = Layer(N, M, name_fn=x, pigeon_ids=pigeon0, mutex_ids=mutex0)

    # Apply M-2 reductions until we reach PHP-(N-M+2)-2.
    layer = layer0
    layer_idx = 0
    while layer.n_holes > 2:
        layer_idx += 1
        cur, layer = emit_layer_reduction(layer, layer_idx, lines, cur)

    # Closure.
    cur = emit_closure(layer, lines, cur)

    lines.append("rup >= 1 ;")
    lines.append("output NONE;")
    lines.append("conclusion UNSAT : -1;")
    lines.append("end pseudo-Boolean proof;")
    return "\n".join(lines) + "\n"

# ─── CLI ────────────────────────────────────────────────────────────────────

def write_cnf(path, clauses, nvars):
    with open(path, "w") as f:
        f.write(f"p cnf {nvars} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(str(l) for l in c) + " 0\n")

def main():
    if len(sys.argv) != 4:
        print(__doc__); sys.exit(1)
    N = int(sys.argv[1]); M = int(sys.argv[2])
    out = sys.argv[3]
    os.makedirs(out, exist_ok=True)

    cnf = php_cnf(N, M)
    cnf_path = os.path.join(out, f"php_{N}_{M}.cnf")
    pbp_path = os.path.join(out, f"php_{N}_{M}.pbp")
    write_cnf(cnf_path, cnf, N * M)
    print(f"wrote {cnf_path}: {N * M} vars, {len(cnf)} clauses")

    proof = gen_proof(N, M, cnf)
    with open(pbp_path, "w") as f:
        f.write(proof)
    print(f"wrote {pbp_path}: {proof.count(chr(10))} lines")

if __name__ == "__main__":
    main()
