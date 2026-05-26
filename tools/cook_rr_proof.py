#!/usr/bin/env python3
"""
RoundRobin cardinality proof generator (VeriPB PBP).

For RR(n teams, d days) with n_pairs = C(n, 2) > d * (n / 2), generates:
  - DIMACS CNF (rr_n_d.cnf): pigeon + team-day mutex + pair-day mutex.
  - VeriPB proof (rr_n_d.pbp): cardinality argument:
      Step 1: per (team, day) at-most-1 (n*d constraints from team-mutex sum/2).
      Step 2: per day at-most-n/2 (d constraints from n team's at-most-1 / 2).
      Step 3: total at-most-d*n/2 (1 constraint by summing days).
      Step 4: pigeon-sum at-least-n_pairs (1 constraint).
      Step 5: contradiction (1 pol + 1 rup).

Proof size O(n*d + d + 4) → linear in input.  VeriPB verification: ms.

CNF layout (own ordering):
  - 1..n_pairs: pigeon clauses (each pair plays SOME day).
  - n_pairs + 1..(team_day_block): team-day mutex grouped by (team, day, lex pair).
  - then: pair-day mutex (per pair, lex day pair).

Usage:
    cook_rr_proof.py <n> <d> <out_dir>
"""
import os
import sys

def gen(n_teams, d_days, out_dir):
    assert n_teams >= 2 and d_days >= 1
    n_pairs = n_teams * (n_teams - 1) // 2
    capacity = d_days * n_teams // 2
    if n_pairs <= capacity:
        print(f"WARN: RR n={n_teams} d={d_days} is SAT or borderline "
              f"({n_pairs} pairs ≤ {capacity} slots)")
    # Pair indexing: pairs in lex order.
    pairs = [(i, j) for i in range(n_teams) for j in range(i + 1, n_teams)]
    def var(pair_idx, day_idx): return pair_idx * d_days + day_idx + 1
    n_vars = n_pairs * d_days

    # --- CNF assembly ---
    clauses = []
    pigeon_ids = {}   # pigeon_ids[pair_idx] = 1-indexed clause id
    team_day_mutex_ids = {}  # (team, day, pair_idx_i, pair_idx_j) → id (i<j)

    # Pigeon clauses
    for p in range(n_pairs):
        clauses.append([var(p, k) for k in range(d_days)])
        pigeon_ids[p] = len(clauses)

    # Team-day mutex
    for t in range(n_teams):
        matches_of_t = sorted([pi for pi, pair in enumerate(pairs) if t in pair])
        for k in range(d_days):
            for i in range(len(matches_of_t)):
                for j in range(i + 1, len(matches_of_t)):
                    pi, pj = matches_of_t[i], matches_of_t[j]
                    clauses.append([-var(pi, k), -var(pj, k)])
                    team_day_mutex_ids[(t, k, pi, pj)] = len(clauses)

    # Pair-day mutex (each pair plays at most 1 day)
    pair_day_mutex_ids = {}
    for p in range(n_pairs):
        for k1 in range(d_days):
            for k2 in range(k1 + 1, d_days):
                clauses.append([-var(p, k1), -var(p, k2)])
                pair_day_mutex_ids[(p, k1, k2)] = len(clauses)

    # --- Write CNF ---
    cnf_path = os.path.join(out_dir, f"rr_n{n_teams}_d{d_days}.cnf")
    with open(cnf_path, "w") as f:
        f.write(f"p cnf {n_vars} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(str(l) for l in c) + " 0\n")
    print(f"wrote {cnf_path}: {n_vars} vars, {len(clauses)} clauses")

    # --- Build PBP ---
    lines = [
        "pseudo-Boolean proof version 3.0",
        f"% RoundRobin n={n_teams} d={d_days}: {n_pairs} matches > {capacity} slots.",
        f"f {len(clauses)};",
        ""
    ]
    cur = len(clauses)
    K = n_teams - 1   # matches per team

    # Step 1: per (team, day) at-most-1.
    # For each (t, k), sum the C(K, 2) team-day mutex clauses, divide by K-1
    # (each match appears in K-1 pairs).
    # Result: ~x_{(t,j1),k} + ~x_{(t,j2),k} + ... + ~x_{(t,jK),k} >= K-1.
    # That's at-most-1 of K matches involving t on day k.
    team_day_amo_ids = {}
    lines.append(f"% --- Step 1: per (team, day) at-most-1 ({n_teams * d_days} constraints) ---")
    for t in range(n_teams):
        matches_of_t = sorted([pi for pi, pair in enumerate(pairs) if t in pair])
        for k in range(d_days):
            # Sum all C(K, 2) mutex for this (t, k), divide by K-1.
            mut_ids = []
            for i in range(len(matches_of_t)):
                for j in range(i + 1, len(matches_of_t)):
                    pi, pj = matches_of_t[i], matches_of_t[j]
                    mut_ids.append(team_day_mutex_ids[(t, k, pi, pj)])
            # Build pol expression: ID1 ID2 + ID3 + ... IDn + (K-1) d
            expr = f"{mut_ids[0]}"
            for mid in mut_ids[1:]:
                expr += f" {mid} +"
            expr += f" {K - 1} d"
            lines.append(f"pol {expr} ;")
            cur += 1
            team_day_amo_ids[(t, k)] = cur
    lines.append("")

    # Step 2: per day at-most-n/2.
    # For each day k, sum n team-day-amo's, divide by 2.
    # Each match x_{(i,j),k} appears in 2 team-day-amos (team i's and team j's).
    # Sum: 2*sum_matches ~x_{*,k} >= n*(K-1).
    # Div by 2: sum ~x_{*,k} >= ceil(n*(K-1)/2) = n*(K-1)/2 if n*(K-1) even.
    # For n even (e.g., 16), K-1 = 15, n*(K-1) = 240, /2 = 120.  Sum has n_pairs vars = C(n,2).
    # at-most-(n_pairs - n*(K-1)/2) = at-most-n/2.  ✓
    per_day_amo_ids = {}
    lines.append(f"% --- Step 2: per day at-most-{n_teams//2} ({d_days} constraints) ---")
    for k in range(d_days):
        team_ids = [team_day_amo_ids[(t, k)] for t in range(n_teams)]
        expr = f"{team_ids[0]}"
        for tid in team_ids[1:]:
            expr += f" {tid} +"
        expr += f" 2 d"
        lines.append(f"pol {expr} ;")
        cur += 1
        per_day_amo_ids[k] = cur
    lines.append("")

    # Step 3: total at-most-(d*n/2): sum per_day_amo over days.
    lines.append("% --- Step 3: sum per-day at-most → total at-most ---")
    expr = f"{per_day_amo_ids[0]}"
    for k in range(1, d_days):
        expr += f" {per_day_amo_ids[k]} +"
    lines.append(f"pol {expr} ;")
    cur += 1
    total_amo_id = cur
    lines.append("")

    # Step 4: pigeon-sum (sum of n_pairs pigeon clauses).
    lines.append("% --- Step 4: sum pigeon clauses → at-least-n_pairs ---")
    expr = f"{pigeon_ids[0]}"
    for p in range(1, n_pairs):
        expr += f" {pigeon_ids[p]} +"
    lines.append(f"pol {expr} ;")
    cur += 1
    pigeon_sum_id = cur
    lines.append("")

    # Step 5: contradiction via pol sum + rup empty.
    lines.append("% --- Step 5: combine → contradiction ---")
    lines.append(f"pol {total_amo_id} {pigeon_sum_id} + ;")
    cur += 1
    lines.append("rup >= 1 ;")
    lines.append("")
    lines.append("output NONE;")
    lines.append("conclusion UNSAT : -1;")
    lines.append("end pseudo-Boolean proof;")

    pbp_path = os.path.join(out_dir, f"rr_n{n_teams}_d{d_days}.pbp")
    with open(pbp_path, "w") as f:
        f.write("\n".join(lines) + "\n")
    print(f"wrote {pbp_path}: {len(lines)} lines")

def main():
    if len(sys.argv) != 4:
        print(__doc__); sys.exit(1)
    n = int(sys.argv[1]); d = int(sys.argv[2])
    out = sys.argv[3]
    os.makedirs(out, exist_ok=True)
    gen(n, d, out)

if __name__ == "__main__":
    main()
