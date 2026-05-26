#!/usr/bin/env python3
"""
RoundRobin cardinality proof generator (VeriPB PBP) with at-most-1
subroutine derived via recursive red rules.

For RR(n teams, d days) with C(n, 2) > d * (n / 2), generates:
  - DIMACS CNF (rr_n_d.cnf)
  - VeriPB proof (rr_n_d.pbp)

Proof structure:
  Step 0: derive IH(K) = at-most-1 over K vars from pairwise mutex.
          (For each team-day, K = n-1 matches involving that team.)
  Step 1: per (team, day) at-most-1 (IH(n-1) applied to that team's
          n-1 match vars on that day).
  Step 2: per day at-most-n/2 (sum n team-at-most-1's / 2).
  Step 3: total at-most-d*n/2 (sum over d days).
  Step 4: pigeon-sum at-least-C(n, 2).
  Step 5: contradiction via pol + rup.

At-most-1 subroutine (per Cook-PR insight):
  - K=3 base: pol-sum of 3 mutex / 2 → at-most-1.
  - K=k recursive: red IH(k) : x_k -> 0 using IH(k-1) in autoprove.

Total proof size: O(n^2 * d) — polynomial in input.

Usage:
    cook_rr_proof.py <n> <d> <out_dir>
"""
import os
import sys


def gen(n_teams, d_days, out_dir, match_official=True):
    """Generate RR(n, d) CNF + Cook proof.

    `match_official=True` produces a clause ordering matching the
    SAT-competition RoundRobin_n16_d13.cnf benchmark exactly:
       per-pair block (pigeon + C(d,2) pair-day mutex), then team-day mutex.
    """
    assert n_teams >= 2 and d_days >= 1
    n_pairs = n_teams * (n_teams - 1) // 2
    capacity = d_days * n_teams // 2
    if n_pairs <= capacity:
        print(f"WARN: RR n={n_teams} d={d_days} is SAT or borderline "
              f"({n_pairs} pairs ≤ {capacity} slots)")
    pairs = [(i, j) for i in range(n_teams) for j in range(i + 1, n_teams)]
    def var(pair_idx, day_idx): return pair_idx * d_days + day_idx + 1
    n_vars = n_pairs * d_days
    K = n_teams - 1   # matches per team

    # ─── CNF assembly ──────────────────────────────────────────────────────
    clauses = []
    pigeon_ids = {}
    pair_day_mutex_ids = {}
    team_day_mutex_ids = {}   # (team, day, pair_i, pair_j) -> CNF clause id

    if match_official:
        # Official layout: per-pair (pigeon + pair-day mutex), then per-(team, day).
        for p in range(n_pairs):
            clauses.append([var(p, k) for k in range(d_days)])
            pigeon_ids[p] = len(clauses)
            for k1 in range(d_days):
                for k2 in range(k1 + 1, d_days):
                    clauses.append([-var(p, k1), -var(p, k2)])
                    pair_day_mutex_ids[(p, k1, k2)] = len(clauses)
        for t in range(n_teams):
            matches_of_t = sorted([pi for pi, pair in enumerate(pairs) if t in pair])
            for k in range(d_days):
                for i in range(len(matches_of_t)):
                    for j in range(i + 1, len(matches_of_t)):
                        pi, pj = matches_of_t[i], matches_of_t[j]
                        clauses.append([-var(pi, k), -var(pj, k)])
                        team_day_mutex_ids[(t, k, pi, pj)] = len(clauses)
    else:
        # Original (our) layout: pigeons, team-day mutex, pair-day mutex.
        for p in range(n_pairs):
            clauses.append([var(p, k) for k in range(d_days)])
            pigeon_ids[p] = len(clauses)
        for t in range(n_teams):
            matches_of_t = sorted([pi for pi, pair in enumerate(pairs) if t in pair])
            for k in range(d_days):
                for i in range(len(matches_of_t)):
                    for j in range(i + 1, len(matches_of_t)):
                        pi, pj = matches_of_t[i], matches_of_t[j]
                        clauses.append([-var(pi, k), -var(pj, k)])
                        team_day_mutex_ids[(t, k, pi, pj)] = len(clauses)
        for p in range(n_pairs):
            for k1 in range(d_days):
                for k2 in range(k1 + 1, d_days):
                    clauses.append([-var(p, k1), -var(p, k2)])
                    pair_day_mutex_ids[(p, k1, k2)] = len(clauses)

    cnf_path = os.path.join(out_dir, f"rr_n{n_teams}_d{d_days}.cnf")
    with open(cnf_path, "w") as f:
        f.write(f"p cnf {n_vars} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(str(l) for l in c) + " 0\n")
    print(f"wrote {cnf_path}: {n_vars} vars, {len(clauses)} clauses")

    # ─── PBP assembly ──────────────────────────────────────────────────────
    lines = [
        "pseudo-Boolean proof version 3.0",
        f"% RoundRobin n={n_teams} d={d_days}: {n_pairs} matches > {capacity} slots.",
        f"f {len(clauses)};",
        ""
    ]
    cur = len(clauses)

    # Step 1: per (team, day) at-most-1 via recursive-red Cook subroutine.
    #   For K = n-1 matches per team:
    #     Base K=3: pol of 3 mutex / 2 → at-most-1.
    #     K=k > 3: red IH(k) : x_k -> 0 using IH(k-1).
    #   Special case K=2: at-most-1 IS the binary mutex (use it directly).
    team_day_amo_ids = {}
    if K == 1:
        # Only 1 match per team per day → trivially at-most-1.
        raise NotImplementedError("n=2 RR has no team-day mutex (only 1 opponent)")
    lines.append(f"% --- Step 1: per (team, day) at-most-1 derived from {K}-var pairwise mutex ---")
    for t in range(n_teams):
        matches_of_t = sorted([pi for pi, pair in enumerate(pairs) if t in pair])
        for k in range(d_days):
            # Build IH chain over matches_of_t[0..K-1] for this (t, k).
            mvars = [f"x{var(p, k)}" for p in matches_of_t]
            if K == 2:
                # IH(2) is the binary mutex itself: just look up its ID.
                amo_id = team_day_mutex_ids[(t, k, matches_of_t[0], matches_of_t[1])]
                team_day_amo_ids[(t, k)] = amo_id
                continue

            # IH(3) base: pol of mutex(p0,p1), mutex(p0,p2), mutex(p1,p2) / 2
            m01 = team_day_mutex_ids[(t, k, matches_of_t[0], matches_of_t[1])]
            m02 = team_day_mutex_ids[(t, k, matches_of_t[0], matches_of_t[2])]
            m12 = team_day_mutex_ids[(t, k, matches_of_t[1], matches_of_t[2])]
            lines.append(f"% IH(3) for team {t} day {k}: at-most-1 of {mvars[0]}, {mvars[1]}, {mvars[2]}.")
            lines.append(f"pol {m01} {m02} + {m12} + 2 d ;")
            cur += 1
            current_ih = cur

            # IH(k) for k = 4..K via recursive red.
            for kk in range(4, K + 1):
                amo_lits = " ".join(f"+1 ~{mvars[i]}" for i in range(kk))
                witness_var = mvars[kk - 1]
                lines.append(f"red {amo_lits} >= {kk - 1} : {witness_var} -> 0 ;")
                cur += 1
                current_ih = cur

            team_day_amo_ids[(t, k)] = current_ih
    lines.append("")

    # Step 2: per day at-most-n/2 via sum of n team-amo's / 2.
    #   Each match var x_{(i,j),k} appears in 2 team-amo's (team i's and j's).
    #   Sum: 2 * sum ~x_{*,k} >= n * (K - 1).
    #   Divide by 2: sum ~x_{*,k} >= ceil(n*(K-1)/2).
    #   Expected: at-most-(n/2).  Sanity for n=16, K=15: sum ~x >= 120,
    #     so at-most-(C(16,2)-120) = at-most-(120-120) = at-most-0?  That's wrong.
    #   Actually sum ~x_{*,k} >= n*(K-1)/2 (assuming n even).  For n=16, K=15: ≥ 120.
    #     n_pairs (= C(16,2)) = 120 vars total per day.  120 - 120 = 0 → at-most-0.
    #     That can't be right.  Let me recheck.
    #
    #   For team t day k, IH(K) says ~x_{(t,j1),k} + ... + ~x_{(t,jK),k} >= K-1.
    #     There are K = n-1 vars in this sum (one per opponent of t).
    #   For n=16: K=15, so each team-amo IH(15) = sum of 15 ~x >= 14.
    #   Sum over n=16 teams: each var ~x_{pair,k} appears in 2 team-amos.
    #     LHS: 2 * sum_pair ~x_{pair,k} (n_pairs = 120 vars total).
    #     RHS: 16 * 14 = 224.
    #     So 2 sum_neg >= 224, sum_neg >= 112.
    #     n_pairs - sum_neg <= 120 - 112 = 8 = max true vars per day = at-most-8.  ✓
    #
    #   So pol C1 C2 + ... + 2 d yields sum_neg >= n * (K-1) / 2 = 112 for n=16.
    per_day_amo_ids = {}
    lines.append(f"% --- Step 2: per day at-most-{n_teams // 2} (= n/2 matches) ---")
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

    # Step 3: total at-most-(d * n/2): sum per_day over d days.
    lines.append("% --- Step 3: sum per-day at-most → total at-most ---")
    expr = f"{per_day_amo_ids[0]}"
    for k in range(1, d_days):
        expr += f" {per_day_amo_ids[k]} +"
    lines.append(f"pol {expr} ;")
    cur += 1
    total_amo_id = cur
    lines.append("")

    # Step 4: pigeon-sum at-least-n_pairs.
    lines.append("% --- Step 4: sum pigeon clauses → at-least-n_pairs ---")
    expr = f"{pigeon_ids[0]}"
    for p in range(1, n_pairs):
        expr += f" {pigeon_ids[p]} +"
    lines.append(f"pol {expr} ;")
    cur += 1
    pigeon_sum_id = cur
    lines.append("")

    # Step 5: contradiction via pol sum + rup.
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
