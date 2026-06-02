#!/usr/bin/env python3
"""
OpenEvolve evaluator for the matrix-method SAT solver's `eff` backend.

For every candidate program OpenEvolve hands us, this evaluator:

  1. Spins up a temporary git worktree of the repo (fast on APFS).
  2. Splices the candidate's EVOLVE-BLOCK back into
     `src/dual/path_effective.rs` in the worktree.
  3. Runs `cargo build --release --bin sat` in the worktree.
  4. Runs `run_benchmark.py` on a tiered slice of `evo/`, scoring:
       * compiled         — did cargo build succeed?
       * sound            — zero MISMATCH rows?  (mutations that
                            produce wrong-UNSAT verdicts get
                            rejected, hard.)
       * solved           — SAT + UNSAT row count (primary maximize)
       * neg_time         — −(sum of solve times)  (secondary; max
                            ⇒ minimize total CPU)
       * timeout_progress — mean(paths_fraction) over TIMEOUT rows
                            (tertiary; partial credit for "got
                            further before timing out")
  5. Cleans up the worktree.

Tiered evaluation cascades:

   smoke  (~10s/eval)  → 6 problems @ 5s timeout, 4 workers
                         Gates on `compiled` + `sound` only.
   quick  (~50s/eval)  → 20 problems @ 20s timeout, 8 workers
                         Adds rough `solved` / `neg_time` signal.
   full   (~4min/eval) → 81 problems @ 30s timeout, 10 workers
                         Production score.

OpenEvolve uses each tier's metrics to decide whether a candidate
advances; only the survivors hit the expensive `full` tier.

Usage:
    python evaluator.py <candidate.rs>            # full evaluation
    python evaluator.py <candidate.rs> --tier smoke
    python evaluator.py <candidate.rs> --json     # machine-readable
"""

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Optional

# ─── Locations ────────────────────────────────────────────────────────
THIS_FILE = Path(__file__).resolve()
EVOLVE_DIR = THIS_FILE.parent                 # evo/evolve
EVO_DIR    = EVOLVE_DIR.parent                # evo
REPO_ROOT  = EVO_DIR.parent                    # repo root
TARGET_RS  = REPO_ROOT / "src" / "dual" / "path_effective.rs"
RUN_BENCH  = REPO_ROOT / "tools" / "gbd" / "run_benchmark.py"
EVO_INDEX  = EVO_DIR / "curated_struct_eff.jsonl"

# ─── Tier configurations ──────────────────────────────────────────────
# (n_problems, per-instance timeout seconds, parallel workers)
#
# NOTE on soundness coverage: the `evolve_guard` contract checks (and
# the SAT-witness check) only fire when a candidate's unsound code is
# *exercised*.  The smoke tier's first-6 records are uniform-cost
# `bench_*` instances where `should_reorder_sum` is usually false, so
# they don't exercise the Sum/Prod reordering paths — a contract
# violation can slip through smoke.  That's fine: it's caught at quick
# (which includes ordering-sensitive `3col`/`Break` instances) before
# it can affect fitness, because the cascade returns the moment any
# tier reports sound=0.  Smoke is only a cheap pre-filter for
# compile-fail / wildly-broken candidates.
TIERS = {
    "smoke": {"limit":  6, "timeout":  5, "parallel": 4, "deadline_s": 60},
    "quick": {"limit": 20, "timeout": 20, "parallel": 8, "deadline_s": 300},
    "full":  {"limit":  0, "timeout": 30, "parallel": 10, "deadline_s": 1800},
}

# Wall-clock cap on `cargo build` — if a mutation generates pathological
# Rust that takes forever to typecheck (rare but possible) we bail.
BUILD_TIMEOUT_S = 180


# ─── Helpers ──────────────────────────────────────────────────────────
EVOLVE_START = "// EVOLVE-BLOCK-START"
EVOLVE_END   = "// EVOLVE-BLOCK-END"


def extract_evolve_block(text: str) -> str:
    """Pull out the EVOLVE-BLOCK contents (between the START / END
    marker lines, both markers excluded).  Caller guarantees exactly
    one block exists.  Raises ValueError otherwise."""
    lines = text.splitlines(keepends=True)
    start = end = None
    for i, ln in enumerate(lines):
        if EVOLVE_START in ln and start is None: start = i
        elif EVOLVE_END in ln and end is None:   end = i
    if start is None or end is None or end <= start:
        raise ValueError(f"missing/malformed EVOLVE-BLOCK markers "
                         f"(start={start}, end={end})")
    return "".join(lines[start:end + 1])


def splice_evolve_block(target_text: str, new_block: str) -> str:
    """Replace the EVOLVE-BLOCK in `target_text` (the live source
    file) with `new_block` (the candidate's block, INCLUDING its
    marker lines).  Returns the rewritten file contents."""
    lines = target_text.splitlines(keepends=True)
    start = end = None
    for i, ln in enumerate(lines):
        if EVOLVE_START in ln and start is None: start = i
        elif EVOLVE_END in ln and end is None:   end = i
    if start is None or end is None or end <= start:
        raise ValueError("target file missing EVOLVE-BLOCK markers")
    before = "".join(lines[:start])
    after  = "".join(lines[end + 1:])
    # Ensure exactly one trailing newline on the spliced block so we
    # don't accidentally collapse lines.
    if not new_block.endswith("\n"):
        new_block += "\n"
    return before + new_block + after


# ─── Scratch-dir sandbox ──────────────────────────────────────────────
#
# We rsync the WORKING TREE (not `git HEAD`) into /tmp so uncommitted
# changes — including EVOLVE-BLOCK markers added before this rig
# went live — flow into the eval naturally.  Cost: each candidate
# gets a fresh `target/`, so cargo builds from scratch (~30s instead
# of ~5s incremental).  Worth it for the simplicity; the LLM call
# itself dominates total iteration time anyway.
#
# Excludes are critical: `target/` (gigs of build cache), `.venv/`
# (gigs of Python), `.git/` (slow to copy, we don't need it for
# the eval), and `evo/evolve/runs/` (the very directory we're
# writing into — would create an infinite recursion).
RSYNC_EXCLUDES = [
    "--exclude=target/",
    "--exclude=.venv/",
    "--exclude=.git/",
    "--exclude=evo/evolve/runs/",
    "--exclude=__pycache__/",
    "--exclude=node_modules/",
    "--exclude=nested-boxes/",
    "--exclude=*.pyc",
]


@dataclass
class Scratch:
    path: Path

    def cleanup(self) -> None:
        """Remove the scratch tree.  Best-effort; logs but doesn't raise."""
        try:
            shutil.rmtree(self.path, ignore_errors=True)
        except Exception as e:
            print(f"warn: scratch cleanup failed: {e}", file=sys.stderr)


def make_scratch() -> Scratch:
    """Rsync the working tree into a fresh /tmp dir.  ~5s on APFS for
    a clean repo (no `target/` is the main savings — the source tree
    is small).  Excludes are listed in `RSYNC_EXCLUDES`."""
    work = Path(tempfile.mkdtemp(prefix="openevolve-eff-"))
    r = subprocess.run(
        ["rsync", "-a", *RSYNC_EXCLUDES,
         f"{REPO_ROOT}/", f"{work}/"],
        capture_output=True, text=True,
    )
    if r.returncode != 0:
        raise RuntimeError(f"rsync failed: {r.stderr}")
    return Scratch(path=work)


# ─── Build + benchmark ────────────────────────────────────────────────
def cargo_build(worktree: Path) -> Optional[str]:
    """Build `sat` + `sat-cover-verify` (release, `--features
    evolve_wide`) in the worktree.  Returns None on success; the stderr
    tail on failure (capped at 4KB for OpenEvolve's artifact stream).

    `evolve_wide` is OPEN-evolution mode: it COMPILES OUT the
    permutation / keep-reachable guards so a mutation MAY drop branches
    (aggressive pruning) and actually run — we *want* to evaluate those,
    not hard-abort them.  Soundness is enforced downstream by the
    run_benchmark gate: ground-truth (drat-verified label) mismatch +
    SAT-witness + UNSAT cover-proof checks.  An always-on index
    sanitizer still prevents any panic from a malformed index.
    `sat-cover-verify` is needed for the --verify-unsat-proof gate."""
    r = subprocess.run(
        ["cargo", "build", "--release", "--bin", "sat",
         "--bin", "sat-cover-verify", "--features", "evolve_wide"],
        cwd=worktree, capture_output=True, text=True,
        timeout=BUILD_TIMEOUT_S,
    )
    if r.returncode != 0:
        # Tail of stderr — the actual error message is at the bottom.
        return r.stderr[-4000:]
    return None


def run_tier(worktree: Path, tier: str, out_dir: Path) -> Dict:
    """Run `run_benchmark.py` for the given tier; return parsed
    metrics dict.  Raises on subprocess failure."""
    cfg = TIERS[tier]
    out_md = out_dir / f"eval_{tier}.md"
    cmd = [
        "uv", "run",
        "--project", str(REPO_ROOT),
        str(RUN_BENCH),
        "--index", str(EVO_INDEX),
        "-b", "eff_cover",
        "-t", str(cfg["timeout"]),
        "-j", str(cfg["parallel"]),
        "-o", str(out_md),
        "--no-progress",
    ]
    if cfg["limit"] > 0:
        cmd.extend(["--limit", str(cfg["limit"])])
    # Point sat at the worktree's freshly-built binary by prepending
    # its target/release to PATH; run_benchmark.py picks up the first
    # `sat` it finds.  Actually run_benchmark.py uses SAT_BIN = REPO_ROOT
    # / "target/release/sat" — a hardcoded path.  Easier to set the
    # SAT_BIN env override... wait, there isn't one.  So we run
    # run_benchmark.py from inside the worktree so its REPO_ROOT
    # detection finds the worktree's binary.
    env = os.environ.copy()
    # Override the script's --project flag scope: when invoked via
    # `uv run --project <worktree>`, uv looks for pyproject.toml in
    # the worktree (which we have, since it's checked in).
    cmd_pyproject = ["uv", "run",
                     "--project", str(worktree),
                     str(worktree / "tools" / "gbd" / "run_benchmark.py"),
                     "--index", str(EVO_INDEX),
                     "-b", "eff_cover",
                     "-t", str(cfg["timeout"]),
                     "-j", str(cfg["parallel"]),
                     "-o", str(out_md),
                     "--no-progress",
                     # Soundness lines of defense beyond ground-truth
                     # mismatch.  --verify-sat-witness: re-check every SAT
                     # model against the CNF (catches a bogus witness).
                     # --verify-unsat-proof: re-derive + check a matrix
                     # cover for every UNSAT (a complete cover = proven
                     # UNSAT; an incomplete one is just "unproven", still
                     # a solve; a re-run that flips to SAT = hard fail).
                     "--verify-sat-witness",
                     "--verify-unsat-proof"]
    if cfg["limit"] > 0:
        cmd_pyproject.extend(["--limit", str(cfg["limit"])])

    r = subprocess.run(cmd_pyproject, cwd=worktree, capture_output=True,
                       text=True, env=env, timeout=cfg["deadline_s"])
    if r.returncode not in (0, 1):
        # run_benchmark.py exits 1 on MISMATCH — that's a valid
        # outcome here (we WANT to detect it).  Other non-zero
        # exits = harness error.
        raise RuntimeError(f"run_benchmark.py exit={r.returncode}\n"
                           f"stderr tail:\n{r.stderr[-2000:]}")

    json_path = out_md.with_suffix(".json")
    if not json_path.exists():
        raise RuntimeError(f"run_benchmark.py didn't produce JSON at {json_path}\n"
                           f"stderr tail:\n{r.stderr[-2000:]}")
    payload = json.loads(json_path.read_text())
    return payload


# ─── Scoring ──────────────────────────────────────────────────────────
def combined_score(compiled: float, sound: float, solved: float,
                   total_time_s: float, timeout_progress: float,
                   n_problems: int, per_problem_timeout_s: float) -> float:
    """Collapse the multi-objective fitness into the single scalar
    OpenEvolve uses for selection pressure (it maximizes this).

    Priority order (your stated objectives):
        1. max problems solved        — dominant integer term
        2. min total solve time        — secondary, in [0, 0.7)
        3. max timeout-progress        — tertiary, in [0, 0.3)

    Construction guarantees lexicographic ordering: one extra solved
    problem (+1.0) always outweighs ANY combination of the speed +
    progress bonuses (which sum to < 1.0).  Within the same `solved`
    count, faster wins; ties on speed broken by timeout-progress.

    Gates: not-compiled or not-sound → 0.0 (worst possible, but
    distinguishable from a compiled-but-useless candidate which
    still earns its `solved` term).
    """
    if compiled < 1.0 or sound < 1.0:
        return 0.0
    # Speed bonus: fraction of the available solve-budget you did NOT
    # consume.  budget = solved × per-problem-timeout.  Instant solves
    # → ~0.7; solves that each crawl to the timeout → ~0.0.  Guard the
    # solved==0 case (no budget, no bonus).
    if solved > 0 and per_problem_timeout_s > 0:
        budget = solved * per_problem_timeout_s
        speed_norm = max(0.0, 1.0 - total_time_s / budget)
    else:
        speed_norm = 0.0
    return float(solved) + 0.7 * speed_norm + 0.3 * float(timeout_progress)


def score_from_payload(payload: Dict, per_problem_timeout_s: float) -> Dict:
    """Reduce a run_benchmark.py JSON payload to OpenEvolve's flat
    fitness dict.  Soundness gate fires inside this function: if ANY
    per-instance soundness failure is present, the candidate is marked
    unsound (sound=0, combined_score=0).

    A soundness failure is any of (all surfaced as the per-result
    `mismatch` flag by run_benchmark):
      * verdict ≠ proof-verified ground truth (wrong SAT/UNSAT),
      * `witness_ok is False` (SAT verdict, bogus model — only when
        run with --verify-sat-witness),
      * `guard_abort` (the eff `evolve_guard` contract tripped → the
        process hard-exited 101).

    We count these from the per-result records, NOT the summary's
    `MISMATCH` bucket — that bucket is keyed by the *markdown* result
    label, which never appears in the JSON summary (it groups by the
    parsed verdict), so reading it would always see zero.

    `per_problem_timeout_s` is the tier's per-instance timeout, used
    to normalize the speed component of `combined_score`."""
    results = payload.get("results", [])
    # A soundness failure is any of: verdict ≠ proof-verified ground
    # truth; bogus SAT witness; tripped evolve_guard; or an UNSAT whose
    # cover re-run flipped to SAT (`unsat_proof_ok is False` — a direct
    # contradiction).  NOTE: an *unprovable* UNSAT (`unsat_proof_ok is
    # None`, cover incomplete) is NOT a failure — it's a correct solve we
    # just couldn't certify (the matrix cover is incomplete for some
    # UNSAT instances); soundness for those rests on the ground-truth
    # label.  See the more-complete-unsat-proofs task.
    n_mismatch = sum(1 for r in results
                     if r.get("mismatch") or r.get("guard_abort")
                     or r.get("witness_ok") is False
                     or r.get("unsat_proof_ok") is False)
    if n_mismatch > 0:
        return {
            "combined_score": 0.0,
            "compiled": 1.0,
            "sound":    0.0,
            "solved":   0.0,
            "neg_time": 0.0,
            "timeout_progress": 0.0,
            "n_mismatch": n_mismatch,
        }
    solved = sum(1 for r in results if r.get("result") in ("SAT", "UNSAT"))
    total_t = sum(r.get("time_s") or 0.0
                  for r in results if r.get("result") in ("SAT", "UNSAT"))
    timeout_rows = [r for r in results if r.get("result") == "TIMEOUT"]
    if timeout_rows:
        fracs = [r.get("paths_fraction") or 0.0 for r in timeout_rows]
        tp = sum(fracs) / len(fracs)
    else:
        tp = 0.0
    cs = combined_score(1.0, 1.0, float(solved), float(total_t),
                        float(tp), len(results), per_problem_timeout_s)
    return {
        "combined_score":   cs,
        "compiled":         1.0,
        "sound":            1.0,
        "solved":           float(solved),
        "neg_time":         -float(total_t),
        "timeout_progress": float(tp),
        "n_problems":       len(results),
        # How many of the solved UNSATs carry a complete verified cover
        # proof (informational — proofs are a bonus, not part of the
        # solved-dominant combined_score; unprovable UNSATs still count
        # as solves).
        "proven_unsat":     sum(1 for r in results
                                if r.get("unsat_proof_ok") is True),
    }


def failed_score(reason: str, detail: str = "") -> Dict:
    """Fitness dict for the various 'this candidate is unusable' cases."""
    return {
        "combined_score": 0.0,
        "compiled": 0.0,
        "sound":    0.0,
        "solved":   0.0,
        "neg_time": -1e9,
        "timeout_progress": 0.0,
        "_failure_reason": reason,
        "_failure_detail": detail[:500],
    }


# ─── Top-level entry: OpenEvolve will call evaluate(file_path) ────────
def evaluate(candidate_path: str, tier: Optional[str] = None) -> Dict:
    """Score a single candidate `path_effective.rs` (or a file with
    just the EVOLVE-BLOCK contents — we extract).  `tier` selects
    which tier to run (None = cascade through all three, returning
    the deepest-reached metrics).  Returns the fitness dict
    OpenEvolve sorts on."""
    candidate = Path(candidate_path).read_text()
    try:
        new_block = extract_evolve_block(candidate)
    except ValueError as e:
        return failed_score("no_evolve_block", str(e))

    scratch = None
    try:
        scratch = make_scratch()
        # Splice the candidate into the scratch tree's path_effective.rs.
        tgt = scratch.path / "src" / "dual" / "path_effective.rs"
        spliced = splice_evolve_block(tgt.read_text(), new_block)
        tgt.write_text(spliced)

        # Build.
        build_err = cargo_build(scratch.path)
        if build_err is not None:
            return failed_score("compile_failed", build_err)

        # Tier cascade.
        out_dir = scratch.path / "evo" / "evolve" / "runs" / f"pid-{os.getpid()}"
        out_dir.mkdir(parents=True, exist_ok=True)
        tiers_to_run = [tier] if tier else ["smoke", "quick", "full"]
        last_score: Dict = {}
        for t in tiers_to_run:
            payload = run_tier(scratch.path, t, out_dir)
            score = score_from_payload(payload, TIERS[t]["timeout"])
            score["_tier"] = t
            last_score = score
            # Soundness gate: if MISMATCH appeared at ANY tier, abort
            # the cascade — we don't trust the candidate to be safe
            # to keep evaluating.
            if score["sound"] == 0.0:
                return score
            # Quality gate: smoke tier must solve at least 50% of
            # its 6 problems to be worth quick/full evaluation.
            # Tweak this if too many promising candidates get culled
            # early.
            if t == "smoke" and score["solved"] < 3.0:
                return score
        return last_score

    except subprocess.TimeoutExpired as e:
        return failed_score("timeout",
                            f"{getattr(e, 'cmd', 'unknown')} ran past "
                            f"{getattr(e, 'timeout', '?')}s")
    except Exception as e:
        return failed_score("exception", f"{type(e).__name__}: {e}")
    finally:
        if scratch is not None:
            scratch.cleanup()


# ─── CLI ──────────────────────────────────────────────────────────────
def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("candidate", help="Path to candidate .rs file")
    ap.add_argument("--tier", choices=list(TIERS.keys()),
                    help="Run only this tier instead of cascading.")
    ap.add_argument("--json", action="store_true",
                    help="Emit fitness dict as JSON on stdout.")
    args = ap.parse_args()

    score = evaluate(args.candidate, tier=args.tier)
    if args.json:
        json.dump(score, sys.stdout, indent=2, default=str)
        print()
    else:
        for k, v in score.items():
            print(f"{k:>22} = {v}")
    return 0 if score.get("sound", 0) == 1.0 else 1


if __name__ == "__main__":
    sys.exit(main())
