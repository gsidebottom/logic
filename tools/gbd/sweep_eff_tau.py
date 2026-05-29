#!/usr/bin/env python3
"""
Sweep `sat --eff-tau` over a curated JSONL index and emit a comparison
report.

Invokes `tools/gbd/run_benchmark.py` once per τ in the sweep list, each
producing its own per-problem benchmark .md.  After all τ runs complete,
parses the result tables and writes a unified `sweep_summary.md` that
shows:

  - Per-τ totals: solved, timed-out, MISMATCH, total CPU.
  - A win matrix: for each instance × τ, the result + time, with the
    fastest τ per instance highlighted.
  - A "best-τ-per-family" table when instance filenames suggest a
    family (e.g. Steiner-*, PHP-*, crypto-*).
  - The recommended τ — the one with the most instance wins
    (ties broken by total CPU time).

Designed to validate Option 2 ("variance-gated Sum reordering" in the
EffectiveCountWrapper) — does a single τ dominate plain eff (τ=0) on
all benchmark families?  If so, ship that τ as the new default.  If
not, the per-family table tells you which families want which τ.

Usage:
  tools/gbd/sweep_eff_tau.py --index sat_benchmarks/easy.jsonl \\
      --backend eff --timeout 60 --parallel 4

  # Custom τ list:
  tools/gbd/sweep_eff_tau.py --index easy.jsonl --backend greedy_eff \\
      --taus 0,0.3,0.5,1,2,inf

  # Filter instances (e.g. only short SAT problems):
  tools/gbd/sweep_eff_tau.py --index curated.jsonl --backend eff \\
      --filter "r['status']=='SAT' and r.get('nvars',0) < 2000"

The default τ list is `0,0.5,1,2,inf`:
  - 0      : always reorder (legacy baseline)
  - 0.5    : reorder when children span ≥ 10^0.5 ≈ 3.16×
  - 1      : reorder when children span ≥ 10×
  - 2      : reorder when children span ≥ 100×
  - inf    : never reorder (eff degrades to Prod zero-count filter only)
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Optional, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT  = SCRIPT_DIR.parent.parent
RUN_BENCH  = SCRIPT_DIR / "run_benchmark.py"

# Same row regex as run_benchmark.py (3-column compatible with the plotter).
ROW_RE = re.compile(
    r"^\|\s*([^|]+?)\s*\|\s*(SAT|UNSAT|TIMEOUT|UNKNOWN|MISMATCH)\s*\|\s*([^|]+?)\s*\|\s*$"
)


def parse_time(s: str) -> Optional[float]:
    """Convert '12.345s' / '<0.001s' / '60s' → float seconds."""
    s = s.strip()
    if s.startswith("got=") or s == "n/a":
        return None
    if s.startswith("<"):
        s = s[1:]
    if not s.endswith("s"):
        return None
    try:
        return float(s[:-1])
    except ValueError:
        return None


# Result-quality order for de-duplicating multiple rows with the same
# problem name (which happens when the input JSONL has duplicate
# records — see run_benchmark.py's `--no-dedupe` flag).  Lower number =
# more informative; when collapsing, keep the lowest-numbered.
_RESULT_QUALITY: Dict[str, int] = {
    "SAT": 0, "UNSAT": 0,
    "TIMEOUT": 1,
    "UNKNOWN": 2,
    "MISMATCH": 3,   # MISMATCH is a soundness signal — never silently override
}

def _better(a: Tuple[str, Optional[float]], b: Tuple[str, Optional[float]]) -> Tuple[str, Optional[float]]:
    """Pick the more-informative of two (result, secs) tuples.  Lower
    quality rank wins; ties (both solved) broken by fastest time."""
    qa = _RESULT_QUALITY.get(a[0], 99)
    qb = _RESULT_QUALITY.get(b[0], 99)
    if qa != qb: return a if qa < qb else b
    # Same result class.  Prefer the one with the smaller numeric time.
    ta, tb = a[1], b[1]
    if ta is None and tb is None: return a
    if ta is None: return b
    if tb is None: return a
    return a if ta <= tb else b


def parse_md(path: Path) -> Dict[str, Tuple[str, Optional[float]]]:
    """
    Read a run_benchmark .md → {problem: (result, secs_or_None)}.

    Defensive against same-name rows appearing more than once (which
    happens when the input JSONL has duplicate records — e.g. from
    multiple curate.py passes that all wrote results for the same
    instances).  When that happens we collapse via `_better`: prefer
    a solved result over TIMEOUT, prefer the fastest among solved.
    A `# WARNING: duplicate rows ...` comment in the output reflects
    this; emit_summary surfaces it too.
    """
    out: Dict[str, Tuple[str, Optional[float]]] = {}
    dupes = 0
    for line in path.read_text().splitlines():
        m = ROW_RE.match(line)
        if not m:
            continue
        problem, result, time_str = m.group(1), m.group(2), m.group(3)
        new_entry = (result, parse_time(time_str))
        prev = out.get(problem)
        if prev is None:
            out[problem] = new_entry
        else:
            dupes += 1
            out[problem] = _better(prev, new_entry)
    if dupes:
        print(f"  warning: {path.name} has {dupes} duplicate problem-name rows; "
              f"collapsed via best-result-fastest-time policy. "
              f"(Fix at source: rerun run_benchmark.py with its default dedupe-by-hash.)",
              file=sys.stderr)
    return out


def fmt_time(secs: Optional[float]) -> str:
    if secs is None:
        return "—"
    if secs < 0.01:
        return f"{secs*1000:.1f}ms"
    if secs < 1:
        return f"{secs:.3f}s"
    if secs < 60:
        return f"{secs:.2f}s"
    return f"{secs:.1f}s"


def fmt_tau(tau: str) -> str:
    """Pretty-print a τ value for display (`inf` stays as `inf`, not `Infinity`)."""
    return "inf" if tau.lower() in ("inf", "infinity") else tau


def family_of(problem_name: str) -> str:
    """
    Heuristic family bucket from the problem name.  Used only for the
    'best τ per family' table — purely cosmetic; matches the common
    benchmark naming patterns seen in GBD's main_2025 / anni_2022 etc.
    Falls back to '(other)' for names that don't match a known shape.
    """
    n = problem_name
    if n.startswith("Steiner-"):           return "Steiner"
    if n.startswith("php-") or n.startswith("PHP-"):           return "PHP"
    if "rphp" in n.lower():                return "rPHP"
    if "crypto" in n.lower() or n.startswith("ssAES"): return "crypto"
    if "prime" in n.lower():               return "prime-factor"
    if "mrpp" in n.lower():                return "mrpp"
    if n.startswith("frb"):                return "frb (random)"
    if n.startswith("WS_"):                return "WS-graph"
    if n.startswith("x9-") or n.startswith("x10-"):           return "x9/x10"
    if n[:1].isdigit() and "-" in n:       return "numeric-id"
    return "(other)"


# ---------------------------------------------------------------------------
# Sweep
# ---------------------------------------------------------------------------
def run_one_tau(
    index: Path, backend: str, timeout: int, parallel: int,
    preprocess: Optional[str], tau: str, out_dir: Path,
    extra_filter: Optional[str], limit: int,
    no_progress: bool,
) -> Path:
    """Run run_benchmark.py for one τ value.  Returns the path to its .md."""
    tau_tag = "inf" if tau.lower() in ("inf", "infinity") else tau.replace(".", "p")
    out_md = out_dir / f"sweep_{backend}_tau_{tau_tag}.md"
    # Idempotent: skip if we already have this file (resume support).
    if out_md.exists() and out_md.stat().st_size > 200:
        print(f"  ✓ τ={tau}: reusing existing {out_md.name}")
        return out_md

    # Use `--sat-arg=...` equals-form to defeat argparse's tendency to
    # treat the following `--eff-tau` as a flag to itself.  Then use
    # sat's own `--eff-tau=...` equals-form so the literal arrives as
    # one argv element on sat's side too.  This way the whole tau
    # value travels as one indivisible token from here to sat.
    cmd = [
        sys.executable, str(RUN_BENCH),
        "--index", str(index),
        "-b", backend,
        "-t", str(timeout),
        "-j", str(parallel),
        "-o", str(out_md),
        f"--sat-arg=--eff-tau={tau}",
    ]
    if preprocess:
        cmd.append(preprocess)
    if extra_filter:
        cmd.extend(["--filter", extra_filter])
    if limit > 0:
        cmd.extend(["--limit", str(limit)])
    if no_progress:
        cmd.append("--no-progress")

    print(f"  → τ={tau}: running {' '.join(cmd[-6:])}")
    rc = subprocess.run(cmd).returncode
    if rc != 0:
        print(f"    ! run_benchmark exited rc={rc} (MISMATCH or error); "
              f"sweep continues so partial data is captured", file=sys.stderr)
    return out_md


def emit_summary(
    sweep_dir: Path, tau_results: List[Tuple[str, Dict[str, Tuple[str, Optional[float]]]]],
    backend: str, timeout: int, index: Path,
) -> Path:
    """Write the sweep_summary.md given parsed tau→results."""
    summary_path = sweep_dir / "sweep_summary.md"

    # Universe of problems = union across all τs.
    all_problems = set()
    for _, results in tau_results:
        all_problems.update(results.keys())
    problems = sorted(all_problems)
    taus = [t for t, _ in tau_results]

    # ── Per-τ totals ──
    lines: List[str] = []
    lines.append(f"# τ sweep on `{index.name}` (backend `{backend}`, timeout {timeout}s)")
    lines.append("")
    lines.append("## Per-τ totals")
    lines.append("")
    lines.append("| τ | solved | timeout | mismatch | unknown | total CPU (solved) |")
    lines.append("|---|--------|---------|----------|---------|--------------------|")
    per_tau_summary: Dict[str, dict] = {}
    for tau, results in tau_results:
        solved = sum(1 for r, _ in results.values() if r in ("SAT", "UNSAT"))
        timed  = sum(1 for r, _ in results.values() if r == "TIMEOUT")
        miss   = sum(1 for r, _ in results.values() if r == "MISMATCH")
        unk    = sum(1 for r, _ in results.values() if r == "UNKNOWN")
        cpu    = sum(t for r, t in results.values()
                     if r in ("SAT", "UNSAT") and t is not None)
        per_tau_summary[tau] = {
            "solved": solved, "timeout": timed, "mismatch": miss,
            "unknown": unk, "cpu": cpu,
        }
        lines.append(
            f"| {fmt_tau(tau)} | {solved} | {timed} | {miss} | {unk} | "
            f"{cpu:.1f}s |"
        )
    lines.append("")

    # ── Win matrix (per-problem winning τ) ──
    # For each problem, find the fastest τ that solved it (SAT or UNSAT).
    winners: Dict[str, str] = {}      # problem → winning τ
    for prob in problems:
        best_tau, best_t = None, float("inf")
        for tau, results in tau_results:
            if prob not in results: continue
            r, t = results[prob]
            if r in ("SAT", "UNSAT") and t is not None and t < best_t:
                best_t, best_tau = t, tau
        if best_tau is not None:
            winners[prob] = best_tau

    # ── Recommended τ ──
    # Selection priorities, applied in order:
    #   1. Most unique problems SOLVED (coverage is paramount — if τ
    #      can solve one more instance, the extra CPU on it almost
    #      always pays for itself in evolution / fitness-eval loops).
    #   2. Most per-instance WINS (fastest solve among τs that did
    #      solve it — captures responsiveness on the shared subset).
    #   3. Lowest total CPU (cheapest at equal coverage + speed).
    # The first axis dominates: a τ that solves N+1 instances at any
    # CPU cost is always better than one that solves N.
    win_counts: Dict[str, int] = {t: 0 for t in taus}
    for w in winners.values():
        win_counts[w] = win_counts.get(w, 0) + 1
    sorted_taus = sorted(taus, key=lambda t: (
        -per_tau_summary[t]["solved"],     # most solved first
        -win_counts[t],                     # then most wins
        per_tau_summary[t]["cpu"],          # then lowest CPU
    ))
    recommended = sorted_taus[0] if sorted_taus else None
    if recommended is not None:
        rec_stats = per_tau_summary[recommended]
        lines.append("## Recommended τ")
        lines.append("")
        lines.append(
            f"**`--eff-tau {fmt_tau(recommended)}`** — solves "
            f"**{rec_stats['solved']}** unique instances "
            f"(wins {win_counts[recommended]} of them on fastest time; "
            f"{rec_stats['cpu']:.1f}s total CPU on solved). "
            f"Ranking criteria: most solved > most wins > lowest CPU.")
        lines.append("")
        lines.append("| τ | solved | wins | CPU on solved |")
        lines.append("|---|--------|------|---------------|")
        for t in sorted_taus:
            s = per_tau_summary[t]
            lines.append(f"| {fmt_tau(t)} | {s['solved']} | "
                         f"{win_counts[t]} | {s['cpu']:.1f}s |")
        lines.append("")

    # ── Best τ per family ──
    family_wins: Dict[str, Dict[str, int]] = {}
    family_problems: Dict[str, int] = {}
    for prob, tau in winners.items():
        fam = family_of(prob)
        family_problems[fam] = family_problems.get(fam, 0) + 1
        family_wins.setdefault(fam, {}).setdefault(tau, 0)
        family_wins[fam][tau] += 1
    # Also count instances with no winner (no τ solved them) per family
    family_unsolved: Dict[str, int] = {}
    for prob in problems:
        if prob not in winners:
            fam = family_of(prob)
            family_unsolved[fam] = family_unsolved.get(fam, 0) + 1
    if family_wins:
        lines.append("## Best τ per family")
        lines.append("")
        lines.append("| Family | solved | unsolved-by-any-τ | top τ (wins) |")
        lines.append("|--------|--------|-------------------|--------------|")
        for fam in sorted(set(list(family_wins.keys()) + list(family_unsolved.keys()))):
            wins = family_wins.get(fam, {})
            top = sorted(wins.items(), key=lambda kv: -kv[1])[:3]
            top_str = ", ".join(f"{fmt_tau(t)} ({n})" for t, n in top) or "—"
            lines.append(
                f"| {fam} | {family_problems.get(fam, 0)} | "
                f"{family_unsolved.get(fam, 0)} | {top_str} |"
            )
        lines.append("")

    # ── Per-problem detail table ──
    lines.append("## Per-problem results")
    lines.append("")
    header = "| Problem | " + " | ".join(fmt_tau(t) for t in taus) + " |"
    sep    = "|---------|" + "|".join(["----------"] * len(taus)) + "|"
    lines.append(header)
    lines.append(sep)
    for prob in problems:
        cells = []
        win = winners.get(prob)
        for tau, results in tau_results:
            entry = results.get(prob)
            if entry is None:
                cells.append("—")
                continue
            r, t = entry
            cell = f"{r} {fmt_time(t)}" if t is not None else r
            if tau == win:
                cell = f"**{cell}**"
            cells.append(cell)
        lines.append(f"| {prob} | " + " | ".join(cells) + " |")
    lines.append("")

    summary_path.write_text("\n".join(lines))
    return summary_path


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------
def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument("--index", required=True, type=Path,
                    help="curate.py JSONL output file.")
    ap.add_argument("-b", "--backend", default="eff",
                    help="sat backend (default: eff).  Must be an eff variant for "
                         "the τ to have any effect.")
    ap.add_argument("-t", "--timeout", type=int, default=60,
                    help="Per-instance wall-clock budget (default: 60s).")
    ap.add_argument("-j", "--parallel", type=int, default=4,
                    help="Parallel workers per τ run (default: 4).")
    pp = ap.add_mutually_exclusive_group()
    pp.add_argument("--preprocess", dest="preprocess", action="store_const",
                    const="--preprocess",
                    help="Force matrix preprocess on for every τ run.")
    pp.add_argument("--no-preprocess", dest="preprocess", action="store_const",
                    const="--no-preprocess",
                    help="Force matrix preprocess off.")
    ap.add_argument("--taus", default="0,0.5,1,2,inf",
                    help="Comma-separated τ values to sweep "
                         "(default: 0,0.5,1,2,inf).  `inf` = never reorder.")
    ap.add_argument("--filter", default=None,
                    help="Python expr to filter records (same as run_benchmark.py).")
    ap.add_argument("--limit", type=int, default=0,
                    help="Only process first N matching records (0 = no limit).")
    ap.add_argument("--out-dir", type=Path, default=None,
                    help="Where to write the sweep .md files.  Default: "
                         "doc/sweeps/<index-stem>_<backend>_<timeout>s/")
    ap.add_argument("--no-progress", action="store_true",
                    help="Disable run_benchmark's live TUI inside each sweep run.")
    ap.add_argument("--regenerate-summary-only", action="store_true",
                    help="Skip benchmark runs entirely.  Just re-parse every "
                         "existing sweep_<backend>_tau_*.md in the output dir "
                         "and re-emit sweep_summary.md.  Use this after fixing "
                         "the summary-generator (e.g. dedupe-by-name policy) "
                         "without paying the hours of CPU to re-measure.  "
                         "Tau list is inferred from the filenames present.")
    args = ap.parse_args()

    # ---- preflight ----
    if not args.regenerate_summary_only:
        if not args.index.exists():
            print(f"FATAL: index not found: {args.index}", file=sys.stderr)
            return 2
        if not RUN_BENCH.exists():
            print(f"FATAL: run_benchmark.py missing at {RUN_BENCH}", file=sys.stderr)
            return 2
        if "eff" not in args.backend:
            print(f"warning: backend '{args.backend}' has no eff layer; "
                  f"--eff-tau will have no effect", file=sys.stderr)

    # ---- output dir ----
    if args.out_dir:
        out_dir = args.out_dir
    else:
        out_dir = REPO_ROOT / "doc" / "sweeps" / (
            f"{args.index.stem}_{args.backend}_{args.timeout}s")
    if not args.regenerate_summary_only:
        out_dir.mkdir(parents=True, exist_ok=True)
    elif not out_dir.exists():
        print(f"FATAL: --regenerate-summary-only but {out_dir} doesn't exist", file=sys.stderr)
        return 2

    # ---- tau list ----
    if args.regenerate_summary_only:
        # Infer taus from existing .md filenames in the output dir.
        # Filename pattern: sweep_<backend>_tau_<TAU>.md, with `.` in
        # TAU encoded as `p` (e.g. `0p5` ← `0.5`).
        import re as _re
        prefix = f"sweep_{args.backend}_tau_"
        found = []
        for p in sorted(out_dir.glob(f"{prefix}*.md")):
            stem = p.stem
            if not stem.startswith(prefix): continue
            tau_str = stem[len(prefix):]
            # Decode the filename encoding back to a sweep token.
            tau_str = "inf" if tau_str == "inf" else tau_str.replace("p", ".")
            found.append((tau_str, p))
        if not found:
            print(f"FATAL: no sweep_{args.backend}_tau_*.md files in {out_dir}",
                  file=sys.stderr)
            return 2
        taus = [t for t, _ in found]
        print(f"regenerating from {len(taus)} existing .md files:")
        for t, p in found:
            print(f"  τ={t}: {p.name}")
        print()
    else:
        taus = [t.strip() for t in args.taus.split(",") if t.strip()]
        if not taus:
            print("FATAL: --taus must list at least one value", file=sys.stderr)
            return 2

    print(f"sweep dir: {out_dir}")
    print(f"backend:   {args.backend}")
    print(f"timeout:   {args.timeout}s")
    if not args.regenerate_summary_only:
        print(f"parallel:  {args.parallel}")
    print(f"taus:      {taus}")
    print()

    # ---- run sweeps (skipped if --regenerate-summary-only) ----
    tau_results: List[Tuple[str, Dict[str, Tuple[str, Optional[float]]]]] = []
    for tau in taus:
        if args.regenerate_summary_only:
            tau_tag = "inf" if tau.lower() in ("inf", "infinity") else tau.replace(".", "p")
            md = out_dir / f"sweep_{args.backend}_tau_{tau_tag}.md"
            if not md.exists():
                print(f"  warning: {md.name} missing — skipping τ={tau}", file=sys.stderr)
                continue
        else:
            md = run_one_tau(
                args.index, args.backend, args.timeout, args.parallel,
                args.preprocess, tau, out_dir, args.filter, args.limit,
                args.no_progress,
            )
        tau_results.append((tau, parse_md(md)))

    # ---- emit summary ----
    print()
    print("generating sweep summary…")
    summary = emit_summary(out_dir, tau_results, args.backend, args.timeout, args.index)
    print(f"  wrote {summary}")
    print()

    # ---- terminal recap ----
    print("Per-τ totals:")
    for tau, results in tau_results:
        solved = sum(1 for r, _ in results.values() if r in ("SAT", "UNSAT"))
        cpu    = sum(t for r, t in results.values()
                     if r in ("SAT", "UNSAT") and t is not None)
        total  = len(results)
        print(f"  τ={fmt_tau(tau):>5}  {solved:>3}/{total:<3} solved  "
              f"({cpu:>7.1f}s CPU on solved)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
