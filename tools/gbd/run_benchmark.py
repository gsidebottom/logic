#!/usr/bin/env python3
"""
Run `sat` against every CNF in a curate.py JSONL index, in parallel,
with a live multi-worker progress display, and incrementally build a
Markdown report (summary table + cactus plot) updated as results arrive.

Per-instance workflow:
  1. Decompress the .xz to a per-worker tmpfile (xz -d -k -c).
  2. Run `sat -b BACKEND -t TIMEOUT --progress` < tmpfile.
     stderr goes through a pty so sat believes it's a TTY and --progress
     emits live frames; we read those, route the latest frame to that
     worker's row in the TUI bottom block.
  3. Parse the trailing `c SAT|UNSAT in Xms` / `c TIMEOUT after Ns`
     from the accumulated stderr.
  4. Cross-check against the JSONL record's known status (`status` field
     from curate.py).  Disagreement → MISMATCH row (recorded distinctly
     and flagged loudly in scrollback).
  5. Append a Markdown row to the output file (atomic O_APPEND so
     parallel workers' rows never interleave mid-line).
  6. Re-finalize the .md: regen the summary table + cactus plot PNG
     (throttled to once per `--finalize-interval` seconds so we don't
     thrash matplotlib on bursts of fast solves).
  7. Delete the per-worker tmpfile.

Output:
  doc/competition-benchmark_<index-stem>_<timeout>_<backend>[_pp|_nopp][_<n>].md
  (auto-numbered to avoid clobbering prior runs).

Terminal (when stderr is a TTY and --no-progress wasn't passed):
  Bottom block of N+1 lines:
    header line (done/solved/timeout/mismatch counts)
    N worker rows: `[i] problem-name  c CaDiCaL: 4.8K learned 0.1s`
  Scrollback above the block gets per-instance "done" lines + warnings.

Usage:
  tools/gbd/run_benchmark.py --index sat_benchmarks/easy.jsonl
  tools/gbd/run_benchmark.py --index easy.jsonl -b eff -t 30 -j 8
  tools/gbd/run_benchmark.py --index easy.jsonl --filter "r['status']=='SAT'"
  tools/gbd/run_benchmark.py --index easy.jsonl --no-progress  # CI mode
"""

import argparse
import json
import os
import pty
import re
import select
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from contextlib import contextmanager
from pathlib import Path
from typing import Dict, List, Optional, Tuple

# ---------------------------------------------------------------------------
# Paths
# ---------------------------------------------------------------------------
SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT  = SCRIPT_DIR.parent.parent
SAT_BIN    = REPO_ROOT / "target" / "release" / "sat"
COVER_VERIFY_BIN = REPO_ROOT / "target" / "release" / "sat-cover-verify"
# Backends that can emit a matrix cover certificate (--emit-cover); the
# UNSAT-proof gate (--verify-unsat-proof) re-runs one of these.
COVER_CAPABLE_BACKENDS = {"eff_cover", "cdcl", "smart"}
# VeriPB checker for the compact Cook PB proofs (--emit-cook-pbp).  The
# UNSAT-proof gate tries this *first* (it completely certifies detected
# PHP/RoundRobin/embedded-pigeonhole shapes, closing the cover cert's
# "None gap" on RR-scale structured UNSAT).  Located on PATH or ~/.cargo.
def _find_veripb() -> Optional[str]:
    import shutil
    hit = shutil.which("veripb")
    if hit:
        return hit
    cand = Path.home() / ".cargo" / "bin" / "veripb"
    return str(cand) if cand.exists() else None
VERIPB_BIN = _find_veripb()
PLOT_PY    = REPO_ROOT / "doc" / "competition-benchmarks-plot.py"
OUT_DIR    = REPO_ROOT / "doc"


# ---------------------------------------------------------------------------
# Helpers: filename munging + sat output parsing
# ---------------------------------------------------------------------------
GUID_RE = re.compile(r"^[0-9a-f]{32}-")

def strip_guid(name: str) -> str:
    """Drop a leading 32-hex SHA prefix from a filename basename."""
    return GUID_RE.sub("", name)


def short_name(rec: dict) -> str:
    """Display label: strip GUID + `.cnf.xz` / `.cnf` suffix."""
    n = strip_guid(rec.get("filename") or Path(rec.get("xz_path", "")).name)
    for suf in (".cnf.xz", ".cnf"):
        if n.endswith(suf):
            n = n[: -len(suf)]
            break
    return n


# `c SAT in 12.3ms`, `c UNSAT in 254.0ms`, `c TIMEOUT after 30s`
RESULT_RE  = re.compile(r"^c (SAT|UNSAT) in (.+)$")
TIMEOUT_RE = re.compile(r"^c TIMEOUT after (.+)$")
# `c INTERRUPTED after 1234.5ms` — sat caught SIGINT (Ctrl-C) and bailed
# mid-search.  Recognise it so an interrupted worker is reported as
# INTERRUPTED, not misclassified as an UNKNOWN *solver* verdict.
INTERRUPTED_RE = re.compile(r"^c INTERRUPTED after (.+)$")
SHORT_RE   = re.compile(r"^s (SATISFIABLE|UNSATISFIABLE)$")
# `c stats paths=6.319e180 log10_total_paths=180.8007 conflicts=31227
# restarts=115 elapsed_ms=2998.441` — emitted unconditionally by sat at
# the end of every search (incl. timeout / SIGINT).  All fields are
# `key=value` so order doesn't matter.
STATS_RE = re.compile(
    r"^c stats\s+"
    r"paths=([\-+0-9.eE]+)\s+"
    r"log10_total_paths=([\-+0-9.eEnif]+)\s+"
    r"conflicts=(\d+)\s+"
    r"restarts=(\d+)\s+"
    r"elapsed_ms=([\-+0-9.eE]+)\s*$"
)
# pb-cadical's CaDiCaL path has no matrix "paths"; it reports just the
# conflicts/restarts scraped from CaDiCaL's last report row.
PB_STATS_RE = re.compile(r"pb-cadical: stats conflicts=(\d+) restarts=(\d+)")

def fmt_time(token: str) -> str:
    """Convert '12.3ms' → '0.0123s'; pass-through 'Ns' / '<0.001s'."""
    t = token.strip()
    if t.endswith("ms"):
        try:
            s = float(t[:-2]) / 1000.0
        except ValueError:
            return t
        out = f"{s:.4f}".rstrip("0").rstrip(".")
        return f"{out}s"
    return t


# Strip CSI sequences (`\x1b[…<letter>`) and standalone `[?25l/h` modes
# so result-line scanning isn't confused by progress overstrike chars.
ANSI_RE = re.compile(r"\x1b\[[0-9;?]*[a-zA-Z]")


class SatStats:
    """Parsed per-instance stats from sat's `c stats ...` line.  All
    fields default to `None` when the line wasn't emitted (e.g. the
    formula was trivially solved by the preprocessor before search
    started — sat returns immediately without invoking the search
    engine, so there are no path counts to report)."""
    __slots__ = ("paths", "log10_total_paths", "conflicts", "restarts",
                 "elapsed_ms")

    def __init__(self):
        self.paths: Optional[float] = None
        self.log10_total_paths: Optional[float] = None
        self.conflicts: Optional[int] = None
        self.restarts: Optional[int] = None
        self.elapsed_ms: Optional[float] = None

    def is_set(self) -> bool:
        return self.elapsed_ms is not None

    def paths_fraction(self) -> Optional[float]:
        """Fraction of the formula's total path space classified by
        the search, in [0, 1].  Returns `None` if either field is
        unknown or if the total is too big to bring to a finite float
        (which happens above ~10^308 — at that point we still publish
        the raw counts but can't form a meaningful ratio)."""
        if self.paths is None or self.log10_total_paths is None:
            return None
        if self.log10_total_paths <= 0:
            # Formula with ≤ 1 total path — fraction is meaningless.
            return None
        if self.log10_total_paths < 308.0:
            total = 10.0 ** self.log10_total_paths
            if total <= 0:
                return None
            return max(0.0, min(1.0, self.paths / total))
        # Use log-space division: paths_frac = paths / 10^log_total
        # → log10(frac) = log10(paths) - log_total.  Then convert
        # back via 10^(...) IF the result is in finite range.
        if self.paths <= 0:
            return 0.0
        import math
        log_frac = math.log10(self.paths) - self.log10_total_paths
        if log_frac >= 0:
            return 1.0
        if log_frac < -308.0:
            return 0.0
        return 10.0 ** log_frac


def parse_sat_output(text: str) -> Tuple[str, str, SatStats]:
    """
    Scan combined stderr (with ANSI removed) for the *final* result line
    AND for the `c stats ...` line.  Mirrors competition-benchmarks.sh's
    awk parser.  Returns
    (RESULT, time_str, stats) where RESULT ∈ {SAT, UNSAT, TIMEOUT, UNKNOWN}.
    """
    clean = ANSI_RE.sub("", text)
    result, time_str, short = "UNKNOWN", "n/a", None
    stats = SatStats()
    # Split on \r + \n so progress overstrikes flatten into one line each.
    for raw in re.split(r"[\r\n]+", clean):
        ln = raw.strip()
        m = RESULT_RE.match(ln)
        if m:
            result, time_str = m.group(1), fmt_time(m.group(2))
            continue
        m = TIMEOUT_RE.match(ln)
        if m:
            result, time_str = "TIMEOUT", fmt_time(m.group(1))
            continue
        m = INTERRUPTED_RE.match(ln)
        if m:
            result, time_str = "INTERRUPTED", fmt_time(m.group(1))
            continue
        m = SHORT_RE.match(ln)
        if m:
            short = "UNSAT" if m.group(1) == "UNSATISFIABLE" else "SAT"
            continue
        m = STATS_RE.match(ln)
        if m:
            try:
                stats.paths              = float(m.group(1))
                stats.log10_total_paths  = float(m.group(2))
                stats.conflicts          = int(m.group(3))
                stats.restarts           = int(m.group(4))
                stats.elapsed_ms         = float(m.group(5))
            except ValueError:
                # Malformed — leave defaults.
                pass
            continue
        m = PB_STATS_RE.search(ln)
        if m:
            # pb-cadical (CaDiCaL path): conflicts/restarts only; paths stay
            # None so the matrix-path columns render as "—".
            stats.conflicts = int(m.group(1))
            stats.restarts  = int(m.group(2))
    if result == "UNKNOWN" and short is not None:
        return short, "<0.001s", stats
    if result == "UNKNOWN":
        # Defensive fallback: a live `--progress` frame ends with `\r`
        # and no newline, so a fast verdict can get glued onto it
        # (`c CaDiCaL: … 0.2sc UNSAT in 260ms`), defeating the
        # line-anchored matches above.  `sat` now emits a separating
        # newline, but search the whole cleaned text too so we stay
        # correct against older binaries / any other glue.  Only runs
        # when nothing matched, so it can't override a real verdict.
        m = re.search(r"c (SAT|UNSAT) in (\S+)", clean)
        if m:
            return m.group(1), fmt_time(m.group(2)), stats
        m = re.search(r"c (TIMEOUT|INTERRUPTED) after (\S+)", clean)
        if m:
            return m.group(1), fmt_time(m.group(2)), stats
    return result, time_str, stats


# ---------------------------------------------------------------------------
# SAT-witness verification — re-check the `v <model> 0` assignment the
# solver emitted against the actual CNF clauses.  Catches a *bogus
# satisfying assignment paired with a correct SAT verdict* — a
# soundness failure that the verdict-vs-ground-truth cross-check
# misses (the verdict agrees; only the witness is wrong).  Used by the
# OpenEvolve evaluator as a second line of defense alongside the
# Rust-side `evolve_guard` contract enforcement.
# ---------------------------------------------------------------------------
def parse_dimacs_clauses(cnf_path: Path) -> List[List[int]]:
    """Parse a DIMACS CNF into a list of clauses (each a list of
    signed ints).  Robust to clauses spanning multiple lines: tokens
    are accumulated across the whole file and split on `0`
    terminators, not on newlines."""
    toks: List[int] = []
    with cnf_path.open() as f:
        for line in f:
            line = line.strip()
            if not line or line[0] in "pc%":
                continue
            for x in line.split():
                try:
                    toks.append(int(x))
                except ValueError:
                    pass
    clauses: List[List[int]] = []
    cur: List[int] = []
    for t in toks:
        if t == 0:
            if cur:
                clauses.append(cur)
            cur = []
        else:
            cur.append(t)
    if cur:                       # tolerate a missing trailing 0
        clauses.append(cur)
    return clauses


def parse_v_line(stdout_text: str) -> Dict[int, bool]:
    """Parse the solver's `v <lit> <lit> ... 0` model line(s) from
    stdout into {var: bool}.  Handles a model split across several
    `v` lines (standard DIMACS); `0` terminates."""
    asg: Dict[int, bool] = {}
    for line in stdout_text.splitlines():
        line = line.strip()
        if not line.startswith("v"):
            continue
        for tok in line[1:].split():
            try:
                lit = int(tok)
            except ValueError:
                continue
            if lit == 0:
                continue
            asg[abs(lit)] = (lit > 0)
    return asg


def verify_sat_witness(cnf_path: Path, stdout_text: str) -> Tuple[bool, str]:
    """Return (ok, reason).  ok=True iff the `v`-line model satisfies
    every clause of `cnf_path`.  A variable absent from the model is
    treated as free → a clause is satisfied if ANY literal is
    satisfied OR references an unassigned variable in the polarity
    that could satisfy it (we treat unassigned as 'could be either',
    i.e. don't fail solely on a missing var — solvers legitimately
    omit don't-care variables)."""
    asg = parse_v_line(stdout_text)
    if not asg:
        return False, "no 'v' model line found on stdout"
    clauses = parse_dimacs_clauses(cnf_path)
    for ci, clause in enumerate(clauses):
        satisfied = False
        has_free = False
        for lit in clause:
            v = abs(lit)
            want = lit > 0
            val = asg.get(v)
            if val is None:
                has_free = True          # don't-care var → clause could be sat
            elif val == want:
                satisfied = True
                break
        if not satisfied and not has_free:
            return False, (f"clause #{ci} {clause} unsatisfied by model "
                           f"(all {len(clause)} literals assigned false)")
    return True, "ok"


def cadical_oracle(cnf_path: Path, timeout_s: int) -> Tuple[str, Optional[bool]]:
    """Independent verdict oracle: run sat's CaDiCaL backend on the CNF.
    Returns (verdict, model_ok) where verdict ∈ {"SAT","UNSAT","UNKNOWN"}
    and model_ok is True/False (the SAT `v`-line re-checked against the
    CNF) or None (not SAT / not checked).  CaDiCaL is a complete solver,
    so it decides instances the matrix cover can't certify."""
    try:
        with cnf_path.open("rb") as cnf_in:
            p = subprocess.run(
                [str(SAT_BIN), "-b", "cadical", "-t", str(timeout_s)],
                stdin=cnf_in, capture_output=True, text=True,
                timeout=timeout_s + 30)
    except subprocess.TimeoutExpired:
        return "UNKNOWN", None
    if "c SAT in" in p.stderr:
        ok, _ = verify_sat_witness(cnf_path, p.stdout)
        return "SAT", ok
    if "c UNSAT in" in p.stderr:
        return "UNSAT", None
    return "UNKNOWN", None


def verify_unsat_cook_pbp(cnf_path: Path) -> Tuple[Optional[bool], str]:
    """Try to PROVE UNSAT via a compact Cook PB proof checked by VeriPB.

    Runs `sat --emit-cook-pbp <tmp>` (detects PHP / RoundRobin /
    embedded-pigeonhole shape on the RAW CNF and emits a polynomial-size
    PB proof), then `veripb <cnf> <tmp>`.  Outcomes:
      - (True,  reason): VeriPB VERIFIED UNSATISFIABLE → proven UNSAT.
      - (False, reason): VeriPB REJECTED the proof.  The emitter only ever
                         fires after an O(S*P^2) clique-completeness check,
                         so this should never happen; treat as a soundness
                         failure if it does.
      - (None,  reason): no shape detected, or VeriPB missing/timeout — NOT
                         a failure; the caller falls back to the cover cert.
    Unlike the cover certificate, this COMPLETELY certifies RR-scale
    structured UNSAT (PHP/RoundRobin/MVRoundRobin), closing the cover
    gate's historical "None gap" on exactly those instances."""
    if VERIPB_BIN is None:
        return None, "veripb not found"
    pbp = cnf_path.with_suffix(cnf_path.suffix + ".pbp")
    try:
        try:
            with cnf_path.open("rb") as cnf_in:
                p = subprocess.run(
                    [str(SAT_BIN), "-b", "eff", "--emit-cook-pbp", str(pbp)],
                    stdin=cnf_in, capture_output=True, text=True, timeout=120)
        except subprocess.TimeoutExpired:
            return None, "cook-pbp emit wall-timeout"
        if "no matching shape" in p.stderr or not pbp.exists():
            return None, "no cook-pbp shape detected"
        try:
            v = subprocess.run([VERIPB_BIN, str(cnf_path), str(pbp)],
                               capture_output=True, text=True, timeout=300)
        except subprocess.TimeoutExpired:
            return None, "veripb wall-timeout"
        if "VERIFIED UNSATISFIABLE" in v.stdout:
            return True, "cook-pbp veripb-verified"
        return False, "veripb rejected cook-pbp proof"
    finally:
        try:
            pbp.unlink()
        except OSError:
            pass


def verify_pb_proof(cnf_path: Path, proof_path: Path, timeout_s: int = 300,
                    on_progress=None) -> Tuple[Optional[bool], str, float]:
    """Verify an EMITTED VeriPB proof (e.g. pb-cadical's `--proof` output)
    directly against the CNF — unlike `verify_unsat_cover`, this checks the
    solver's OWN proof rather than re-deriving one.  This runs SEPARATELY
    from the solve, with its own wall `timeout_s`, and returns the elapsed
    verification time so it can be reported apart from the solve time.

    Returns (ok, reason, elapsed_s):
      - (True,  "ok",   t)  : VeriPB VERIFIED the proof.
      - (False, reason, t)  : VeriPB REJECTED it.
      - (None,  reason, t)  : veripb missing / no proof / timed out.

    When `on_progress` is given, VeriPB runs with --show-progress and its
    `Progress: X%` is relayed through the callback for the live display."""
    if VERIPB_BIN is None:
        return None, "veripb not found", 0.0
    if not proof_path.exists() or proof_path.stat().st_size == 0:
        return None, "no proof emitted", 0.0
    t0 = time.time()
    cmd = [VERIPB_BIN]
    if on_progress is not None:
        cmd.append("--show-progress")
    cmd += [str(cnf_path), str(proof_path)]
    # Popen (not subprocess.run) so we can relay progress live AND enforce
    # our own timeout independently of the solve's.
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True)
    state = {"verified": False}

    def _reader():
        last, tail = 0.0, ""
        try:
            for chunk in iter(lambda: proc.stdout.read(512), ""):
                tail = (tail + chunk)[-4096:]      # rolling tail for the verdict
                if "VERIFIED UNSATISFIABLE" in tail:
                    state["verified"] = True
                if on_progress is not None:
                    m = re.findall(r"Progress:\s*([\d.]+)%", chunk)
                    if m and time.time() - last >= 0.4:
                        last = time.time()
                        on_progress(f"verifying proof… {m[-1]}%")
        except Exception:
            pass

    th = threading.Thread(target=_reader, daemon=True)
    th.start()
    try:
        proc.wait(timeout=timeout_s)
    except subprocess.TimeoutExpired:
        proc.kill()
        try: proc.wait(timeout=5)
        except Exception: pass
        th.join(timeout=1)
        return None, f"veripb timeout ({timeout_s}s)", time.time() - t0
    th.join(timeout=2)
    elapsed = time.time() - t0
    if state["verified"]:
        return True, "ok", elapsed
    return False, "veripb rejected the emitted proof", elapsed


def verify_unsat_cover(cnf_path: Path, backend: str,
                       timeout_s: int) -> Tuple[Optional[bool], str]:
    """Try to PROVE an UNSAT verdict by re-deriving a matrix cover
    certificate and checking it; fall back to the CaDiCaL oracle when
    the cover is incomplete.

    First attempts the compact Cook PB proof (`verify_unsat_cook_pbp`):
    on a detected PHP/RoundRobin/embedded-pigeonhole shape it completely
    certifies UNSAT in milliseconds, closing the cover gate's None gap on
    RR-scale structured instances.  Only when no shape is detected does it
    fall through to the matrix cover certificate below.

    Re-runs `sat -b <backend> --no-preprocess --emit-cover <tmp>` on the
    CNF (a cover-capable backend re-solves and emits its cover), then
    `sat-cover-verify <cnf> <cover>`.  Outcomes:
      - (True,  "ok")    : verifier accepted a COMPLETE cover → proven UNSAT.
      - (False, reason)  : DEFINITIVE soundness failure — either the cover
                           re-run itself reached SAT, or (cover incomplete)
                           the CaDiCaL oracle found a VERIFIED SAT model.
                           The instance is satisfiable, so the UNSAT verdict
                           is wrong; the candidate is scored unsound (0),
                           which is worse than a timeout.
      - (None,  reason)  : no complete cover AND CaDiCaL agrees UNSAT (or is
                           inconclusive).  NOT a failure — the matrix cover
                           is provably incomplete for some genuinely-UNSAT
                           instances (e.g. 3-colouring), so an unprovable-
                           but-correct UNSAT scores as a solve (better than
                           a timeout).
    The None gap is now closed for PHP/RoundRobin/MVRoundRobin-style
    structured UNSAT by the Cook PB proof tried first below; other
    families (e.g. 3-colouring) can still legitimately return None."""
    # Preferred: compact Cook PB proof (complete on detected pigeonhole
    # shapes).  Definitive True/False short-circuits; None falls through.
    ck_ok, ck_reason = verify_unsat_cook_pbp(cnf_path)
    if ck_ok is not None:
        return ck_ok, ck_reason
    if not COVER_VERIFY_BIN.exists():
        return None, "sat-cover-verify binary missing"
    cover = cnf_path.with_suffix(cnf_path.suffix + ".cover")
    try:
        try:
            with cnf_path.open("rb") as cnf_in:
                p = subprocess.run(
                    [str(SAT_BIN), "-b", backend, "-t", str(timeout_s),
                     "--no-preprocess", "--emit-cover", str(cover)],
                    stdin=cnf_in, capture_output=True, text=True,
                    timeout=timeout_s + 30)
        except subprocess.TimeoutExpired:
            return None, "cover re-run wall-timeout"
        if "c SAT in" in p.stderr:
            # The cover re-run found a SATISFYING path — the metric run's
            # UNSAT verdict contradicts it.  Definitive soundness failure
            # (preprocess preserves sat/unsat, so a sound policy could
            # never flip).
            return False, "cover re-run found SAT — UNSAT verdict is wrong"
        if "c UNSAT in" not in p.stderr:
            # Neither verdict (timed out, or cover-emission overhead
            # pushed it past budget) → can't certify, but don't penalise.
            return None, "cover re-run reached no verdict (timeout/over budget)"
        try:
            v = subprocess.run([str(COVER_VERIFY_BIN), str(cnf_path), str(cover)],
                               capture_output=True, text=True,
                               timeout=timeout_s + 30)
        except subprocess.TimeoutExpired:
            # Verifier (CaDiCaL on the cover CSP) didn't finish in budget
            # → can't certify, but don't penalise.
            return None, "cover verify wall-timeout"
        if v.returncode == 0:
            return True, "ok"
        # Verifier rejected the cover.  An incomplete cover does NOT by
        # itself imply SAT (the matrix cover is just incomplete for some
        # UNSAT instances).  So ask the CaDiCaL oracle, which can decide:
        #   - CaDiCaL finds a VERIFIED SAT model → the instance is
        #     satisfiable → the UNSAT verdict is WRONG → fail (False).
        #   - CaDiCaL says UNSAT / is inconclusive → unprovable-but-
        #     correct UNSAT → not a failure (None).
        cov_reason = next((ln.strip() for ln in v.stdout.splitlines()
                           if "INVALID" in ln or "INCOMPLETE" in ln),
                          "cover incomplete")
        verdict, model_ok = cadical_oracle(cnf_path, timeout_s)
        if verdict == "SAT" and model_ok:
            return False, ("CaDiCaL found a verified SAT model — "
                           "UNSAT verdict is wrong")
        return None, (f"no complete cover ({cov_reason}); "
                      f"CaDiCaL={verdict.lower()}")
    finally:
        try: cover.unlink()
        except FileNotFoundError: pass


# ---------------------------------------------------------------------------
# Summary + plot regeneration (mirrors competition-benchmarks.sh)
# ---------------------------------------------------------------------------
# Match 7-column rows.  We include MISMATCH so the summary counts them
# distinctly; the plotter's regex (built separately) is permissive about
# extra columns and consumes the leading three (problem / result / time).
#
# Columns:
#   1. Problem name
#   2. Result (SAT/UNSAT/TIMEOUT/UNKNOWN/MISMATCH)
#   3. Time   (e.g. "0.0123s" or "got=SAT expected=UNSAT, …")
#   4. Paths  (cover-mult-weighted classified path count, e.g. "1.2e150")
#   5. Total  (formula's total path count as "10^X" or "—")
#   6. Conf   (CDCL conflicts learned, decimal int or "—")
#   7. Rst    (CDCL Luby restarts, decimal int or "—")
#
# Cells use "—" when the underlying stat is unavailable (preprocessor-
# resolved instances, non-CDCL backends, MISMATCH rows where we trust
# the verdict but not the stats line provenance, etc.).
ROW_RE = re.compile(
    r"^\|\s*([^|]+?)\s*"                                              # name
    r"\|\s*(SAT|UNSAT|TIMEOUT|UNKNOWN|MISMATCH)\s*"                   # result
    r"\|\s*([^|]+?)\s*"                                               # time
    r"\|\s*([^|]+?)\s*"                                               # paths
    r"\|\s*([^|]+?)\s*"                                               # total
    r"\|\s*([^|]+?)\s*"                                               # conflicts
    r"\|\s*([^|]+?)\s*"                                               # restarts
    r"\|\s*$"
)
HDR_LINE = "| Problem | Result | Time | Paths | Total | Conf | Rst |"
SEP_LINE = "|---------|--------|------|-------|-------|------|-----|"


def fmt_count(n: Optional[float]) -> str:
    """SI-prefix big-number formatter — same shape as sat's
    `format_count`.  Returns '—' for `None`.  Used for the
    per-instance `Paths` / `Conf` / `Rst` columns and the
    summary-table mean / range cells."""
    if n is None: return "—"
    a = abs(n)
    if a < 1e3:   return f"{n:.0f}"
    if a < 1e6:   return f"{n/1e3:.1f}K"
    if a < 1e9:   return f"{n/1e6:.1f}M"
    if a < 1e12:  return f"{n/1e9:.1f}G"
    if a < 1e15:  return f"{n/1e12:.1f}T"
    if a < 1e18:  return f"{n/1e15:.1f}P"
    return f"{n:.2e}"


def fmt_log10_count(log10_n: Optional[float]) -> str:
    """Format a log10-valued count.  < 10^9 → reconstruct via
    `fmt_count`; ≥ 10^9 → '10^X.Y' since the literal int is too
    big to print compactly."""
    if log10_n is None: return "—"
    if log10_n < 0 or log10_n != log10_n: return "0"  # NaN / negative-inf
    if log10_n < 9.0:
        return fmt_count(10.0 ** log10_n)
    return f"10^{log10_n:.1f}"


def fmt_pct(frac: Optional[float]) -> str:
    """0.42 → '42%'.  Returns '—' for `None`."""
    if frac is None: return "—"
    return f"{100.0 * frac:.1f}%"


def fmt_mean_range(values: List[float], formatter=fmt_count) -> str:
    """`mean (min-max)` cell.  Empty list → '—'."""
    if not values: return "—"
    mean = sum(values) / len(values)
    if len(values) == 1:
        return formatter(mean)
    return f"{formatter(mean)} ({formatter(min(values))}-{formatter(max(values))})"


def fmt_pct_range(fracs: List[float]) -> str:
    """Like `fmt_mean_range` but each value is a fraction in [0, 1]
    displayed as a percent."""
    if not fracs: return "—"
    mean = sum(fracs) / len(fracs)
    if len(fracs) == 1:
        return fmt_pct(mean)
    return f"{fmt_pct(mean)} ({fmt_pct(min(fracs))}-{fmt_pct(max(fracs))})"


def _parse_cell_count(cell: str) -> Optional[float]:
    """Inverse of `fmt_count` — parse a `1.2K` / `3.4M` / `5e10` cell
    back to a float.  Returns None for '—' / unparseable."""
    s = cell.strip()
    if not s or s == "—":
        return None
    mult = 1.0
    if s[-1] in "KMGTP":
        mult = {"K": 1e3, "M": 1e6, "G": 1e9, "T": 1e12, "P": 1e15}[s[-1]]
        s = s[:-1]
    try:
        return float(s) * mult
    except ValueError:
        return None


def _parse_cell_log10(cell: str) -> Optional[float]:
    """Inverse of `fmt_log10_count` — parse '10^180.8' / '1.2K' back
    to the log10 value.  Returns None for unparseable / '—'."""
    s = cell.strip()
    if not s or s == "—":
        return None
    if s.startswith("10^"):
        try:
            return float(s[3:])
        except ValueError:
            return None
    n = _parse_cell_count(s)
    if n is None or n <= 0:
        return None
    import math
    return math.log10(n)


def _parse_time_cell(cell: str) -> Optional[float]:
    """`'0.0123s'` → `0.0123`; `'got=… '` → `None`."""
    s = cell.strip()
    if "got=" in s or s == "n/a":
        return None
    if s.startswith("<"):
        s = s[1:]
    if s.endswith("s"):
        try:
            return float(s[:-1])
        except ValueError:
            return None
    return None


def build_summary(md_path: Path) -> str:
    """Walk the table rows and produce a multi-section summary:

      1. Verdict counts (legacy table — kept for backward compat
         with `sweep_eff_tau.py` and tooling that greps it).
      2. Per-group solver-effort stats (paths covered / conflicts /
         restarts, with mean + range and per-second rates).

    Empty groups (e.g. no TIMEOUTs in this run) are skipped.  The
    'Total' row aggregates every successfully-parsed row.
    """
    # Rows partitioned by result, each row → (paths, log10_total, conf,
    # rst, time_s).  Unparseable cells become None and skip per-stat.
    by_group: Dict[str, List[Tuple[Optional[float], Optional[float],
                                   Optional[int], Optional[int],
                                   Optional[float]]]] = {}
    counts: Dict[str, int] = {}
    total = 0
    for line in md_path.read_text().splitlines():
        m = ROW_RE.match(line)
        if not m:
            continue
        _name, result, t_cell, p_cell, tot_cell, c_cell, r_cell = m.groups()
        counts[result] = counts.get(result, 0) + 1
        total += 1
        paths = _parse_cell_count(p_cell)
        log10 = _parse_cell_log10(tot_cell)
        conf  = _parse_cell_count(c_cell)
        rst   = _parse_cell_count(r_cell)
        secs  = _parse_time_cell(t_cell)
        by_group.setdefault(result, []).append((paths, log10,
                                                int(conf) if conf is not None else None,
                                                int(rst) if rst is not None else None,
                                                secs))

    out: List[str] = ["## Summary", ""]

    # ── Section 1: verdict counts (legacy) ──
    out.extend(["| Result | Count | % |", "|--------|-------|---|"])
    for r in ("SAT", "UNSAT", "TIMEOUT", "UNKNOWN"):
        if r in counts:
            out.append(f"| {r} | {counts[r]} | {100.0 * counts[r] / total:.1f}% |")
    if "MISMATCH" in counts:
        out.append(f"| **MISMATCH** | {counts['MISMATCH']} | "
                   f"{100.0 * counts['MISMATCH'] / total:.1f}% |")
    if total:
        out.append(f"| **Total** | {total} | 100% |")
    out.append("")

    # ── Section 2: solver-effort stats per group ──
    out.extend([
        "### Solver effort (mean (min-max))",
        "",
        "| Group | N | Paths covered | Conflicts | Conf/s | Restarts | Rst/s |",
        "|-------|---|---------------|-----------|--------|----------|-------|",
    ])
    # Build groups: each explicit verdict (when non-empty), then Total.
    group_order = [g for g in ("SAT", "UNSAT", "TIMEOUT", "UNKNOWN", "MISMATCH")
                   if g in by_group]
    if total:
        group_order.append("Total")
    for g in group_order:
        rows = (sum((by_group.get(k, []) for k in by_group), [])
                if g == "Total" else by_group[g])
        n = len(rows)
        # Extract per-row stats, dropping `None` per-statistic so a row
        # missing only conflicts (e.g. non-CDCL backend) still counts
        # toward path-coverage statistics.
        fracs: List[float] = []
        confs: List[int]   = []
        rsts:  List[int]   = []
        conf_rates: List[float] = []
        rst_rates:  List[float] = []
        for (paths, log10, conf, rst, secs) in rows:
            stats = SatStats()
            stats.paths             = paths
            stats.log10_total_paths = log10
            f = stats.paths_fraction()
            if f is not None:
                fracs.append(f)
            if conf is not None:
                confs.append(conf)
                if secs and secs > 0:
                    conf_rates.append(conf / secs)
            if rst is not None:
                rsts.append(rst)
                if secs and secs > 0:
                    rst_rates.append(rst / secs)
        out.append(
            f"| {g} | {n} "
            f"| {fmt_pct_range(fracs)} "
            f"| {fmt_mean_range([float(c) for c in confs])} "
            f"| {fmt_mean_range(conf_rates)} "
            f"| {fmt_mean_range([float(r) for r in rsts])} "
            f"| {fmt_mean_range(rst_rates)} |"
        )

    return "\n".join(out)


def regenerate_plot(md_path: Path) -> bool:
    """Run competition-benchmarks-plot.py → <stem>.png.  Returns success."""
    if not PLOT_PY.exists():
        return False
    png_path = md_path.with_suffix(".png")
    try:
        subprocess.run(
            ["python3", str(PLOT_PY), str(md_path), "-o", str(png_path)],
            check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        )
        return True
    except Exception:
        return False


def finalize(md_path: Path) -> None:
    """
    Rewrite md_path with:  title → summary → plot → per-problem table.
    Idempotent: prior `## Summary` / `## Cactus plot` / `## Per-problem
    results` blocks in the title section get stripped before re-insertion.
    """
    lines = md_path.read_text().split("\n")
    hdr_idx = next((i for i, l in enumerate(lines) if l.startswith(HDR_LINE)), None)
    if hdr_idx is None:
        return  # no table yet (no rows appended)

    # Title = everything above the table header, with any prior summary
    # / plot / per-problem heading dropped.
    title: List[str] = []
    for line in lines[:hdr_idx]:
        if line.startswith(("## Summary", "## Cactus plot", "## Per-problem results")):
            break
        title.append(line)
    while title and title[-1] == "":
        title.pop()

    plot_ok = regenerate_plot(md_path)
    summary = build_summary(md_path)

    parts: List[str] = []
    parts.extend(title)
    parts.append("")
    parts.append(summary)
    parts.append("")
    if plot_ok:
        parts.append("## Cactus plot")
        parts.append("")
        parts.append(f"![cactus plot]({md_path.with_suffix('.png').name})")
        parts.append("")
    parts.append("## Per-problem results")
    parts.append("")
    parts.extend(lines[hdr_idx:])

    tmp = md_path.with_suffix(md_path.suffix + ".tmp")
    tmp.write_text("\n".join(parts))
    tmp.replace(md_path)


class MdWriter:
    """
    Single-locked owner of the output .md file.  All mutations
    (appends + finalize rewrites) go through one mutex so a rewrite can
    never overwrite a row that landed between read-modify-write.
    Also throttles finalize() to at most once per `interval` seconds
    (forced flush is always honoured).
    """
    def __init__(self, md_path: Path, interval: float = 2.0):
        self.md_path = md_path
        self.interval = interval
        self.last = 0.0
        self.lock = threading.Lock()

    def append_row(self, row: str) -> None:
        """Atomic row append + maybe-finalize in one critical section."""
        with self.lock:
            with self.md_path.open("a") as f:
                f.write(row)
            now = time.monotonic()
            if now - self.last >= self.interval:
                self.last = now
                finalize(self.md_path)

    def flush(self) -> None:
        """Force a finalize regardless of throttle."""
        with self.lock:
            self.last = time.monotonic()
            finalize(self.md_path)


# ---------------------------------------------------------------------------
# TUI: fixed bottom block, scrollback above
# ---------------------------------------------------------------------------
# Cursor invariant: after every render, cursor sits one line BELOW the
# last worker row.  All operations begin by moving up (N+1) and clearing
# to end-of-screen, then re-emitting the block (and optionally a log
# line above it).
COLOR_RED    = "\x1b[31m"
COLOR_GREEN  = "\x1b[32m"
COLOR_YELLOW = "\x1b[33m"
COLOR_ORANGE = "\x1b[38;5;208m"   # solve TIMEOUT (distinct from yellow proof-timeout)
COLOR_BOLD   = "\x1b[1m"
COLOR_RESET  = "\x1b[0m"
HIDE_CURSOR  = "\x1b[?25l"
SHOW_CURSOR  = "\x1b[?25h"

def colorize(s: str, color: str, enabled: bool) -> str:
    return f"{color}{s}{COLOR_RESET}" if enabled else s


class TUI:
    def __init__(self, n_workers: int, total: int, enabled: bool):
        self.n = n_workers
        self.total = total
        self.enabled = enabled and sys.stderr.isatty()
        self.lock = threading.Lock()
        self.worker_names: List[str] = [""] * n_workers
        # Two stacked rows per worker, mirroring sat's two-bar display:
        # path row holds the log-progress bar / banner / result line;
        # time row holds the wall-clock bar.  Either can be empty (e.g.
        # before the first frame, or when sat was invoked without a
        # timeout so no time bar is emitted).
        self.worker_path: List[str] = [""] * n_workers
        self.worker_time: List[str] = [""] * n_workers
        # Total bottom-block rows: 1 header + 2 per worker.
        self.block_rows = 1 + 2 * n_workers
        # Worker-index field width — wide enough for the largest [N]
        # we'll print so the bracket column lines up across all rows.
        # For -j 10 → indices 0..9 → 1 char; for -j 100 → 0..99 → 2.
        self.idx_width = max(1, len(str(max(1, n_workers - 1))))
        self.done = 0
        self.solved = 0
        self.timed_out = 0
        self.mismatch = 0
        self.unknown = 0
        self.started_at = time.monotonic()

    # ------ public API --------------------------------------------------
    def install(self) -> None:
        if self.enabled:
            with self.lock:
                self._emit_block()

    def uninstall(self) -> None:
        if self.enabled:
            sys.stderr.write(SHOW_CURSOR)
            sys.stderr.flush()

    def update_worker(self, idx: int, name: str, line: str) -> None:
        """
        Route a sat-progress frame to the worker's path or time row
        based on its content.  Banners (`c parsed ...`, `c backend ...`)
        and result lines (`c SAT in Xms`) don't match either bar
        marker — those land in the path row so they're visible.
        """
        with self.lock:
            self.worker_names[idx] = name
            if TIME_FRAME_RE.search(line):
                self.worker_time[idx] = line
            elif PATH_FRAME_RE.search(line):
                self.worker_path[idx] = line
            else:
                # Banner / result / unknown — put it in the path row
                # and clear any stale time-bar text from a previous
                # run on this slot.
                self.worker_path[idx] = line
                self.worker_time[idx] = ""
            self._redraw()

    def free_worker(self, idx: int) -> None:
        with self.lock:
            self.worker_names[idx] = ""
            self.worker_path[idx] = ""
            self.worker_time[idx] = ""
            self._redraw()

    def record(self, result: str, mismatch: bool) -> None:
        with self.lock:
            self.done += 1
            if mismatch:
                self.mismatch += 1
            elif result in ("SAT", "UNSAT"):
                self.solved += 1
            elif result == "TIMEOUT":
                self.timed_out += 1
            else:
                self.unknown += 1
            self._redraw()

    def log(self, msg: str, *, color: str = "") -> None:
        with self.lock:
            if self.enabled:
                self._clear_block()
                colored = colorize(msg, color, True) if color else msg
                sys.stderr.write(colored + "\n")
                self._emit_block()
            else:
                sys.stderr.write(msg + "\n")
                sys.stderr.flush()

    # ------ internals ---------------------------------------------------
    def _cols(self) -> int:
        try:
            return max(40, shutil.get_terminal_size().columns)
        except Exception:
            return 100

    def _header(self) -> str:
        elapsed = time.monotonic() - self.started_at
        mm, ss = divmod(int(elapsed), 60)
        hh, mm = divmod(mm, 60)
        time_s = f"{hh:02d}:{mm:02d}:{ss:02d}"
        # Coloured counts
        parts = [
            f"{COLOR_BOLD}{self.done}/{self.total}{COLOR_RESET} done",
            f"{COLOR_GREEN}{self.solved} solved{COLOR_RESET}",
            f"{COLOR_ORANGE}{self.timed_out} timeout{COLOR_RESET}",
        ]
        if self.mismatch:
            parts.append(f"{COLOR_RED}{self.mismatch} MISMATCH{COLOR_RESET}")
        if self.unknown:
            parts.append(f"{self.unknown} unknown")
        parts.append(f"({time_s})")
        return "  ".join(parts)

    # Fixed visual columns so progress bars line up across all
    # worker rows, regardless of name length.  Names longer than
    # NAME_WIDTH are truncated with an ellipsis; shorter names are
    # right-padded with spaces.  Combined with `idx_width` this
    # gives every row the same prefix length, so the `c [bar...]`
    # column starts at the same character position on every line.
    NAME_WIDTH = 20

    def _fmt_name(self, name: str) -> str:
        """Pad/truncate `name` to exactly NAME_WIDTH visible characters."""
        if len(name) <= self.NAME_WIDTH:
            return name.ljust(self.NAME_WIDTH)
        # Truncate + ellipsis.  The ellipsis is one character so the
        # truncated name still occupies exactly NAME_WIDTH columns.
        return name[: self.NAME_WIDTH - 1] + "…"

    def _row_prefix(self, i: int, with_name: bool, name: str = "") -> str:
        """
        Visual prefix shared by both rows of a worker.  Path-bar row
        (with_name=True) shows `[i] <name>`; time-bar row
        (with_name=False) blanks the entire bracket + name area so
        the time bar reads as a clear continuation of the path bar
        above it.  Both forms have identical total width, so the bar
        column lines up across all worker rows.
        Width = 2 (gutter) + 1 ('[') + idx_width + 2 ('] ')
              + NAME_WIDTH + 2 (gap before bar).
        """
        bracket_w = 1 + self.idx_width + 2  # "[N] "
        if with_name:
            idx_str = str(i).rjust(self.idx_width)
            head = f"[{idx_str}] "
            body = self._fmt_name(name)
        else:
            head = " " * bracket_w
            body = " " * self.NAME_WIDTH
        return "  " + head + body + "  "

    def _worker_rows(self, i: int) -> Tuple[str, str]:
        """
        Two stacked rows per worker, vertically aligned:
          row 1: `  [i] <name padded to 20>  <path-bar frame>`
          row 2: `  [i] <20 blanks>           <time-bar frame>`
        Bars start at the same column on every row regardless of
        which worker is showing what name.
        """
        name = self.worker_names[i]
        cols = self._cols()
        if not name:
            # Idle slot — keep the prefix width so the empty row
            # doesn't visually shift the others when a worker
            # finishes and a new one hasn't claimed the slot yet.
            return (self._row_prefix(i, with_name=True, name="(idle)"), "")
        prefix1 = self._row_prefix(i, with_name=True, name=name)
        prefix2 = self._row_prefix(i, with_name=False)

        path = self.worker_path[i]
        avail1 = max(5, cols - len(prefix1) - 1)
        if len(path) > avail1:
            path = path[: avail1 - 1] + "…"
        row1 = prefix1 + path

        tline = self.worker_time[i]
        avail2 = max(5, cols - len(prefix2) - 1)
        if len(tline) > avail2:
            tline = tline[: avail2 - 1] + "…"
        row2 = prefix2 + tline
        return (row1, row2)

    def _emit_block(self) -> None:
        out: List[str] = [HIDE_CURSOR]
        out.append(self._header() + "\n")
        for i in range(self.n):
            r1, r2 = self._worker_rows(i)
            out.append(r1 + "\n")
            out.append(r2 + "\n")
        out.append(SHOW_CURSOR)
        sys.stderr.write("".join(out))
        sys.stderr.flush()

    def _clear_block(self) -> None:
        """Cursor → header line, then clear-to-end-of-screen."""
        sys.stderr.write(f"\x1b[{self.block_rows}A\x1b[J")

    def _redraw(self) -> None:
        if not self.enabled:
            return
        self._clear_block()
        self._emit_block()


# ---------------------------------------------------------------------------
# Subprocess wrangling: pty for stderr, frame parser
# ---------------------------------------------------------------------------
# `sat --progress` emits frames separated by these byte sequences.
# Each frame is the text BETWEEN consecutive separators; we surface the
# latest non-empty stripped frame to the worker's TUI row.
#
# `\x1b[<N>A` (cursor-up) is critical: sat emits it between frames to
# reposition for the in-place overwrite of its two stacked bars.
# Without recognising it as a separator, the cursor-up bytes get
# concatenated onto the END of the previous frame's text (which is
# the time-bar line — sat doesn't terminate it with `\n` because the
# next frame's `\x1b[1A` does that job).  We'd then either emit the
# time-bar text with an embedded escape (which corrupts the TUI when
# printed) or drop it entirely.  Matching `\x1b[NA` for any N covers
# the 1-line case (just the path bar, `\x1b[0A` is a no-op anyway)
# and the 2-line case (`\x1b[1A`).
SEP_RE = re.compile(r"\x1b\[2K|\x1b\[\?25[lh]|\x1b\[\d*A|\r|\n")

# Recognise which of sat's two bars a frame belongs to.  Both start
# with `c [bar] ` followed by either "paths " (log-progress line) or
# "time " (wall-clock line).  Banner lines (`c parsed ...`,
# `c backend: ...`, `c preprocess: ...`) and the final result line
# (`c SAT in ...`) match neither — we route those to the path row so
# they're visible in scrollback before the bars take over.
PATH_FRAME_RE = re.compile(r"\bpaths\s")
TIME_FRAME_RE = re.compile(r"\btime\s")

# Track all live sat subprocesses so a Ctrl-C in main can SIGTERM them
# even if the worker thread is blocked on os.read.
_running_procs: List[subprocess.Popen] = []
_procs_lock = threading.Lock()
_shutdown = threading.Event()

@contextmanager
def _register_proc(proc: subprocess.Popen):
    with _procs_lock:
        _running_procs.append(proc)
    try:
        yield
    finally:
        with _procs_lock:
            try:
                _running_procs.remove(proc)
            except ValueError:
                pass


def _kill_all_running() -> None:
    with _procs_lock:
        for p in list(_running_procs):
            try:
                p.terminate()
            except Exception:
                pass


def run_sat_with_pty(
    cmd: List[str],
    cnf_path: Path,
    on_frame,
) -> Tuple[int, str, str]:
    """
    Spawn `sat` with stderr attached to a pty (so --progress activates),
    stdin from cnf_path.  Reads stderr in chunks, splits on ANSI/CR/LF
    separators, calls on_frame(text) for each non-empty frame.

    stdout (which carries `s SATISFIABLE` + the `v <model> 0` witness
    line) is captured to a temp FILE — not a pipe — so it can never
    deadlock against the pty read loop even when the model is large.

    Returns (exit_code, full_stderr_text, full_stdout_text).
    """
    master_fd, slave_fd = pty.openpty()
    stdout_tmp = tempfile.NamedTemporaryFile(
        prefix="sat-stdout-", suffix=".txt", delete=False)
    stdout_tmp_path = Path(stdout_tmp.name)
    try:
        with cnf_path.open("rb") as cnf_in:
            proc = subprocess.Popen(
                cmd,
                stdin=cnf_in,
                stdout=stdout_tmp,          # → file, never blocks
                stderr=slave_fd,
                close_fds=True,
                env={**os.environ, "TERM": os.environ.get("TERM", "xterm-256color")},
            )
            stdout_tmp.close()              # child holds its own fd now
            os.close(slave_fd)
            slave_fd = -1  # mark closed

            with _register_proc(proc):
                full = bytearray()
                pending = ""
                while True:
                    if _shutdown.is_set():
                        try: proc.terminate()
                        except Exception: pass
                        break
                    try:
                        r, _, _ = select.select([master_fd], [], [], 0.1)
                    except (OSError, ValueError):
                        break
                    if master_fd in r:
                        try:
                            chunk = os.read(master_fd, 4096)
                        except OSError:
                            # Slave closed (child exited) → done.
                            break
                        if not chunk:
                            break
                        full.extend(chunk)
                        # Decode the pending+new chunk; split on separators.
                        pending += chunk.decode("utf-8", "replace")
                        last_end = 0
                        for m in SEP_RE.finditer(pending):
                            frame = pending[last_end:m.start()].strip()
                            if frame:
                                on_frame(frame)
                            last_end = m.end()
                        pending = pending[last_end:]
                    if proc.poll() is not None:
                        # Drain any remaining bytes the kernel still has buffered.
                        try:
                            while True:
                                chunk = os.read(master_fd, 4096)
                                if not chunk:
                                    break
                                full.extend(chunk)
                                pending += chunk.decode("utf-8", "replace")
                        except OSError:
                            pass
                        # Emit any trailing partial frame
                        for m in SEP_RE.finditer(pending):
                            pass  # exhaust
                        if pending.strip():
                            on_frame(pending.strip())
                        break

            try:
                rc = proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                rc = proc.wait()
            try:
                stdout_text = stdout_tmp_path.read_text(errors="replace")
            except OSError:
                stdout_text = ""
            return rc, full.decode("utf-8", "replace"), stdout_text
    finally:
        try: os.close(master_fd)
        except Exception: pass
        if slave_fd >= 0:
            try: os.close(slave_fd)
            except Exception: pass
        try: stdout_tmp_path.unlink()
        except OSError: pass


# ---------------------------------------------------------------------------
# Per-instance worker
# ---------------------------------------------------------------------------
def solve_one(
    rec: dict,
    *,
    timeout_s: int,
    backend: str,
    preprocess_flag: Optional[str],
    extra_sat_args: List[str],
    worker_idx: int,
    md_writer: "MdWriter",
    tui: TUI,
    verify_witness: bool = False,
    verify_unsat_proof: bool = False,
    proof_dir: Optional[Path] = None,
    proof_timeout: int = 300,
) -> dict:
    """Decompress + solve + append row + re-finalize.  Returns result dict.

    When `verify_witness` is set, a SAT verdict's `v`-line model is
    re-checked against the CNF clauses (while the decompressed CNF
    still exists on disk); a bogus model is recorded as a soundness
    failure (MISMATCH-class) even though the verdict itself agreed."""
    xz = Path(rec["xz_path"])
    display = short_name(rec)
    known = (rec.get("status") or "").upper()
    if known not in ("SAT", "UNSAT"):
        known = ""  # ignore TIMEOUT/UNKNOWN/missing as a cross-check anchor

    if _shutdown.is_set():
        return {"hash": rec.get("hash"), "result": "INTERRUPTED"}

    tui.update_worker(worker_idx, display, "decompressing…")

    tmp_path: Optional[Path] = None
    result, time_str, stats = "UNKNOWN", "n/a", SatStats()
    witness_ok: Optional[bool] = None   # None = not checked
    witness_reason = ""
    unsat_proof_ok: Optional[bool] = None   # None = not checked
    unsat_proof_reason = ""
    pb_proof_ok: Optional[bool] = None       # pb-cadical emitted-proof check
    pb_proof_reason = ""
    pb_proof_prover: Optional[str] = None    # "cook" | "cadical" (which emitted it)
    pb_proof_time: Optional[float] = None    # VeriPB verification wall time (s)
    proof_path: Optional[Path] = None        # /tmp write target (deleted unless kept)
    proof_kept: Optional[Path] = None        # where a FAILING proof is kept, else None
    try:
        with tempfile.NamedTemporaryFile(suffix=".cnf", delete=False) as tmp:
            tmp_path = Path(tmp.name)
        with tmp_path.open("wb") as f_out:
            subprocess.run(["xz", "-d", "-k", "-c", str(xz)],
                           stdout=f_out, check=True)

        tui.update_worker(worker_idx, display, "starting sat…")

        cmd = [str(SAT_BIN), "-b", backend, "-t", str(timeout_s)]
        if preprocess_flag:
            cmd.append(preprocess_flag)
        if tui.enabled:
            cmd.append("--progress")
        cmd.extend(extra_sat_args)

        # pb-cadical: emit a per-instance VeriPB proof, verify it after an
        # UNSAT verdict, then DELETE it (CaDiCaL proofs run to hundreds of
        # MB).  Only proofs that FAIL to verify are kept (moved to proof_dir
        # below).  So we write to a temp file, not proof_dir itself.
        proof_stem = None
        if proof_dir is not None and backend in ("pb-cadical", "pb_cadical"):
            proof_stem = rec.get("hash") or re.sub(r"[^A-Za-z0-9._-]", "_", display)
            proof_path = Path(tempfile.gettempdir()) / f"pbproof-{proof_stem}.pbp"
            cmd.extend(["--proof", str(proof_path)])

        def on_frame(frame: str) -> None:
            # Only show "c …" status lines; ignore stray ANSI residue.
            if frame.startswith("c "):
                tui.update_worker(worker_idx, display, frame)

        rc, stderr_text, stdout_text = run_sat_with_pty(cmd, tmp_path, on_frame)
        result, time_str, stats = parse_sat_output(stderr_text)

        # Fast-solve pty race: a sub-millisecond solve (e.g. an XOR-GE
        # pre-pass deciding a parity formula) can exit and close the pty
        # before its `c SAT/UNSAT in` stderr line is drained — on macOS
        # the kernel drops buffered master bytes on slave close — so
        # parse returns UNKNOWN.  The `s SATISFIABLE/UNSATISFIABLE` line
        # is on STDOUT, captured to a file (never lost), so recover the
        # verdict from there.
        if result == "UNKNOWN" and stdout_text:
            if re.search(r"^s SATISFIABLE\b", stdout_text, re.M):
                result = "SAT"
            elif re.search(r"^s UNSATISFIABLE\b", stdout_text, re.M):
                result = "UNSAT"

        # A worker killed mid-solve — by Ctrl-C (SIGTERM from
        # _kill_all_running) or by the OS (e.g. SIGKILL on OOM) — may
        # print no verdict line at all, so parse returns UNKNOWN.  That
        # is interrupted/incomplete work, NOT a genuine "the solver
        # couldn't decide" result; label it INTERRUPTED so a Ctrl-C'd
        # run's report isn't dominated by misleading UNKNOWN rows.
        # (rc < 0 ⇒ the child died on signal -rc.)
        if result == "UNKNOWN" and (_shutdown.is_set()
                                    or (rc is not None and rc < 0)):
            result = "INTERRUPTED"

        # Witness check MUST happen here — the CNF is unlinked in
        # `finally` below.
        if verify_witness and result == "SAT" and tmp_path is not None:
            witness_ok, witness_reason = verify_sat_witness(tmp_path, stdout_text)
        # UNSAT-proof gate — also needs the CNF on disk.  Re-derive +
        # check a matrix cover certificate; an over-pruning policy that
        # wrongly reports UNSAT yields an incomplete/​failing cover and
        # is rejected (None = couldn't certify in budget → not penalised).
        if verify_unsat_proof and result == "UNSAT" and tmp_path is not None:
            unsat_proof_ok, unsat_proof_reason = verify_unsat_cover(
                tmp_path, backend, timeout_s)
        # pb-cadical: VeriPB-check the proof the solver just emitted.
        if (proof_path is not None and result == "UNSAT"
                and tmp_path is not None):
            tui.update_worker(worker_idx, display, "verifying proof…")
            # Live %-progress only for LARGE proofs: VeriPB's --show-progress
            # ~doubles verify time, so skip it on small/fast proofs (the
            # static message above already covers those); big proofs are the
            # long verifies where watching progress actually matters.
            _big = proof_path.stat().st_size > 20_000_000
            _on_prog = ((lambda m: tui.update_worker(worker_idx, display, m))
                        if tui.enabled and _big else None)
            pb_proof_ok, pb_proof_reason, pb_proof_time = verify_pb_proof(
                tmp_path, proof_path, timeout_s=proof_timeout, on_progress=_on_prog)
            # Which prover emitted it — a Cook-path proof failure is a real
            # soundness alarm (our detector/proof is wrong); a CaDiCaL-path
            # one is only a certification gap (CaDiCaL is a trusted oracle,
            # its verdict stands; VeriPB just couldn't check its proof).
            if "prover=cook" in stderr_text:
                pb_proof_prover = "cook"
            elif "prover=cadical" in stderr_text:
                pb_proof_prover = "cadical"
            # Keep ONLY proofs that FAIL to verify (move to proof_dir for
            # inspection); verified/unverifiable ones are deleted in `finally`
            # (they're far too large to retain).
            if pb_proof_ok is False and proof_path is not None:
                if proof_dir is not None:
                    dest = proof_dir / proof_path.name
                    try:
                        proof_path.replace(dest)
                        proof_kept = dest
                    except OSError:
                        proof_kept = proof_path   # move failed → keep in /tmp
                else:
                    proof_kept = proof_path
    finally:
        # Delete the temp proof unless it was kept (a verification failure).
        if proof_path is not None and proof_path != proof_kept:
            try: proof_path.unlink()
            except OSError: pass
        if tmp_path is not None:
            try: tmp_path.unlink()
            except FileNotFoundError: pass

    # The `evolve_guard` Rust feature hard-exits (code 101) on a
    # soundness-contract violation, printing a `c EVOLVE-GUARD ABORT`
    # marker on stderr.  Detect via EXIT CODE primarily (reliable from
    # proc.wait()) and the stderr marker as confirmation — the marker
    # alone is racy because the process dies right after writing it and
    # the pty buffer may not be drained in time.  Either signal →
    # treat as the strongest soundness failure, regardless of what
    # verdict (if any) leaked out: a candidate that trips a contract
    # can never be rewarded.
    guard_abort = (rc == 101) or ("EVOLVE-GUARD ABORT" in stderr_text)

    mismatch = bool(known) and result in ("SAT", "UNSAT") and result != known
    if guard_abort:
        md_result = "MISMATCH"
        md_time = "GUARD-ABORT: soundness-contract violation"
        mismatch = True
    elif witness_ok is False:
        # SAT verdict but the model doesn't satisfy the formula —
        # a soundness failure even if the verdict matched ground truth.
        md_result = "MISMATCH"
        md_time = f"WRONG-SAT-WITNESS: {witness_reason}, {time_str}"
        mismatch = True
    elif unsat_proof_ok is False:
        # UNSAT verdict whose cover certificate doesn't check out (an
        # uncovered/​satisfying path exists, or a re-run found SAT) —
        # the instance isn't actually UNSAT, so this is a soundness
        # failure even if the verdict matched ground truth.
        md_result = "MISMATCH"
        md_time = f"BAD-UNSAT-PROOF: {unsat_proof_reason}, {time_str}"
        mismatch = True
    elif pb_proof_ok is False and pb_proof_prover != "cadical":
        # Cook-path proof (the one WE generate) was rejected by VeriPB —
        # our detector/proof is wrong, so the verdict itself is suspect.
        # Soundness failure.
        md_result = "MISMATCH"
        md_time = f"BAD-PB-PROOF: {pb_proof_reason}, {time_str}"
        mismatch = True
    elif pb_proof_ok is False:
        # CaDiCaL-path proof VeriPB couldn't verify.  CaDiCaL is a trusted
        # reference solver (we use it as the cross-check oracle elsewhere),
        # so its UNSAT verdict stands — this is a certification GAP, not a
        # soundness failure.  Keep the verdict; mark the proof unverified.
        md_result = result
        md_time = f"{time_str} (CaDiCaL proof unverified)"
    elif pb_proof_ok is None and pb_proof_reason:
        # Verification was ATTEMPTED but couldn't conclude (VeriPB timed out
        # on a large proof, veripb missing, no proof emitted, …).  Surface
        # the reason rather than printing a bare ✓ with no proof mention.
        md_result = result
        md_time = f"{time_str} (proof unchecked: {pb_proof_reason})"
    elif mismatch:
        md_result = "MISMATCH"
        md_time = f"got={result} expected={known}, {time_str}"
    else:
        md_result = result
        md_time = time_str

    # Per-row stats columns — `—` for any field the stats line didn't
    # carry (trivial-preprocess solves / non-CDCL backends / parse
    # error).  Conflict / restart counts on backends without CDCL are
    # genuinely zero, but the stats line WAS emitted, so they show
    # as "0" rather than "—".
    paths_cell = fmt_count(stats.paths) if stats.paths is not None else "—"
    total_cell = fmt_log10_count(stats.log10_total_paths)
    conf_cell  = fmt_count(stats.conflicts) if stats.conflicts is not None else "—"
    rst_cell   = fmt_count(stats.restarts)  if stats.restarts  is not None else "—"

    row = (f"| {display} | {md_result} | {md_time} "
           f"| {paths_cell} | {total_cell} | {conf_cell} | {rst_cell} |\n")
    md_writer.append_row(row)

    tui.record(result, mismatch)
    tui.free_worker(worker_idx)

    if guard_abort:
        tui.log(f"  ✗ [{display}] GUARD-ABORT (contract violation)",
                color=COLOR_RED + COLOR_BOLD)
    elif witness_ok is False:
        tui.log(f"  ✗ [{display}] WRONG-SAT-WITNESS  ({witness_reason})",
                color=COLOR_RED + COLOR_BOLD)
    elif unsat_proof_ok is False:
        tui.log(f"  ✗ [{display}] BAD-UNSAT-PROOF  ({unsat_proof_reason})",
                color=COLOR_RED + COLOR_BOLD)
    elif pb_proof_ok is False and pb_proof_prover != "cadical":
        tui.log(f"  ✗ [{display}] BAD-PB-PROOF  ({pb_proof_reason})",
                color=COLOR_RED + COLOR_BOLD)
    elif pb_proof_ok is False:
        tui.log(f"  ⚠ [{display}] {result} {time_str}  [CaDiCaL proof unverified]",
                color=COLOR_YELLOW)
    elif pb_proof_ok is True:
        _pt = f" {pb_proof_time:.1f}s" if pb_proof_time is not None else ""
        tui.log(f"  ✓ [{display}] {result} {time_str}  [proof ✓{_pt}]",
                color=COLOR_GREEN)
    elif pb_proof_ok is None and pb_proof_reason:
        tui.log(f"  ⚠ [{display}] {result} {time_str}  [proof unchecked: {pb_proof_reason}]",
                color=COLOR_YELLOW)
    elif mismatch:
        tui.log(f"  ! [{display}] {result}  (expected {known})  {time_str}",
                color=COLOR_RED + COLOR_BOLD)
    elif result in ("SAT", "UNSAT"):
        tui.log(f"  ✓ [{display}] {result} {time_str}", color=COLOR_GREEN)
    elif result == "TIMEOUT":
        tui.log(f"  · [{display}] {result} {time_str}", color=COLOR_ORANGE)
    else:
        tui.log(f"  ? [{display}] {result} {time_str}")

    # Return dict carries the full per-instance record for the JSON
    # writer (in `main`).  Stat fields are `None` when sat didn't emit
    # them (trivially-preprocess-resolved instances, etc.).
    return {
        "hash":           rec.get("hash"),
        "name":           display,
        "result":         result,
        "expected":       known,
        "mismatch":       mismatch,
        "guard_abort":    guard_abort,
        "witness_ok":     witness_ok,      # None=not checked, True/False=checked
        "witness_reason": witness_reason or None,
        "unsat_proof_ok": unsat_proof_ok,  # None=not checked, True/False=checked
        "unsat_proof_reason": unsat_proof_reason or None,
        "pb_proof_ok":    pb_proof_ok,     # pb-cadical emitted-proof veripb check
        "pb_proof_reason": pb_proof_reason or None,
        "pb_proof_prover": pb_proof_prover,  # "cook" | "cadical"
        "pb_proof_time_s": pb_proof_time,    # VeriPB verify wall time (separate from solve)
        "pb_proof_path":  str(proof_kept) if proof_kept else None,  # only kept on failure
        "time_s":         _parse_time_cell(time_str),
        "time_str":       time_str,
        "paths":          stats.paths,
        "log10_total_paths": stats.log10_total_paths,
        "paths_fraction": stats.paths_fraction(),
        "conflicts":      stats.conflicts,
        "restarts":       stats.restarts,
        "elapsed_ms":     stats.elapsed_ms,
    }


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------
def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument("--index", required=True, type=Path,
                    help="Path to a curate.py JSONL output file.")
    ap.add_argument("-b", "--backend", default="cadical",
                    help="sat backend name (default: cadical).")
    ap.add_argument("-t", "--timeout", type=int, default=60,
                    help="Per-instance timeout in seconds (default: 60).")
    ap.add_argument("-j", "--parallel", type=int, default=4,
                    help="Parallel workers (default: 4).")
    pp = ap.add_mutually_exclusive_group()
    pp.add_argument("--preprocess", dest="preprocess",
                    action="store_const", const="--preprocess",
                    help="Force matrix preprocess on.")
    pp.add_argument("--no-preprocess", dest="preprocess",
                    action="store_const", const="--no-preprocess",
                    help="Force matrix preprocess off.")
    ap.add_argument("-o", "--output", type=Path, default=None,
                    help="Output .md path.  Default: <output-dir>/"
                         "competition-benchmark_<index-stem>_<timeout>_"
                         "<backend>[_pp|_nopp][_<n>].md (auto-numbered to "
                         "avoid clobbering prior runs).  Overrides --output-dir "
                         "entirely when set.")
    ap.add_argument("--output-dir", type=Path, default=OUT_DIR,
                    help=f"Directory that holds the auto-named output .md / "
                         f".json / .png when --output is not given.  Created "
                         f"if missing.  Default: {OUT_DIR}")
    ap.add_argument("--proof-dir", type=Path, default=None,
                    help="Where pb-cadical's FAILED VeriPB proofs are kept for "
                         "inspection.  Each proof is written to /tmp, verified, "
                         "then DELETED (they run to hundreds of MB) — only those "
                         "that fail to verify are moved here.  Default: the "
                         "output directory (next to the .md / .json).")
    ap.add_argument("--proof-timeout", type=int, default=None,
                    help="Wall-clock limit (s) for VeriPB proof verification, "
                         "applied SEPARATELY from the solve --timeout (the solve "
                         "time reported is CaDiCaL's only).  Default: same as "
                         "--timeout.")
    ap.add_argument("--limit", type=int, default=0,
                    help="Only process first N matching records (0 = no limit).")
    ap.add_argument("--filter", default=None,
                    help="Python expr filter on record dict `r`, e.g. "
                         "\"r['status']=='SAT' and r.get('nvars',0)<1000\".")
    ap.add_argument("--no-progress", action="store_true",
                    help="Disable live TUI; one-line completion logs only.")
    ap.add_argument("--no-dedupe", action="store_true",
                    help="Don't dedupe records by `hash`.  Default is to keep "
                         "the first occurrence per hash and warn about how many "
                         "duplicates were dropped — curate.py is append-only, "
                         "so multi-pass JSONL files commonly carry duplicates.")
    ap.add_argument("--finalize-interval", type=float, default=2.0,
                    help="Min seconds between full .md rewrites (summary + "
                         "plot regen).  Default: 2.0.")
    ap.add_argument("--sat-arg", action="append", default=[],
                    metavar="ARG", help="Extra arg passed verbatim to sat "
                                        "(repeatable).")
    ap.add_argument("--verify-sat-witness", action="store_true",
                    help="For every SAT verdict, re-check the solver's "
                         "`v`-line model against the CNF clauses.  A model "
                         "that doesn't satisfy the formula is recorded as a "
                         "MISMATCH (soundness failure) even if the verdict "
                         "matched the expected status.  Used by the "
                         "OpenEvolve evaluator to catch bogus witnesses.")
    ap.add_argument("--verify-unsat-proof", action="store_true",
                    help="For every UNSAT verdict, independently re-derive "
                         "and check a matrix cover certificate (re-runs the "
                         "backend with --no-preprocess --emit-cover, then "
                         "sat-cover-verify).  An UNSAT whose cover doesn't "
                         "check out (a satisfying path exists) is recorded as "
                         "a MISMATCH (soundness failure).  Requires a "
                         "cover-capable backend (eff_cover, cdcl, smart).  "
                         "Used by the OpenEvolve evaluator to gate the open "
                         "(potentially-unsound) evolve block.")
    args = ap.parse_args()

    # ---- preflight ----
    if not args.index.exists():
        print(f"FATAL: index file not found: {args.index}", file=sys.stderr)
        return 2
    if not SAT_BIN.exists():
        print(f"FATAL: sat binary missing: {SAT_BIN}\n"
              f"       Build with: cargo build --release --bin sat",
              file=sys.stderr)
        return 2
    if args.verify_unsat_proof:
        # The gate has two proof paths: the compact Cook PB proof (any
        # backend; needs VeriPB) tried first, then the matrix cover cert
        # (needs a cover-capable backend + sat-cover-verify) as fallback.
        # Require at least one to be usable.
        cook_ok = VERIPB_BIN is not None
        cover_ok = (args.backend in COVER_CAPABLE_BACKENDS
                    and COVER_VERIFY_BIN.exists())
        if not cook_ok and not cover_ok:
            print(f"FATAL: --verify-unsat-proof needs either VeriPB (for the "
                  f"Cook PB proof path) or a cover-capable backend "
                  f"({', '.join(sorted(COVER_CAPABLE_BACKENDS))}) with "
                  f"sat-cover-verify; got backend {args.backend!r}, "
                  f"veripb={'found' if cook_ok else 'missing'}, "
                  f"sat-cover-verify={'found' if COVER_VERIFY_BIN.exists() else 'missing'}.",
                  file=sys.stderr)
            return 2
        if not cook_ok:
            print("c --verify-unsat-proof: VeriPB not found; Cook PB proof "
                  "path disabled, using cover certificate only.",
                  file=sys.stderr)
    if shutil.which("xz") is None:
        print("FATAL: xz not on PATH.", file=sys.stderr)
        return 2

    # ---- load + filter records ----
    records: List[dict] = []
    with args.index.open() as f:
        for line in f:
            line = line.strip()
            if line:
                records.append(json.loads(line))
    if args.filter:
        try:
            keep = []
            for r in records:
                if eval(args.filter, {"__builtins__": {}}, {"r": r}):
                    keep.append(r)
            records = keep
        except Exception as e:
            print(f"FATAL: --filter expression error: {e}", file=sys.stderr)
            return 2

    # Resolve `xz_path` against the index file's parent directory when
    # the path is relative — this lets self-contained benchmark dirs
    # (like `evo/`: index + .cnf.xz files next to each other) be
    # portable across machines and CI without rewriting absolute
    # paths.  Absolute paths and existing relative paths that already
    # resolve are left alone.  Mutates records in place so downstream
    # code (solve_one, JSON sidecar) sees the resolved path.
    index_dir = args.index.resolve().parent
    for r in records:
        p = Path(r.get("xz_path", ""))
        if not p.is_absolute() and not p.exists():
            cand = index_dir / p
            if cand.exists():
                r["xz_path"] = str(cand)

    # Skip records whose CNF isn't on disk (e.g. user moved BENCH_DIR).
    missing = [r for r in records if not Path(r.get("xz_path", "")).exists()]
    if missing:
        print(f"warning: {len(missing)} records have missing xz_path; skipping",
              file=sys.stderr)
        records = [r for r in records if Path(r.get("xz_path", "")).exists()]

    # Dedupe by `hash` field (or by xz_path as fallback) — curate.py is
    # append-only by default, so a JSONL built from multiple curate
    # passes ends up with the same instance recorded N times.  Without
    # deduping we'd solve each instance N times (wasted CPU) AND emit
    # N rows per instance in the output .md (which downstream tools
    # like sweep_eff_tau.py then mis-collate into wrong totals).
    #
    # Keep the FIRST occurrence per hash and warn loudly with counts
    # so the user knows whether to clean their index file.  Pass
    # `--no-dedupe` to disable (e.g. for genuinely parametrically
    # repeated runs with intentionally same hash).
    if not args.no_dedupe:
        seen = set()
        unique: List[dict] = []
        for r in records:
            key = r.get("hash") or r.get("xz_path") or json.dumps(r, sort_keys=True)
            if key in seen:
                continue
            seen.add(key)
            unique.append(r)
        if len(unique) < len(records):
            dupes = len(records) - len(unique)
            print(f"warning: deduped {dupes} duplicate records "
                  f"(kept {len(unique)} unique; --no-dedupe to disable)",
                  file=sys.stderr)
            records = unique

    if args.limit > 0:
        records = records[: args.limit]
    if not records:
        print("no records to process", file=sys.stderr)
        return 1

    # ---- pick output path ----
    pp_suffix = ""
    if args.preprocess == "--preprocess":
        pp_suffix = "_pp"
    elif args.preprocess == "--no-preprocess":
        pp_suffix = "_nopp"
    # `--output` (explicit .md path) wins outright.  Otherwise we
    # auto-name into `--output-dir` (defaults to the repo's `doc/`).
    out_dir = args.output_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    if args.output:
        out_md = args.output
        out_md.parent.mkdir(parents=True, exist_ok=True)
    else:
        base_name = (f"competition-benchmark_{args.index.stem}_"
                     f"{args.timeout}_{args.backend}{pp_suffix}.md")
        out_md = out_dir / base_name
        n = 1
        while out_md.exists():
            n += 1
            out_md = out_dir / f"{Path(base_name).stem}_{n}.md"

    # --proof-dir defaults to the markdown/JSON output directory.  Only the
    # pb-cadical backend emits proofs into it (one <hash>.pbp per UNSAT,
    # VeriPB-verified); other backends ignore it.
    if args.proof_dir is None:
        args.proof_dir = out_md.parent
    args.proof_dir.mkdir(parents=True, exist_ok=True)
    if args.proof_timeout is None:
        args.proof_timeout = args.timeout

    pp_tag = ""
    if args.preprocess == "--preprocess":
        pp_tag = ", preprocess=on"
    elif args.preprocess == "--no-preprocess":
        pp_tag = ", preprocess=off"

    header = (
        f"# Competition Benchmark Results "
        f"(index={args.index.name}, timeout={args.timeout}s, "
        f"backend={args.backend}, parallel={args.parallel}{pp_tag})\n"
        f"\n"
        f"{HDR_LINE}\n"
        f"{SEP_LINE}\n"
    )
    out_md.write_text(header)

    tui_on = (not args.no_progress) and sys.stderr.isatty()
    print(f"writing results to:   {out_md}")
    print(f"index:                {args.index}  ({len(records)} records)")
    print(f"timeout per problem:  {args.timeout}s")
    print(f"backend:              {args.backend}")
    # CaDiCaL ignores the matrix `--preprocess` pass (it runs its own
    # inprocessing), so don't imply a preprocess setting applies to it.
    pp_display = ("n/a (CaDiCaL runs its own)" if args.backend == "cadical"
                  else (args.preprocess or "<sat default>"))
    print(f"preprocess:           {pp_display}")
    print(f"parallel workers:     {args.parallel}")
    print(f"progress TUI:         {'on' if tui_on else 'off'}")
    if args.sat_arg:
        print(f"extra sat args:       {args.sat_arg}")

    tui = TUI(n_workers=args.parallel, total=len(records), enabled=not args.no_progress)
    md_writer = MdWriter(out_md, interval=args.finalize_interval)

    # Slot allocator so each in-flight worker gets a stable TUI row.
    free_slots: List[int] = list(range(args.parallel))
    slot_lock = threading.Lock()
    slot_cv = threading.Condition(slot_lock)

    def acquire_slot() -> int:
        with slot_cv:
            while not free_slots:
                slot_cv.wait()
            return free_slots.pop()

    def release_slot(idx: int) -> None:
        with slot_cv:
            free_slots.append(idx)
            slot_cv.notify()

    # ---- SIGINT: cleanly shut down workers ----
    def on_sigint(signum, frame):
        if not _shutdown.is_set():
            _shutdown.set()
            tui.log("interrupted; killing in-flight workers and finalizing…",
                    color=COLOR_YELLOW + COLOR_BOLD)
            _kill_all_running()

    signal.signal(signal.SIGINT, on_sigint)

    tui.install()

    def task(rec: dict) -> dict:
        if _shutdown.is_set():
            return {"hash": rec.get("hash"), "result": "INTERRUPTED"}
        idx = acquire_slot()
        try:
            return solve_one(
                rec,
                timeout_s=args.timeout,
                backend=args.backend,
                preprocess_flag=args.preprocess,
                extra_sat_args=list(args.sat_arg),
                worker_idx=idx,
                md_writer=md_writer,
                tui=tui,
                verify_witness=args.verify_sat_witness,
                verify_unsat_proof=args.verify_unsat_proof,
                proof_dir=args.proof_dir,
                proof_timeout=args.proof_timeout,
            )
        finally:
            release_slot(idx)

    # Collected per-instance result dicts (returned from `solve_one`).
    # Accumulated for the JSON sidecar written after the run completes.
    collected: List[dict] = []
    try:
        with ThreadPoolExecutor(max_workers=args.parallel) as ex:
            futures = [ex.submit(task, r) for r in records]
            for fut in as_completed(futures):
                try:
                    res = fut.result()
                    if isinstance(res, dict):
                        collected.append(res)
                except Exception as e:
                    tui.log(f"worker error: {e!r}", color=COLOR_RED)
    finally:
        tui.uninstall()

    md_writer.flush()

    # ── JSON sidecar ──
    #
    # Per-problem results + verdict-grouped summary statistics.  Same
    # data the Markdown report carries, in a form downstream tooling
    # (sweep_eff_tau.py, custom analysis scripts) can consume without
    # parsing Markdown tables.  Written next to the .md as
    # `<out_md.stem>.json`.
    json_out = out_md.with_suffix(".json")
    summary_json = _build_summary_json(collected)
    json_payload = {
        "metadata": {
            "index":      str(args.index),
            "backend":    args.backend,
            "timeout_s":  args.timeout,
            "parallel":   args.parallel,
            "preprocess": args.preprocess,
            "sat_args":   list(args.sat_arg),
            "md_path":    str(out_md),
        },
        "summary": summary_json,
        "results": collected,
    }
    try:
        json_out.write_text(json.dumps(json_payload, indent=2, default=_json_default))
    except OSError as e:
        print(f"warning: failed to write JSON sidecar {json_out}: {e}", file=sys.stderr)

    # Final summary to stdout
    print()
    print(f"done; results in {out_md}")
    print(f"        + JSON sidecar: {json_out}")
    print(f"  total:    {tui.done}/{tui.total}")
    print(f"  solved:   {tui.solved}")
    print(f"  timeout:  {tui.timed_out}")
    if tui.mismatch:
        print(f"  MISMATCH: {tui.mismatch}  ← SOUNDNESS BUG, investigate!")
    if tui.unknown:
        print(f"  unknown:  {tui.unknown}")
    return 0 if tui.mismatch == 0 else 1


def _json_default(obj):
    """json.dumps fallback for non-trivially-serializable values
    (NaN / inf survive `default=` so the f64 sentinels in
    `paths_fraction` always round-trip)."""
    try:
        return float(obj)
    except Exception:
        return str(obj)


def _build_summary_json(results: List[dict]) -> dict:
    """Build the structured summary that goes into the JSON sidecar.
    Mirrors `build_summary`'s per-group stats but in a form that's
    convenient to consume programmatically (no parsing of '5.2K' or
    'mean (min-max)' strings)."""
    by_group: Dict[str, List[dict]] = {}
    for r in results:
        by_group.setdefault(r.get("result", "UNKNOWN"), []).append(r)

    def _agg(rows: List[dict]) -> dict:
        fracs      = [r["paths_fraction"] for r in rows if r.get("paths_fraction") is not None]
        confs      = [r["conflicts"]      for r in rows if r.get("conflicts")      is not None]
        rsts       = [r["restarts"]       for r in rows if r.get("restarts")       is not None]
        secs       = [r["time_s"]         for r in rows if r.get("time_s")         is not None]
        conf_rates = [r["conflicts"] / r["time_s"]
                      for r in rows
                      if r.get("conflicts") is not None
                      and r.get("time_s") and r["time_s"] > 0]
        rst_rates  = [r["restarts"]  / r["time_s"]
                      for r in rows
                      if r.get("restarts") is not None
                      and r.get("time_s") and r["time_s"] > 0]
        def stat(xs: List[float]) -> Optional[dict]:
            if not xs: return None
            return {"n": len(xs),
                    "mean": sum(xs) / len(xs),
                    "min":  min(xs),
                    "max":  max(xs)}
        return {
            "count":            len(rows),
            "time_s":           stat(secs),
            "paths_fraction":   stat(fracs),
            "conflicts":        stat([float(c) for c in confs]),
            "conflicts_per_s":  stat(conf_rates),
            "restarts":         stat([float(r) for r in rsts]),
            "restarts_per_s":   stat(rst_rates),
        }

    out = {"by_verdict": {g: _agg(rs) for g, rs in by_group.items()}}
    if results:
        out["total"] = _agg(results)
    # Explicit soundness-failure tally — `by_verdict` is keyed by the
    # parsed verdict (SAT/UNSAT/TIMEOUT/UNKNOWN) so a MISMATCH never
    # shows up there.  Surface the real soundness counts at top level
    # so consumers (and humans reading the sidecar) can gate on them.
    out["soundness"] = {
        "mismatch":       sum(1 for r in results if r.get("mismatch")),
        "guard_abort":    sum(1 for r in results if r.get("guard_abort")),
        "bad_witness":    sum(1 for r in results if r.get("witness_ok") is False),
        "witness_checked":sum(1 for r in results if r.get("witness_ok") is not None),
        # bad_unsat_proof: UNSAT whose cover re-run found SAT (definitive
        # contradiction → soundness failure).  proven_unsat: UNSAT with a
        # complete verified cover.  unproven_unsat: correct UNSAT we just
        # couldn't certify (matrix cover incomplete) — still a solve.
        "bad_unsat_proof":sum(1 for r in results if r.get("unsat_proof_ok") is False),
        "proven_unsat":   sum(1 for r in results if r.get("unsat_proof_ok") is True),
        "unproven_unsat": sum(1 for r in results
                              if r.get("result") == "UNSAT"
                              and r.get("unsat_proof_ok") is None
                              and r.get("pb_proof_ok") is not True),
        # pb-cadical emitted-proof verification (the solver's OWN proof,
        # VeriPB-checked).  pb_proof_verified: UNSAT with a verified emitted
        # proof; pb_proof_failed: emitted proof VeriPB rejected (soundness
        # failure).
        "pb_proof_verified": sum(1 for r in results if r.get("pb_proof_ok") is True),
        # Cook-path proof rejected by VeriPB = real soundness failure:
        "pb_proof_failed":   sum(1 for r in results if r.get("pb_proof_ok") is False
                                 and r.get("pb_proof_prover") != "cadical"),
        # CaDiCaL-path proof VeriPB couldn't verify = certification gap, not a lie:
        "pb_proof_unverified": sum(1 for r in results if r.get("pb_proof_ok") is False
                                   and r.get("pb_proof_prover") == "cadical"),
    }
    return out


if __name__ == "__main__":
    sys.exit(main())
