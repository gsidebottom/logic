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
SHORT_RE   = re.compile(r"^s (SATISFIABLE|UNSATISFIABLE)$")

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

def parse_sat_output(text: str) -> Tuple[str, str]:
    """
    Scan combined stderr (with ANSI removed) for the *final* result line.
    Mirrors competition-benchmarks.sh's awk parser.  Returns
    (RESULT, time_str) where RESULT ∈ {SAT, UNSAT, TIMEOUT, UNKNOWN}.
    """
    clean = ANSI_RE.sub("", text)
    result, time_str, short = "UNKNOWN", "n/a", None
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
        m = SHORT_RE.match(ln)
        if m:
            short = "UNSAT" if m.group(1) == "UNSATISFIABLE" else "SAT"
    if result == "UNKNOWN" and short is not None:
        return short, "<0.001s"
    return result, time_str


# ---------------------------------------------------------------------------
# Summary + plot regeneration (mirrors competition-benchmarks.sh)
# ---------------------------------------------------------------------------
# Match 3-column rows.  We include MISMATCH so the summary counts them
# distinctly; the plotter's regex doesn't match MISMATCH (intentional —
# suspect results stay off the cactus curve).
ROW_RE = re.compile(
    r"^\|\s*([^|]+?)\s*\|\s*(SAT|UNSAT|TIMEOUT|UNKNOWN|MISMATCH)\s*\|\s*([^|]+?)\s*\|\s*$"
)
HDR_LINE = "| Problem | Result | Time |"

def build_summary(md_path: Path) -> str:
    """Count rows by Result column → Markdown summary table."""
    counts: Dict[str, int] = {}
    total = 0
    for line in md_path.read_text().splitlines():
        m = ROW_RE.match(line)
        if not m:
            continue
        r = m.group(2)
        counts[r] = counts.get(r, 0) + 1
        total += 1
    out = ["## Summary", "", "| Result | Count | % |", "|--------|-------|---|"]
    for r in ("SAT", "UNSAT", "TIMEOUT", "UNKNOWN"):
        if r in counts:
            out.append(f"| {r} | {counts[r]} | {100.0 * counts[r] / total:.1f}% |")
    if "MISMATCH" in counts:
        out.append(f"| **MISMATCH** | {counts['MISMATCH']} | "
                   f"{100.0 * counts['MISMATCH'] / total:.1f}% |")
    out.append(f"| **Total** | {total} | 100% |")
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
            f"{COLOR_YELLOW}{self.timed_out} timeout{COLOR_RESET}",
        ]
        if self.mismatch:
            parts.append(f"{COLOR_RED}{self.mismatch} MISMATCH{COLOR_RESET}")
        if self.unknown:
            parts.append(f"{self.unknown} unknown")
        parts.append(f"({time_s})")
        return "  ".join(parts)

    def _worker_rows(self, i: int) -> Tuple[str, str]:
        """
        Two stacked rows for worker `i`: the path-bar row (with the
        worker name on it) and the time-bar row (indented under it).
        Both truncated to fit the terminal width.
        """
        name = self.worker_names[i]
        cols = self._cols()
        if not name:
            # Idle slot: row 1 shows "(idle)", row 2 is empty.
            return (f"  [{i}] (idle)", "")
        # Row 1: name + path-bar line.
        prefix1 = f"  [{i}] {name}  "
        path = self.worker_path[i]
        avail1 = max(5, cols - len(prefix1) - 1)
        if len(path) > avail1:
            path = path[:avail1 - 1] + "…"
        row1 = prefix1 + path
        # Row 2: indented continuation, time-bar line only.
        prefix2 = " " * len(prefix1)
        tline = self.worker_time[i]
        avail2 = max(5, cols - len(prefix2) - 1)
        if len(tline) > avail2:
            tline = tline[:avail2 - 1] + "…"
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
) -> Tuple[int, str]:
    """
    Spawn `sat` with stderr attached to a pty (so --progress activates),
    stdout to /dev/null, stdin from cnf_path.  Reads stderr in chunks,
    splits on ANSI/CR/LF separators, calls on_frame(text) for each
    non-empty frame.  Returns (exit_code, full_stderr_text).
    """
    master_fd, slave_fd = pty.openpty()
    try:
        with cnf_path.open("rb") as cnf_in:
            proc = subprocess.Popen(
                cmd,
                stdin=cnf_in,
                stdout=subprocess.DEVNULL,
                stderr=slave_fd,
                close_fds=True,
                env={**os.environ, "TERM": os.environ.get("TERM", "xterm-256color")},
            )
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
            return rc, full.decode("utf-8", "replace")
    finally:
        try: os.close(master_fd)
        except Exception: pass
        if slave_fd >= 0:
            try: os.close(slave_fd)
            except Exception: pass


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
) -> dict:
    """Decompress + solve + append row + re-finalize.  Returns result dict."""
    xz = Path(rec["xz_path"])
    display = short_name(rec)
    known = (rec.get("status") or "").upper()
    if known not in ("SAT", "UNSAT"):
        known = ""  # ignore TIMEOUT/UNKNOWN/missing as a cross-check anchor

    if _shutdown.is_set():
        return {"hash": rec.get("hash"), "result": "INTERRUPTED"}

    tui.update_worker(worker_idx, display, "decompressing…")

    tmp_path: Optional[Path] = None
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

        def on_frame(frame: str) -> None:
            # Only show "c …" status lines; ignore stray ANSI residue.
            if frame.startswith("c "):
                tui.update_worker(worker_idx, display, frame)

        _, stderr_text = run_sat_with_pty(cmd, tmp_path, on_frame)
    finally:
        if tmp_path is not None:
            try: tmp_path.unlink()
            except FileNotFoundError: pass

    result, time_str = parse_sat_output(stderr_text)

    mismatch = bool(known) and result in ("SAT", "UNSAT") and result != known
    if mismatch:
        md_result = "MISMATCH"
        md_time = f"got={result} expected={known}, {time_str}"
    else:
        md_result = result
        md_time = time_str

    row = f"| {display} | {md_result} | {md_time} |\n"
    md_writer.append_row(row)

    tui.record(result, mismatch)
    tui.free_worker(worker_idx)

    if mismatch:
        tui.log(f"  ! [{display}] {result}  (expected {known})  {time_str}",
                color=COLOR_RED + COLOR_BOLD)
    elif result in ("SAT", "UNSAT"):
        tui.log(f"  ✓ [{display}] {result} {time_str}", color=COLOR_GREEN)
    elif result == "TIMEOUT":
        tui.log(f"  · [{display}] {result} {time_str}", color=COLOR_YELLOW)
    else:
        tui.log(f"  ? [{display}] {result} {time_str}")

    return {"hash": rec.get("hash"), "result": result, "time": time_str,
            "expected": known, "mismatch": mismatch}


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
                    help="Output .md path.  Default: doc/competition-benchmark_"
                         "<index-stem>_<timeout>_<backend>[_pp|_nopp][_<n>].md")
    ap.add_argument("--limit", type=int, default=0,
                    help="Only process first N matching records (0 = no limit).")
    ap.add_argument("--filter", default=None,
                    help="Python expr filter on record dict `r`, e.g. "
                         "\"r['status']=='SAT' and r.get('nvars',0)<1000\".")
    ap.add_argument("--no-progress", action="store_true",
                    help="Disable live TUI; one-line completion logs only.")
    ap.add_argument("--finalize-interval", type=float, default=2.0,
                    help="Min seconds between full .md rewrites (summary + "
                         "plot regen).  Default: 2.0.")
    ap.add_argument("--sat-arg", action="append", default=[],
                    metavar="ARG", help="Extra arg passed verbatim to sat "
                                        "(repeatable).")
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

    # Skip records whose CNF isn't on disk (e.g. user moved BENCH_DIR).
    missing = [r for r in records if not Path(r.get("xz_path", "")).exists()]
    if missing:
        print(f"warning: {len(missing)} records have missing xz_path; skipping",
              file=sys.stderr)
        records = [r for r in records if Path(r.get("xz_path", "")).exists()]

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
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    if args.output:
        out_md = args.output
        out_md.parent.mkdir(parents=True, exist_ok=True)
    else:
        base_name = (f"competition-benchmark_{args.index.stem}_"
                     f"{args.timeout}_{args.backend}{pp_suffix}.md")
        out_md = OUT_DIR / base_name
        n = 1
        while out_md.exists():
            n += 1
            out_md = OUT_DIR / f"{Path(base_name).stem}_{n}.md"

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
        f"|---------|--------|------|\n"
    )
    out_md.write_text(header)

    tui_on = (not args.no_progress) and sys.stderr.isatty()
    print(f"writing results to:   {out_md}")
    print(f"index:                {args.index}  ({len(records)} records)")
    print(f"timeout per problem:  {args.timeout}s")
    print(f"backend:              {args.backend}")
    print(f"preprocess:           {args.preprocess or '<sat default>'}")
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
            )
        finally:
            release_slot(idx)

    try:
        with ThreadPoolExecutor(max_workers=args.parallel) as ex:
            futures = [ex.submit(task, r) for r in records]
            for fut in as_completed(futures):
                try:
                    fut.result()
                except Exception as e:
                    tui.log(f"worker error: {e!r}", color=COLOR_RED)
    finally:
        tui.uninstall()

    md_writer.flush()

    # Final summary to stdout
    print()
    print(f"done; results in {out_md}")
    print(f"  total:    {tui.done}/{tui.total}")
    print(f"  solved:   {tui.solved}")
    print(f"  timeout:  {tui.timed_out}")
    if tui.mismatch:
        print(f"  MISMATCH: {tui.mismatch}  ← SOUNDNESS BUG, investigate!")
    if tui.unknown:
        print(f"  unknown:  {tui.unknown}")
    return 0 if tui.mismatch == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
