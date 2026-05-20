#!/usr/bin/env python3
"""
Cactus plot of competition-benchmark results.

Reads one or more `doc/competition-benchmark_<timeout>[_<n>].md` table
files and plots, per file, the cumulative number of problems solved
within t seconds — the standard SAT-competition "instances solved
within CPU time" curve.

A problem counts as "solved" if its Result is SAT or UNSAT;
TIMEOUT and UNKNOWN rows are excluded (they're the tail of the
distribution, not data points on the curve).

Usage:
    doc/competition-benchmarks-plot.py FILE [FILE ...] [-o OUT.png]
    doc/competition-benchmarks-plot.py doc/competition-benchmark_600.md
    doc/competition-benchmarks-plot.py doc/competition-benchmark_300.md \\
                           doc/competition-benchmark_600.md \\
                           -o doc/benchmark_compare.png

The default output is alongside the first input file, named
`<basename>.png` (so `competition-benchmark_600.md` → `.png`).
"""

import argparse
import os
import re
import sys
from pathlib import Path

import matplotlib
matplotlib.use("Agg")  # No display server needed on headless macOS sessions.
import matplotlib.pyplot as plt


# ---------------------------------------------------------------------------
# Time-string parsing.  The script emits four formats:
#   "0.4623s"  — decimal seconds (the common case)
#   "600s"     — pure-seconds (timeouts pass through unchanged)
#   "0s"       — trivial fast-path (0.0ms → 0)
#   "<0.001s"  — fallback for bare `s` lines from older sat builds
# Everything ends in "s"; strip it and parse the numeric prefix.
# ---------------------------------------------------------------------------
def parse_time(s):
    """Return seconds as float, or None if the field can't be parsed."""
    s = s.strip()
    if s == "n/a":
        return None
    if s.startswith("<"):
        # "<0.001s" → treat as the upper bound
        s = s[1:]
    if not s.endswith("s"):
        return None
    try:
        return float(s[:-1])
    except ValueError:
        return None


# Match rows like: `| problem-name | RESULT | 4.0317s |`
ROW_RE = re.compile(r"^\|\s*([^|]+?)\s*\|\s*(SAT|UNSAT|TIMEOUT|UNKNOWN)\s*\|\s*([^|]+?)\s*\|\s*$")


def load_table(path):
    """
    Read a benchmark Markdown file.  Returns (timeout_secs, backend,
    [(problem, result, secs)…]).  `timeout_secs` and `backend` are
    parsed from the file header if present, else None.
    """
    timeout = None
    backend = None
    rows = []
    timeout_re = re.compile(r"timeout=(\d+(?:\.\d+)?)s")
    backend_re = re.compile(r"backend=([A-Za-z0-9_.-]+)")
    with open(path) as f:
        for line in f:
            if timeout is None:
                m = timeout_re.search(line)
                if m:
                    timeout = float(m.group(1))
            if backend is None:
                m = backend_re.search(line)
                if m:
                    backend = m.group(1)
            m = ROW_RE.match(line)
            if not m:
                continue
            problem, result, time_str = m.group(1), m.group(2), m.group(3)
            secs = parse_time(time_str)
            if secs is None:
                # Skip rows we can't parse — they'd plot as zero and
                # distort the curve.
                continue
            rows.append((problem, result, secs))
    return timeout, backend, rows


def cactus_data(rows):
    """
    Build the cactus-plot series from a list of (problem, result,
    secs) rows.  Returns parallel lists (xs, ys) where xs is the
    cumulative time sorted ascending and ys is the running count of
    solved (SAT or UNSAT) problems.

    Standard cactus-plot convention: the x-axis is the per-problem
    solve time, sorted ascending across solved problems only.  ys[i]
    = i + 1.  Reading the chart: "the solver solved ys problems each
    in ≤ xs CPU-seconds."
    """
    solved = sorted(t for (_, r, t) in rows if r in ("SAT", "UNSAT"))
    if not solved:
        return [], []
    return solved, list(range(1, len(solved) + 1))


def label_for(path, timeout, backend):
    """Human-friendly legend label for a file."""
    if backend is not None and timeout is not None:
        return f"sat -b {backend} (timeout {int(timeout)}s)"
    if backend is not None:
        return f"sat -b {backend}"
    if timeout is not None:
        return f"sat (timeout {int(timeout)}s)"
    return Path(path).stem


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("files", nargs="+", help="Benchmark Markdown files to plot.")
    ap.add_argument("-o", "--out", default=None,
                    help="Output PNG path.  Default: alongside first input, "
                         "with .png suffix.")
    ap.add_argument("--title", default="Competition benchmark cactus plot",
                    help="Plot title.")
    ap.add_argument("--xlog", action="store_true",
                    help="Log-scale the x-axis (CPU time).  Often more "
                         "readable when results span many orders of "
                         "magnitude.")
    args = ap.parse_args()

    out = args.out or str(Path(args.files[0]).with_suffix(".png"))

    fig, ax = plt.subplots(figsize=(9, 6))
    total_problems = None

    for path in args.files:
        timeout, backend, rows = load_table(path)
        xs, ys = cactus_data(rows)
        if not xs:
            print(f"warning: no solved rows in {path}", file=sys.stderr)
            continue
        if total_problems is None:
            total_problems = len(rows)
        ax.plot(xs, ys, marker="o", markersize=3, linewidth=1.4,
                label=label_for(path, timeout, backend))
        solved = len(xs)
        timed_out = sum(1 for (_, r, _) in rows if r == "TIMEOUT")
        print(f"{path}: {solved} solved / {len(rows)} total "
              f"({timed_out} timeouts)")

    ax.set_xlabel("CPU time (seconds)")
    ax.set_ylabel("solved instances (cumulative)")
    ax.set_title(args.title)
    if args.xlog:
        ax.set_xscale("log")
    ax.grid(True, which="both", linestyle=":", alpha=0.5)
    ax.legend(loc="lower right")
    # Pad the y-axis a touch above the data so the curve doesn't kiss
    # the frame.
    if total_problems is not None:
        ax.set_ylim(0, total_problems * 1.02)
    fig.tight_layout()
    fig.savefig(out, dpi=150)
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
