#!/usr/bin/env bash
#
# Run `target/release/sat -b <backend>` against every *.cnf.xz file in
# $BENCH_DIR (default: /Users/greg/projects/sat_benchmarks), in
# parallel, and record the result + elapsed time as table rows in a
# fresh doc/competition-benchmark_<timeout>_<backend>[_<n>].md file.
#
# Per-problem workflow:
#   1. Decompress with `xz -d -k` — keeps the .xz on disk for safety,
#      so an interrupt can never leave us without the compressed
#      original.
#   2. Run `sat -b <backend> -t <timeout>` on the .cnf.
#   3. Parse the trailing "c SAT|UNSAT in Xms" or "c TIMEOUT after Ns"
#      line from sat's stdout.  Convert ms-based times to seconds with
#      decimal precision (e.g. `3726.0ms` → `3.726s`); pure-second
#      timeouts pass through unchanged (`8s`).
#   4. Strip the SHA-prefix from the basename (e.g.
#      `00d5...86cfb-st_890_86_9_572.normalised` →
#      `st_890_86_9_572.normalised`) for the displayed problem name.
#   5. Append one Markdown table row to the output file immediately
#      (atomic O_APPEND keeps parallel workers' rows un-interleaved).
#   6. Delete the decompressed .cnf — disk state returns to the
#      starting "only the .xz is present" layout.
#
# Output file: a fresh doc/competition-benchmark_<timeout>_<backend>.md
# is created each run.  If that path already exists,
# doc/competition-benchmark_<timeout>_<backend>_2.md is used (then _3,
# …) so no prior results are overwritten.
#
# Parallelism: workers are launched via `xargs -P` and re-invoke this
# same script in `--worker` mode for each individual problem.  Rows
# land in the output in completion order, not input order.
#
# When the run completes, the output .md is automatically finalized:
# a `## Summary` table (counts + percentages per Result) and a
# `## Cactus plot` image are inserted between the title and the
# per-problem table.  The plot is rendered to
# `<basename>.png` by `competition-benchmarks-plot.py` (skipped
# gracefully if Python or matplotlib is missing).
#
# Usage:
#   doc/competition-benchmarks.sh                    # 600s timeout, 10 parallel, cadical
#   doc/competition-benchmarks.sh -b eff             # use the eff backend
#   doc/competition-benchmarks.sh -b greedy_eff 300  # eff backend, 300s timeout
#   doc/competition-benchmarks.sh 300                # 300s timeout, 10 parallel
#   doc/competition-benchmarks.sh 300 4              # 300s timeout, 4 parallel
#   doc/competition-benchmarks.sh 300 10 5           # only first 5 problems
#   BENCH_DIR=/some/other/dir doc/...sh              # different bench dir
#
# Backend (-b / --backend): name passed to `sat -b NAME`.  Defaults to
# `cadical`.  Known matrix backends include `smart`, `cdcl`, `eff`,
# `greedy_cdcl`, `greedy_eff`, `basic_eff`.  Run `sat --help` for the
# authoritative list.  The chosen name is encoded in the output
# filename so runs of different backends don't overwrite each other.
#
#   doc/competition-benchmarks.sh --finalize FILE.md [FILE.md …]
#       Retroactively add the summary table + cactus plot to an
#       existing results file (e.g. one produced by an interrupted run
#       or an older version of the script).

set -euo pipefail

SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd "$SCRIPT_DIR/.." && pwd)
BENCH_DIR=${BENCH_DIR:-/Users/greg/projects/sat_benchmarks}
SAT_BIN="$REPO_ROOT/target/release/sat"

# Strip a 32-hex-char SHA prefix + dash from a basename, if present.
# Examples:
#   00d5a43a481477fa4d56a2ce152a6cfb-st_890_86_9_572.normalised
#       → st_890_86_9_572.normalised
#   no-guid-name (no prefix)
#       → no-guid-name (unchanged)
strip_guid() {
  echo "$1" | sed -E 's/^[0-9a-f]{32}-//'
}

# Parse sat's stdout (passed as a file path).  Echoes "Result|Time"
# for the table row, with time in seconds.
#
# Recognised forms in input:
#   c SAT in 12.3ms        → SAT     | 0.0123s
#   c UNSAT in 254.0ms     → UNSAT   | 0.254s
#   c TIMEOUT after 30s    → TIMEOUT | 30s
# Anything else → UNKNOWN | n/a.
#
# Pure awk — bash 3.2 (the system bash on macOS) has a regression
# where `BASH_REMATCH` array indices return empty strings even on
# successful `=~` matches, so we can't use the obvious bash-regex
# parse here.
parse_result() {
  awk '
    function fmt_time(t,    ms, s, fmt) {
      # ms-suffixed → convert to seconds, format up to 4 dp, then
      # strip trailing zeros and a trailing dot.  Result keeps real
      # precision but stays compact (e.g. `3.726s`, `0.254s`).
      if (t ~ /ms$/) {
        ms = substr(t, 1, length(t) - 2) + 0
        s = ms / 1000.0
        fmt = sprintf("%.4f", s)
        sub(/0+$/, "", fmt)
        sub(/\.$/, "", fmt)
        return fmt "s"
      }
      # Already in seconds (e.g. timeout "30s") — pass through.
      return t
    }
    /^c SAT in /        { result = "SAT";     time = fmt_time(substr($0, length("c SAT in ") + 1)); }
    /^c UNSAT in /      { result = "UNSAT";   time = fmt_time(substr($0, length("c UNSAT in ") + 1)); }
    /^c TIMEOUT after / { result = "TIMEOUT"; time = fmt_time(substr($0, length("c TIMEOUT after ") + 1)); }
    # Belt-and-suspenders fallback: if sat short-circuits with only a
    # `s UNSATISFIABLE` / `s SATISFIABLE` line (older builds did this
    # on the trivial-UNSAT / no-clauses fast paths), record the result
    # as "<0.001s" instead of UNKNOWN.  Only kicks in when no `c …`
    # timing line was seen, so it never overrides real timings.
    /^s UNSATISFIABLE/  { if (result == "") { result = "UNSAT"; time = "<0.001s"; } }
    /^s SATISFIABLE/    { if (result == "") { result = "SAT";   time = "<0.001s"; } }
    END {
      if (result == "") print "UNKNOWN|n/a";
      else              print result "|" time;
    }
  ' "$1"
}

# Build a Markdown summary block from the per-problem table in $1.
# Emits one section: a count + percentage per Result, plus a Total
# row.  Stable order (SAT, UNSAT, TIMEOUT, UNKNOWN) so the column
# layout doesn't shuffle between runs.
build_summary() {
  awk -F'|' '
    # Only count rows whose Result column is one of the known
    # values.  Filtering by value (rather than by line range) makes
    # the function safe to call on an already-finalized file —
    # neither the existing summary table nor the per-problem table
    # header gets miscounted.
    $0 ~ /^\|/ {
      gsub(/^ +| +$/, "", $3)
      if ($3 == "SAT" || $3 == "UNSAT" || $3 == "TIMEOUT" || $3 == "UNKNOWN") {
        counts[$3]++
        total++
      }
    }
    END {
      print "## Summary"
      print ""
      print "| Result | Count | % |"
      print "|--------|-------|---|"
      n = split("SAT UNSAT TIMEOUT UNKNOWN", order, " ")
      for (i = 1; i <= n; i++) {
        r = order[i]
        if (r in counts) {
          printf "| %s | %d | %.1f%% |\n", r, counts[r], 100.0 * counts[r] / total
        }
      }
      printf "| **Total** | %d | 100%% |\n", total
    }
  ' "$1"
}

# Add a `## Summary` table and (if Python+matplotlib is available) a
# `## Cactus plot` image to the output .md.  Rewrites the file with
# the layout:  title → summary → plot → per-problem table.
#
# Idempotent: previously-inserted `## Summary` / `## Cactus plot` /
# `## Per-problem results` headings are stripped before re-insertion,
# so this can be re-run safely on an already-finalized file.
finalize_output() {
  local md=$1
  local png="${md%.md}.png"
  local plotter="$SCRIPT_DIR/competition-benchmarks-plot.py"
  local title_block_end hdr_line tmp have_plot

  echo "finalizing $md ..."

  # Generate the plot.  Soft-fail: if matplotlib is missing or the
  # plot fails for any reason, skip the image link rather than block
  # the rewrite.
  have_plot=0
  if [ -x "$plotter" ] && command -v python3 >/dev/null; then
    if python3 "$plotter" "$md" -o "$png" >/dev/null 2>&1; then
      have_plot=1
      echo "  plot: $png"
    else
      echo "  plot: (failed; matplotlib installed?)"
    fi
  else
    echo "  plot: (skipped; python3 or plotter missing)"
  fi

  # Locate the per-problem table header.  Everything above is title;
  # everything from this line down (inclusive) is the existing detail
  # table.
  hdr_line=$(grep -n '^| Problem | Result | Time |' "$md" | head -1 | cut -d: -f1)
  if [ -z "$hdr_line" ]; then
    echo "  error: can't find per-problem table header in $md; skipping" >&2
    return 0
  fi
  title_block_end=$((hdr_line - 1))

  # Strip any prior `## Summary`, `## Cactus plot`, or
  # `## Per-problem results` blocks from the title section so
  # re-finalizing doesn't accumulate duplicates.  `sed`-deletes
  # everything from each heading up to (but not including) the next
  # blank-then-non-blank boundary; simpler: just drop every line
  # from the first `## Summary` heading on down within the title
  # block, then we re-append fresh sections below.
  tmp=$(mktemp)
  head -n "$title_block_end" "$md" \
    | awk '/^## (Summary|Cactus plot|Per-problem results)$/ { stop=1 } !stop' \
    > "$tmp"

  {
    cat "$tmp"
    build_summary "$md"
    echo
    if [ "$have_plot" = "1" ]; then
      echo "## Cactus plot"
      echo
      printf '![cactus plot](%s)\n' "$(basename "$png")"
      echo
    fi
    echo "## Per-problem results"
    echo
    tail -n +"$hdr_line" "$md"
  } > "$md.new" && mv "$md.new" "$md"
  rm -f "$tmp"
  echo "  rewrote: $md"
}

# ---------------------------------------------------------------------------
# Finalize mode.  `$0 --finalize FILE.md [FILE.md …]` — add the
# summary + plot to existing benchmark files without re-running.
# ---------------------------------------------------------------------------
if [ "${1:-}" = "--finalize" ]; then
  shift
  if [ $# -eq 0 ]; then
    echo "usage: $0 --finalize FILE.md [FILE.md …]" >&2
    exit 1
  fi
  for f in "$@"; do
    finalize_output "$f"
  done
  exit 0
fi

# ---------------------------------------------------------------------------
# Worker mode.  Invoked by xargs -P as `$0 --worker <base>`.  Runs
# the full per-problem pipeline for a single benchmark, then exits.
# Reads OUT_MD and TIMEOUT_SECS from env (exported by main mode below).
# ---------------------------------------------------------------------------
if [ "${1:-}" = "--worker" ]; then
  base=$2
  : "${OUT_MD:?OUT_MD must be exported}"
  : "${TIMEOUT_SECS:?TIMEOUT_SECS must be exported}"
  : "${BACKEND:?BACKEND must be exported}"

  cnf="$BENCH_DIR/$base.cnf"
  cleanup() {
    if [ -n "${cnf:-}" ] && [ -f "$cnf" ]; then
      rm -f "$cnf"
    fi
    # MUST return 0: the EXIT trap's final exit status becomes the
    # script's exit status, and a non-zero here causes xargs to count
    # this worker as failed (which in turn makes the main script
    # exit with `set -e`).
    return 0
  }
  trap cleanup EXIT INT TERM

  echo "[$base] decmp"
  xz -d -k -f "$BENCH_DIR/$base.cnf.xz"

  echo "[$base] run (timeout ${TIMEOUT_SECS}s)"
  tmp=$(mktemp)
  # `|| true` so a non-zero sat exit (124 on timeout, 130 on SIGINT
  # propagated through, etc.) doesn't kill the worker via `set -e`.
  "$SAT_BIN" -b "$BACKEND" -t "$TIMEOUT_SECS" < "$cnf" > "$tmp" 2>&1 || true

  IFS='|' read -r result time <<<"$(parse_result "$tmp")"
  display=$(strip_guid "$base")
  echo "[$base] result $result $time"

  rm -f "$tmp" "$cnf"

  # O_APPEND ensures the printf write is atomic with respect to other
  # workers also appending — each row lands as a single, complete
  # line.  Well under PIPE_BUF (typically 4 KB on macOS) so this
  # guarantee holds even with all 10 workers racing.
  printf '| %s | %s | %s |\n' "$display" "$result" "$time" >> "$OUT_MD"
  exit 0
fi

# ---------------------------------------------------------------------------
# Main mode.  Parse args, pick the output filename, build the
# to-process list, dispatch parallel workers via xargs.
# ---------------------------------------------------------------------------
# Parse leading flags.  -b/--backend NAME may appear before or
# interspersed with positional args; remaining args drop into the
# positional slots (timeout, parallel, limit).
BACKEND=cadical
positional=()
while [ $# -gt 0 ]; do
  case "$1" in
    -b|--backend)
      [ $# -ge 2 ] || { echo "missing value for $1" >&2; exit 1; }
      BACKEND=$2
      shift 2
      ;;
    --)
      shift
      while [ $# -gt 0 ]; do positional+=("$1"); shift; done
      break
      ;;
    -*) echo "unknown flag: $1" >&2; exit 1 ;;
    *)
      positional+=("$1")
      shift
      ;;
  esac
done
set -- "${positional[@]:-}"

TIMEOUT_SECS=${1:-600}
PARALLEL=${2:-10}
LIMIT=${3:-0}      # 0 = no limit

[ -x "$SAT_BIN" ]        || { echo "missing $SAT_BIN — run 'cargo build --release --bin sat'" >&2; exit 1; }
[ -d "$BENCH_DIR" ]      || { echo "missing benchmark dir $BENCH_DIR" >&2; exit 1; }
command -v xz >/dev/null || { echo "xz not on PATH" >&2; exit 1; }

# Pick an output filename that doesn't clobber a previous run.  The
# backend is in the name so that, e.g., a `cadical` run and an `eff`
# run at the same timeout produce distinct files.
OUT_MD="$REPO_ROOT/doc/competition-benchmark_${TIMEOUT_SECS}_${BACKEND}.md"
n=1
while [ -e "$OUT_MD" ]; do
  n=$((n + 1))
  OUT_MD="$REPO_ROOT/doc/competition-benchmark_${TIMEOUT_SECS}_${BACKEND}_${n}.md"
done

# Seed the output file with a header + table separator.  Workers
# append rows below this.  The header keeps the metadata
# (timeout/backend/parallel) machine-parseable for downstream tools
# like competition-benchmarks-plot.py.
cat > "$OUT_MD" <<EOF
# Competition Benchmark Results (timeout=${TIMEOUT_SECS}s, backend=${BACKEND}, parallel=${PARALLEL})

| Problem | Result | Time |
|---------|--------|------|
EOF

echo "writing results to: $OUT_MD"
echo "timeout per problem: ${TIMEOUT_SECS}s"
echo "backend:             ${BACKEND}"
echo "parallel workers:    $PARALLEL"

# Build the to-process list, honouring LIMIT if set.
to_process=()
for xz in "$BENCH_DIR"/*.cnf.xz; do
  base=$(basename "$xz" .cnf.xz)
  to_process+=("$base")
  if [ "$LIMIT" -gt 0 ] && [ "${#to_process[@]}" -ge "$LIMIT" ]; then
    break
  fi
done
echo "queued ${#to_process[@]} problems"

# Resolve our own absolute path so xargs can re-invoke us in
# worker mode regardless of the current working directory.
SELF="$SCRIPT_DIR/$(basename "$0")"
export BENCH_DIR SAT_BIN OUT_MD TIMEOUT_SECS BACKEND

# Dispatch.  -n 1: one basename per worker invocation.  -P N: up to
# N workers in flight at once.  xargs propagates SIGINT/SIGTERM to
# children, whose trap handlers clean up any stray .cnf files.
printf '%s\n' "${to_process[@]}" | xargs -n 1 -P "$PARALLEL" "$SELF" --worker

# All workers done; assemble the final report.
finalize_output "$OUT_MD"

echo "done; results in $OUT_MD"
