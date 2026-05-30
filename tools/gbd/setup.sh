#!/usr/bin/env bash
#
# Download the GBD metadata + feature databases used by the curation
# scripts in this directory (`curate.py`, `curate_balanced.py`,
# `verify_unsat.py`).
#
# After this runs, you can use `gbd` to query the SAT-competition
# benchmark database (https://benchmark-database.de).  Specifically:
#
#   gbd get "track=main_2025 and result=unsat" -r filename
#
# returns the list of UNSAT instances from the SAT competition 2025
# main track.
#
# Prerequisite: the `gbd` CLI itself.  Two options:
#   (a) Run the top-level `./setup.sh` from the repo root first — it
#       installs uv + creates ./.venv with `gbd-tools` (which provides
#       `gbd`) per pyproject.toml.  Then run this script with that
#       venv active (`source .venv/bin/activate` first, or use
#       `uv run tools/gbd/setup.sh`).
#   (b) `pip install --user gbd-tools` manually if you'd rather not
#       use the project venv.
#
# Environment:
#   BENCH_DIR  Directory holding benchmark instances + GBD DBs.
#              Default: /Users/greg/projects/sat_benchmarks
#   GBD_DIR    Where to store the downloaded databases.
#              Default: $BENCH_DIR/.gbd
#
# Idempotent: re-running skips already-downloaded DBs.

set -euo pipefail

BENCH_DIR=${BENCH_DIR:-/Users/greg/projects/sat_benchmarks}
GBD_DIR=${GBD_DIR:-$BENCH_DIR/.gbd}

echo "BENCH_DIR=$BENCH_DIR"
echo "GBD_DIR=$GBD_DIR"
echo

# ─── Step 1: locate the `gbd` CLI ──────────────────────────────────────────
# `gbd` is installed by the project's uv venv (top-level `./setup.sh`
# → `uv sync` → `gbd-tools` package).  It lands at `.venv/bin/gbd` on
# POSIX or `.venv\Scripts\gbd.exe` on Windows.
#
# Resolution order (first hit wins):
#   1. Already on PATH (user activated the venv or installed gbd globally)
#   2. The project's .venv (auto-find via THIS file's location)
#   3. Fail with a clear, actionable message
REPO_ROOT=$(cd "$(dirname "$0")/../.." && pwd)
if ! command -v gbd >/dev/null 2>&1; then
    if   [ -x "$REPO_ROOT/.venv/bin/gbd" ];        then export PATH="$REPO_ROOT/.venv/bin:$PATH"
    elif [ -x "$REPO_ROOT/.venv/Scripts/gbd.exe" ];then export PATH="$REPO_ROOT/.venv/Scripts:$PATH"
    fi
fi
if ! command -v gbd >/dev/null 2>&1; then
    echo "ERROR: 'gbd' not found.  The project's Python venv hasn't been" >&2
    echo "       created yet — bootstrap it first by running:" >&2
    echo >&2
    echo "           $REPO_ROOT/setup.sh" >&2
    echo >&2
    echo "       That installs uv (if missing), creates $REPO_ROOT/.venv," >&2
    echo "       and installs the gbd-tools package into it.  Then re-run" >&2
    echo "       this script — it'll auto-find gbd in the venv." >&2
    exit 1
fi
echo "✓ gbd: $(command -v gbd)"
echo

# ─── Step 2: ensure GBD_DIR exists ──────────────────────────────────────────
mkdir -p "$GBD_DIR"

# ─── Step 3: download metadata + base feature databases ─────────────────────
# meta.db provides: track, result, family, filename
# base.db provides: variables, clauses, instance-size features
for db in meta base; do
    out="$GBD_DIR/$db.db"
    if [ -s "$out" ]; then
        echo "✓ $db.db present ($(du -h "$out" | cut -f1))"
    else
        echo "→ downloading $db.db from benchmark-database.de..."
        wget --content-disposition -q --show-progress -O "$out.tmp" \
            "https://benchmark-database.de/getdatabase/$db"
        mv "$out.tmp" "$out"
        echo "  ↳ saved $out ($(du -h "$out" | cut -f1))"
    fi
done
echo

# ─── Step 4: print env-var hint ─────────────────────────────────────────────
echo "Done.  To use gbd from any shell, add to your ~/.zshrc or ~/.bashrc:"
echo
echo "    export GBD_DB=\"$GBD_DIR/meta.db:$GBD_DIR/base.db\""
echo
echo "Or use the wrapper script that sets it for you:"
echo
echo "    $(dirname "$0")/query.sh \"track=main_2025 and result=unsat\" -r filename"
