#!/usr/bin/env bash
#
# Install gbd-tools and download the GBD metadata + feature databases.
#
# After this runs, you can use `gbd` to query the SAT-competition
# benchmark database (https://benchmark-database.de).  Specifically:
#
#   gbd get "track=main_2025 and result=unsat" -r filename
#
# returns the list of UNSAT instances from the SAT competition 2025
# main track.
#
# Environment:
#   BENCH_DIR  Directory holding benchmark instances + GBD DBs.
#              Default: /Users/greg/projects/sat_benchmarks
#   GBD_DIR    Where to store the downloaded databases.
#              Default: $BENCH_DIR/.gbd
#
# Idempotent: re-running skips already-installed pieces.

set -euo pipefail

BENCH_DIR=${BENCH_DIR:-/Users/greg/projects/sat_benchmarks}
GBD_DIR=${GBD_DIR:-$BENCH_DIR/.gbd}

echo "BENCH_DIR=$BENCH_DIR"
echo "GBD_DIR=$GBD_DIR"
echo

# ─── Step 1: install gbd-tools via pip ──────────────────────────────────────
if python3 -c "import gbd_core" 2>/dev/null; then
    echo "✓ gbd-tools already installed (python3 -c 'import gbd_core' succeeds)"
else
    echo "→ installing gbd-tools via pip..."
    # --user puts it under ~/Library/Python/X.Y/bin (macOS) or ~/.local/bin.
    # Use --break-system-packages on newer Pythons that block --user pip.
    if ! pip3 install --user gbd-tools 2>/dev/null; then
        pip3 install --user --break-system-packages gbd-tools
    fi
    echo "  ↳ make sure the user-site bin is on PATH (gbd CLI):"
    python3 -c "import site; print('    ', site.getuserbase() + '/bin')"
fi
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
