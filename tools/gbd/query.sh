#!/usr/bin/env bash
#
# Wrapper around `gbd get` that sets PATH and GBD_DB for you.
#
# Usage:
#   query.sh "<query>" [gbd-get-options...]
#
# Examples:
#   query.sh "track=main_2025 and result=unsat" -r filename
#   query.sh "track=main_2025 and result=sat and variables<1000" -r filename variables clauses
#   query.sh "family like crypto%" -r filename family
#
# See `gbd get --help` for the full option set and the LIPIcs paper for
# query syntax (https://doi.org/10.4230/LIPIcs.SAT.2024.18).

set -euo pipefail

BENCH_DIR=${BENCH_DIR:-/Users/greg/projects/sat_benchmarks}
GBD_DIR=${GBD_DIR:-$BENCH_DIR/.gbd}

# `gbd` is expected on PATH already — supplied by the uv-managed venv
# (created by the repo's top-level `setup.sh`).  Either source
# `.venv/bin/activate` once per shell, or invoke this script via
# `uv run`, and the binary will resolve.  As a convenience, if the
# user hasn't done either, fall back to looking in the project's
# .venv directly so `query.sh` Just Works without manual activation.
if ! command -v gbd >/dev/null 2>&1; then
    REPO_ROOT=$(cd "$(dirname "$0")/../.." && pwd)
    if [ -x "$REPO_ROOT/.venv/bin/gbd" ]; then
        export PATH="$REPO_ROOT/.venv/bin:$PATH"
    elif [ -x "$REPO_ROOT/.venv/Scripts/gbd.exe" ]; then
        export PATH="$REPO_ROOT/.venv/Scripts:$PATH"
    fi
fi
export GBD_DB="$GBD_DIR/meta.db:$GBD_DIR/base.db"

if [ $# -eq 0 ]; then
    cat <<'EOF' >&2
usage: query.sh "<query>" [gbd-get-options...]

Common useful features for SAT benchmarks:
  meta:  track  result  family  filename  isohash  author
  base:  variables  clauses  horn  bytes  status  minisat1m

Examples:
  query.sh "track=main_2025"                                          # all 2025-main instances
  query.sh "track=main_2025 and result=unsat" -r filename             # known-UNSAT, filenames only
  query.sh "track=main_2025 and result=sat and variables<500" \
           -r filename variables clauses                              # small SAT instances + size
  query.sh "family like rphp%" -r filename family result              # rphp family with status

Operators: =  !=  <  >  <=  >=  like  unlike
Combine:   and  or  ( )
EOF
    exit 1
fi

# Filter known-benign Python SIGPIPE noise from gbd's stderr.  When
# the output is piped into `head` (or any tool that closes its stdin
# early), Python's default SIGPIPE handler raises BrokenPipeError and
# prints an "Exception ignored" traceback to stderr.  Standard Unix
# tools silently exit on SIGPIPE; gbd's Python doesn't.  We drop those
# specific lines, keeping any real errors intact.
gbd get "$@" 2> >(grep -v -E '^(Exception ignored|BrokenPipeError)' >&2)
