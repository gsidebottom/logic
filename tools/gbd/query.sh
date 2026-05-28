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

# Make sure the user-site Python bin is on PATH so `gbd` is callable.
# (pip --user installs land here on macOS; ~/.local/bin on Linux.)
USER_BIN=$(python3 -c "import site; print(site.getuserbase() + '/bin')")
export PATH="$USER_BIN:$PATH"
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
