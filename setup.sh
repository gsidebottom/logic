#!/usr/bin/env bash
#
# setup.sh — bootstrap the Python tooling for this repo using `uv`.
#
# `uv` (https://docs.astral.sh/uv/) is Astral's cross-platform Python
# manager.  It downloads + caches a Python interpreter that satisfies
# `requires-python` from pyproject.toml, creates a project venv, and
# installs every declared dependency in one step — no system pip, no
# `pip install --user` PATH games, no per-OS divergence.
#
# What this script does:
#   1. Install `uv` if it's not already on PATH (curl- or wget-based
#      bootstrap from https://astral.sh/uv/install.sh).
#   2. Run `uv sync` to provision ./.venv from pyproject.toml, pulling
#      `matplotlib` and `gbd-tools` (which itself installs the `gbd`
#      CLI into .venv/bin).
#   3. Optionally chain to the GBD database download
#      (tools/gbd/setup.sh) when invoked with `--gbd` or `GBD_SETUP=1`.
#   4. Print activation / usage instructions.
#
# Idempotent — re-running is safe and picks up any new entries in
# pyproject.toml.  Will NOT overwrite an existing .venv unless
# pyproject.toml asks for a different Python version.
#
# Platform notes:
#   * Tested on macOS, Linux, and Windows under Git-Bash / WSL.
#   * On native Windows (PowerShell / cmd) skip this script and run
#     the uv installer + `uv sync` directly per
#     https://docs.astral.sh/uv/getting-started/installation/
#
# To get the venv activated in your current shell (so `python3` /
# `gbd` resolve to the project ones), source this script instead of
# executing it:
#
#     . ./setup.sh            # bash / zsh — leaves you in the venv
#     ./setup.sh              # ordinary exec — env exists, not active
#
# When sourced, we `source .venv/bin/activate` for you at the end.
# When executed, we print the activation command instead.

set -euo pipefail

# ── Sourced-vs-executed detection ────────────────────────────────────
# In bash: $BASH_SOURCE[0] != $0 iff the file was sourced.
# In zsh:  $ZSH_EVAL_CONTEXT contains ':file' for sourced files.
# Fallback: assume executed.
__sourced=0
if [ -n "${BASH_SOURCE:-}" ]; then
    [ "${BASH_SOURCE[0]:-$0}" != "$0" ] && __sourced=1
elif [ -n "${ZSH_EVAL_CONTEXT:-}" ]; then
    case "$ZSH_EVAL_CONTEXT" in *:file*) __sourced=1;; esac
fi

# ── Resolve the repo root from this script's own location ────────────
# Use the sourced path when sourced, $0 otherwise.  `realpath` is the
# portable way to get an absolute path (BSD `readlink -f` fails on
# macOS without coreutils).  Fall back to Python if neither exists.
__src="${BASH_SOURCE[0]:-$0}"
if command -v realpath >/dev/null 2>&1; then
    __abs=$(realpath "$__src")
elif command -v readlink >/dev/null 2>&1 && readlink -f / >/dev/null 2>&1; then
    __abs=$(readlink -f "$__src")
else
    __abs=$(python3 -c "import os,sys; print(os.path.realpath(sys.argv[1]))" "$__src")
fi
REPO_ROOT=$(cd "$(dirname "$__abs")" && pwd)

# ── Flag parsing ─────────────────────────────────────────────────────
do_gbd=0
if [ "${GBD_SETUP:-0}" = "1" ]; then do_gbd=1; fi
while [ $# -gt 0 ]; do
    case "$1" in
        --gbd|--with-gbd)    do_gbd=1; shift ;;
        --no-gbd)            do_gbd=0; shift ;;
        -h|--help)
            sed -n '2,40p' "$__abs" | sed 's/^# \{0,1\}//'
            return 0 2>/dev/null || exit 0
            ;;
        *)
            echo "setup.sh: unknown arg '$1'" >&2
            return 2 2>/dev/null || exit 2
            ;;
    esac
done

cd "$REPO_ROOT"

# ── Step 1: install uv if missing ────────────────────────────────────
if ! command -v uv >/dev/null 2>&1; then
    echo "→ uv not on PATH; installing from https://astral.sh/uv/"
    if command -v curl >/dev/null 2>&1; then
        curl -LsSf https://astral.sh/uv/install.sh | sh
    elif command -v wget >/dev/null 2>&1; then
        wget -qO- https://astral.sh/uv/install.sh | sh
    else
        echo "ERROR: need 'curl' or 'wget' to bootstrap uv." >&2
        echo "       Install one of them or install uv manually:" >&2
        echo "         https://docs.astral.sh/uv/getting-started/installation/" >&2
        return 1 2>/dev/null || exit 1
    fi
    # The installer drops the binary in $HOME/.local/bin (or
    # $XDG_BIN_HOME) — add common locations to PATH for the rest of
    # this script.  The installer also writes a one-liner to the
    # user's shell rc that does the equivalent permanently, but it
    # only takes effect after the next login.
    export PATH="$HOME/.local/bin:$HOME/.cargo/bin:$PATH"
fi

if ! command -v uv >/dev/null 2>&1; then
    echo "ERROR: uv install succeeded but 'uv' still not on PATH." >&2
    echo "       Restart your shell or add the install directory to PATH." >&2
    return 1 2>/dev/null || exit 1
fi

echo "✓ $(uv --version)"

# ── Step 2: sync the project's venv ──────────────────────────────────
# `uv sync` reads pyproject.toml (+ uv.lock if present), provisions a
# Python interpreter that satisfies requires-python (downloading from
# https://github.com/indygreg/python-build-standalone if the system
# Python doesn't qualify), creates ./.venv, and installs every
# declared dependency.  Subsequent runs are fast (lockfile + cache).
echo "→ syncing Python environment from pyproject.toml ..."
uv sync

# ── Step 3 (optional): GBD database setup ────────────────────────────
if [ "$do_gbd" = "1" ]; then
    echo
    echo "→ GBD database setup (--gbd / GBD_SETUP=1) ..."
    # tools/gbd/setup.sh needs the `gbd` CLI on PATH — it's installed
    # in the venv we just synced.  We're a subprocess (not sourced)
    # so `.venv/bin/activate` wouldn't propagate; just prepend the
    # venv's bin to PATH for the chained call.
    if   [ -d "$REPO_ROOT/.venv/bin" ];     then __venv_bin="$REPO_ROOT/.venv/bin"
    elif [ -d "$REPO_ROOT/.venv/Scripts" ]; then __venv_bin="$REPO_ROOT/.venv/Scripts"
    else __venv_bin=""; fi
    PATH="$__venv_bin${__venv_bin:+:}$PATH" "$REPO_ROOT/tools/gbd/setup.sh"
fi

# ── Step 4: activate (if sourced) or print instructions ──────────────
echo
echo "✓ Python environment ready in $REPO_ROOT/.venv"

# Cross-platform path to the activate script.  On POSIX it's
# .venv/bin/activate; on Windows it's .venv/Scripts/activate (bash) or
# .venv/Scripts/Activate.ps1 (PowerShell).  Pick whichever exists.
__activate=""
if   [ -f "$REPO_ROOT/.venv/bin/activate" ];          then __activate="$REPO_ROOT/.venv/bin/activate"
elif [ -f "$REPO_ROOT/.venv/Scripts/activate" ];      then __activate="$REPO_ROOT/.venv/Scripts/activate"
fi

if [ "$__sourced" = "1" ] && [ -n "$__activate" ]; then
    # Activate the venv in the caller's shell.  No-op if already active.
    # shellcheck disable=SC1090
    . "$__activate"
    echo "✓ venv activated in current shell ($(python3 --version))"
    echo "  (later, deactivate with 'deactivate')"
else
    cat <<EOF

To run a tool one-off (no activation needed):
  uv run tools/gbd/run_benchmark.py --index ...
  uv run doc/competition-benchmarks-plot.py FILE.md -o OUT.png

To activate the venv for this shell:
  source $REPO_ROOT/.venv/bin/activate          # bash / zsh
  source $REPO_ROOT/.venv/bin/activate.fish     # fish
  $REPO_ROOT/.venv/Scripts/activate             # Windows Git-Bash
  & $REPO_ROOT/.venv/Scripts/Activate.ps1       # Windows PowerShell

Or source this script directly to get the venv active for free:
  . ./setup.sh
EOF
fi
