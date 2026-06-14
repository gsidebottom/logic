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
#      CLI into .venv/bin).  Auto-selects the neural/ ML backend extra:
#      Apple Silicon -> mlx, a CUDA host (nvidia-smi) -> torch, else none.
#      Override with `--ml-backend mlx|torch|none` or ML_BACKEND=...
#   3. Build + install the GRAT verified-checker tool chain
#      (gratgen + gratchk) into ~/.cargo/bin, used to certify the
#      pb-cadical/hydra kissat path's UNSAT proofs.  Needs Boost + MLton
#      (auto-installed via brew/apt).  Skip with `--no-grat` / GRAT_SETUP=0;
#      skipped automatically when already installed; warns (never aborts)
#      if a compiler/Boost/MLton is missing.
#   4. Optionally chain to the GBD database download
#      (tools/gbd/setup.sh) when invoked with `--gbd` or `GBD_SETUP=1`.
#   5. Print activation / usage instructions.
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
# GRAT verified-checker tool chain (gratgen + gratchk) for the kissat-path
# UNSAT proofs (pb-cadical / hydra).  Built by default; --no-grat skips it,
# GRAT_SETUP=0 disables.  Skipped automatically when already installed.
do_grat=1
if [ "${GRAT_SETUP:-1}" = "0" ]; then do_grat=0; fi
# Neural-SAT ML accelerator backend (neural/): auto | mlx | torch | none.
# `auto` (default) picks per platform below; ML_BACKEND env overrides.
ml_backend="${ML_BACKEND:-auto}"
while [ $# -gt 0 ]; do
    case "$1" in
        --gbd|--with-gbd)    do_gbd=1; shift ;;
        --no-gbd)            do_gbd=0; shift ;;
        --grat)              do_grat=1; shift ;;
        --no-grat)           do_grat=0; shift ;;
        --ml-backend)        ml_backend="${2:?--ml-backend needs auto|mlx|torch|none}"; shift 2 ;;
        --ml-backend=*)      ml_backend="${1#*=}"; shift ;;
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
# Auto-select the neural/ ML accelerator backend unless overridden:
#   CUDA present (nvidia-smi)       -> torch  (portable; cluster GPUs)
#   Apple Silicon (Darwin/arm64)   -> mlx    (fast on M-series)
#   otherwise                      -> none   (core only; force with --ml-backend)
if [ "$ml_backend" = "auto" ]; then
    if command -v nvidia-smi >/dev/null 2>&1; then
        ml_backend=torch
    elif [ "$(uname -s)" = "Darwin" ] && \
         { [ "$(uname -m)" = "arm64" ] || [ "$(uname -m)" = "aarch64" ]; }; then
        ml_backend=mlx
    else
        ml_backend=none
    fi
fi
echo "→ syncing Python environment from pyproject.toml (ML backend: $ml_backend) ..."
case "$ml_backend" in
    none)       uv sync ;;
    mlx|torch)  uv sync --extra "$ml_backend" ;;
    *) echo "ERROR: --ml-backend must be auto|mlx|torch|none (got '$ml_backend')" >&2
       return 2 2>/dev/null || exit 2 ;;
esac

# ── Step 2.5: GRAT verified-checker tool chain (kissat-path UNSAT proofs) ──
# The pb-cadical/hydra kissat path elaborates kissat's binary DRAT into a
# GRAT certificate with `gratgen` (parallel; faster + lighter than
# drat-trim) and verifies it with the formally-verified `gratchk`.  We
# build both from Lammich's distribution and install them next to the
# other checkers in ~/.cargo/bin.  Degrades gracefully: a missing
# compiler / Boost / MLton just warns (proofs go unchecked), never aborts.
install_grat() {
    local bindir="$HOME/.cargo/bin"
    if { command -v gratgen >/dev/null 2>&1 || [ -x "$bindir/gratgen" ]; } && \
       { command -v gratchk >/dev/null 2>&1 || [ -x "$bindir/gratchk" ]; }; then
        echo "✓ GRAT tool chain already installed (gratgen, gratchk)"
        return 0
    fi
    echo "→ installing GRAT tool chain (gratgen + gratchk) ..."
    mkdir -p "$bindir"
    # Dependencies: Boost headers (gratgen) + MLton (gratchk).
    if [ "$(uname -s)" = "Darwin" ]; then
        if command -v brew >/dev/null 2>&1; then
            brew list boost >/dev/null 2>&1 || brew install boost || true
            command -v mlton >/dev/null 2>&1 || brew install mlton || true
        else
            echo "  ! Homebrew not found — install 'boost' and 'mlton' manually." >&2
        fi
    elif command -v apt-get >/dev/null 2>&1; then
        sudo apt-get install -y libboost-dev mlton >/dev/null 2>&1 || \
            echo "  ! apt-get install libboost-dev mlton failed — install manually." >&2
    else
        echo "  ! unknown platform — ensure Boost headers + MLton are installed." >&2
    fi
    # Pick a C++ compiler.
    local cxx=""
    for c in c++ g++ clang++; do command -v "$c" >/dev/null 2>&1 && { cxx="$c"; break; }; done
    if [ -z "$cxx" ] || ! command -v mlton >/dev/null 2>&1; then
        echo "  ! missing C++ compiler or MLton — skipping GRAT build." >&2
        echo "    (kissat-path UNSAT proofs go unchecked until installed)" >&2
        return 0
    fi
    local inc=""
    [ -d /opt/homebrew/include ] && inc="-I/opt/homebrew/include"      # macOS brew
    [ -d /usr/local/include ]    && inc="$inc -I/usr/local/include"
    local work base
    work=$(mktemp -d); base="https://www21.in.tum.de/~lammich/grat"
    if ( cd "$work" \
         && curl -fsSL -o gratgen.tgz     "$base/gratgen.tgz" \
         && curl -fsSL -o gratchk-sml.tgz "$base/gratchk-sml.tgz" \
         && tar xzf gratgen.tgz && tar xzf gratchk-sml.tgz \
         && "$cxx" -O3 -DNDEBUG -DBOOST_TIMER_ENABLE_DEPRECATED -std=c++11 \
                -pthread $inc -o gratgen/gratgen gratgen/gratgen.cpp \
         && make -C gratchk-sml >/dev/null ); then
        cp "$work/gratgen/gratgen"      "$bindir/gratgen"
        cp "$work/gratchk-sml/gratchk"  "$bindir/gratchk"
        chmod +x "$bindir/gratgen" "$bindir/gratchk"
        echo "✓ GRAT installed to $bindir (gratgen, gratchk)"
    else
        echo "  ! GRAT build failed — kissat-path UNSAT proofs go unchecked." >&2
        echo "    Boost 1.90+ removed <boost/progress.hpp>; we pass" >&2
        echo "    -DBOOST_TIMER_ENABLE_DEPRECATED to keep it building." >&2
    fi
    rm -rf "$work"
    return 0
}
if [ "$do_grat" = "1" ]; then
    echo
    install_grat
fi

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
