#!/bin/bash

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PID_FILE="$SCRIPT_DIR/.pids"
LOG_DIR="$SCRIPT_DIR/.logs"
RUST_BIN="$SCRIPT_DIR/target/release/web_app"
VITE_DIR="$SCRIPT_DIR/nested-boxes"

export PATH="$HOME/.local/bin:$HOME/.cargo/bin:$PATH"

mkdir -p "$LOG_DIR"

# ── Prerequisites ─────────────────────────────────────────────────────────────

is_mac() { [[ "$(uname)" == "Darwin" ]]; }

ensure_prereqs() {
    local missing=()

    # Check cargo (Rust)
    if ! command -v cargo &>/dev/null; then
        echo "Installing Rust via rustup..."
        curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
        source "$HOME/.cargo/env"
        if ! command -v cargo &>/dev/null; then
            echo "ERROR: Failed to install Rust"; exit 1
        fi
    fi

    # Check bun
    if ! command -v bun &>/dev/null; then
        echo "Installing bun..."
        curl -fsSL https://bun.sh/install | bash
        export PATH="$HOME/.bun/bin:$PATH"
        if ! command -v bun &>/dev/null; then
            echo "ERROR: Failed to install bun"; exit 1
        fi
    fi

    # Check node (needed by vite at runtime)
    if ! command -v node &>/dev/null; then
        echo "Installing Node.js..."
        if is_mac; then
            if command -v brew &>/dev/null; then
                brew install node
            else
                echo "Installing Homebrew first..."
                /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
                eval "$(/opt/homebrew/bin/brew shellenv 2>/dev/null || /usr/local/bin/brew shellenv 2>/dev/null)"
                brew install node
            fi
        else
            # Linux: use NodeSource or distro package manager
            if command -v apt-get &>/dev/null; then
                sudo apt-get update && sudo apt-get install -y nodejs npm
            elif command -v dnf &>/dev/null; then
                sudo dnf install -y nodejs npm
            elif command -v pacman &>/dev/null; then
                sudo pacman -S --noconfirm nodejs npm
            else
                echo "ERROR: Cannot auto-install Node.js — install it manually"; exit 1
            fi
        fi
        if ! command -v node &>/dev/null; then
            echo "ERROR: Failed to install Node.js"; exit 1
        fi
    fi

    # Install node_modules if missing
    if [[ ! -d "$VITE_DIR/node_modules" ]]; then
        echo "Installing frontend dependencies..."
        (cd "$VITE_DIR" && bun install) || { echo "ERROR: bun install failed"; exit 1; }
    fi
}

# ── Helpers ───────────────────────────────────────────────────────────────────

pid_running() { kill -0 "$1" 2>/dev/null; }

read_pids() {
    if [[ -f "$PID_FILE" ]]; then
        read -r RUST_PID VITE_PID VITE_PORT < "$PID_FILE"
        VITE_PORT="${VITE_PORT:-8080}"
    else
        RUST_PID=""; VITE_PID=""; VITE_PORT="8080"
    fi
}

parse_port() {
    VITE_PORT="8080"
    while [[ $# -gt 0 ]]; do
        case "$1" in
            --port|-p) VITE_PORT="${2:?--port requires a value}"; shift 2 ;;
            *) shift ;;
        esac
    done
}

# Kill any processes listening on the Rust service port (catches orphaned instances)
kill_rust_orphans() {
    local pids
    pids=$(lsof -ti:3001 2>/dev/null)
    if [[ -n "$pids" ]]; then
        echo "$pids" | xargs kill 2>/dev/null
        sleep 0.3
    fi
}

# Kill any orphaned vite processes from this project
kill_vite_orphans() {
    local pids
    pids=$(pgrep -f "node.*$VITE_DIR.*vite" 2>/dev/null)
    if [[ -n "$pids" ]]; then
        echo "$pids" | xargs kill 2>/dev/null
        sleep 0.3
    fi
}

# ── Commands ──────────────────────────────────────────────────────────────────

needs_build() {
    [[ ! -x "$RUST_BIN" ]] && return 0  # binary missing
    # rebuild if any .rs file or Cargo.toml is newer than the binary
    find "$SCRIPT_DIR/src" "$SCRIPT_DIR/Cargo.toml" \
        -name "*.rs" -o -name "Cargo.toml" 2>/dev/null \
        | xargs -I{} find {} -newer "$RUST_BIN" -print -quit \
        | grep -q .
}

cmd_build() {
    local force=${1:-}
    if [[ "$force" == "--force" ]] || needs_build; then
        [[ "$force" == "--force" ]] && echo "Building web_app (forced)..." \
                                    || echo "Building web_app (source changed)..."
        cargo build --release --bin web_app --manifest-path "$SCRIPT_DIR/Cargo.toml" || exit 1
    else
        echo "web_app is up to date, skipping build."
    fi
}

cmd_start() {
    local force=""
    [[ "$*" == *"--force"* || "$*" == *"-f"* ]] && force="--force"

    ensure_prereqs

    read_pids
    parse_port "$@"
    if [[ -n "$RUST_PID" ]] && pid_running "$RUST_PID"; then
        echo "Already running. Use restart or stop first."; exit 1
    fi

    # Kill any orphaned instances from previous sessions before starting
    kill_rust_orphans
    kill_vite_orphans

    cmd_build "$force"

    echo "Starting web_app..."
    "$RUST_BIN" >> "$LOG_DIR/web_app.log" 2>&1 &
    RUST_PID=$!

    echo "Starting Vite UI on port $VITE_PORT..."
    (cd "$VITE_DIR" && bunx vite --port "$VITE_PORT" --strictPort >> "$LOG_DIR/vite.log" 2>&1) &
    VITE_PID=$!

    echo "$RUST_PID $VITE_PID $VITE_PORT" > "$PID_FILE"

    sleep 1  # give processes a moment to start

    echo ""
    cmd_status
    echo ""
    echo "Logs: $LOG_DIR/"
}

cmd_stop() {
    read_pids

    for pid in "$RUST_PID" "$VITE_PID"; do
        if [[ -n "$pid" ]] && pid_running "$pid"; then
            kill "$pid" && echo "Stopped PID $pid"
        fi
    done

    # Also kill any orphaned instances not tracked by .pids
    kill_rust_orphans
    kill_vite_orphans

    rm -f "$PID_FILE"
}

cmd_status() {
    read_pids

    check() {
        local label=$1 pid=$2 url=$3
        if [[ -n "$pid" ]] && pid_running "$pid"; then
            echo "  ✓  $label  (PID $pid)  →  $url"
        else
            echo "  ✗  $label  — not running"
        fi
    }

    check "web_app" "$RUST_PID" "http://localhost:3001"
    check "vite   " "$VITE_PID" "http://localhost:$VITE_PORT"
}

cmd_monitor() {
    while true; do
        clear
        echo "$(date)  [Ctrl-C to exit]"
        echo "─────────────────────────────────────────"
        cmd_status
        echo ""
        echo "── web_app ──────────────────────────────"
        tail -8 "$LOG_DIR/web_app.log" 2>/dev/null || echo "(no log yet)"
        echo ""
        echo "── vite ─────────────────────────────────"
        tail -8 "$LOG_DIR/vite.log" 2>/dev/null || echo "(no log yet)"
        sleep 3
    done
}

cmd_logs() {
    tail -f "$LOG_DIR/web_app.log" "$LOG_DIR/vite.log" 2>/dev/null
}

# ── Dispatch ──────────────────────────────────────────────────────────────────

case "${1:-}" in
    start)   cmd_start "$@" ;;
    stop)    cmd_stop ;;
    restart) cmd_stop; sleep 1; cmd_start "$@" ;;
    build)   cmd_build "${2:-}" ;;
    status)  cmd_status ;;
    monitor) cmd_monitor ;;
    logs)    cmd_logs ;;
    *)
        echo "Usage: $0 {start|stop|restart|build|status|monitor|logs} [--force|-f] [--port|-p PORT]"
        exit 1 ;;
esac
