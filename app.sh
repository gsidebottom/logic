#!/bin/bash

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PID_FILE="$SCRIPT_DIR/.pids"
LOG_DIR="$SCRIPT_DIR/.logs"
RUST_BIN="$SCRIPT_DIR/target/release/web_app"
VITE_DIR="$SCRIPT_DIR/nested-boxes"

export PATH="$HOME/.local/bin:$HOME/.cargo/bin:$PATH"

mkdir -p "$LOG_DIR"

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
    parse_port "$@"

    read_pids
    if [[ -n "$RUST_PID" ]] && pid_running "$RUST_PID"; then
        echo "Already running. Use restart or stop first."; exit 1
    fi

    cmd_build "$force"

    echo "Starting web_app..."
    "$RUST_BIN" >> "$LOG_DIR/web_app.log" 2>&1 &
    RUST_PID=$!

    echo "Starting Vite UI on port $VITE_PORT..."
    (cd "$VITE_DIR" && bunx vite --port "$VITE_PORT" >> "$LOG_DIR/vite.log" 2>&1) &
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
    if [[ -z "$RUST_PID" ]]; then echo "Not running."; return; fi

    for pid in "$RUST_PID" "$VITE_PID"; do
        if [[ -n "$pid" ]] && pid_running "$pid"; then
            kill "$pid" && echo "Stopped PID $pid"
        fi
    done

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
