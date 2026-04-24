# ─────────────────────────────────────────────────────────────────────────────
# Multi-stage build for the `logic` web app.
# Stage 1: build the Rust `web_app` binary (with the vendored CaDiCaL C++ src).
# Stage 2: build the Vite/React frontend into a static bundle.
# Stage 3: slim Debian runtime that bundles the binary, the static bundle, the
#          jq libraries, and the examples file.  One process, one port (3001).
# ─────────────────────────────────────────────────────────────────────────────

# ── Stage 1: Rust backend ─────────────────────────────────────────────────────
FROM rust:1.88-bookworm AS rust-builder
WORKDIR /app

# CaDiCaL compiles C++ from source via cc; make sure clang++ and libc++ headers
# are present.  The `cadical` crate vendors the C++ sources so we only need a
# C++ toolchain, not a separate CaDiCaL install.
RUN apt-get update \
    && apt-get install -y --no-install-recommends clang libc++-dev libc++abi-dev ca-certificates \
    && rm -rf /var/lib/apt/lists/*

COPY Cargo.toml Cargo.lock ./
COPY src ./src
RUN cargo build --release --bin web_app --locked

# ── Stage 2: frontend ─────────────────────────────────────────────────────────
FROM oven/bun:1-debian AS frontend-builder
WORKDIR /app

COPY nested-boxes/package.json nested-boxes/bun.lock* nested-boxes/bun.lockb* ./
RUN bun install --frozen-lockfile 2>/dev/null || bun install

COPY nested-boxes/ ./
RUN bunx vite build

# ── Stage 3: runtime ──────────────────────────────────────────────────────────
FROM debian:bookworm-slim AS runtime
WORKDIR /app

RUN apt-get update \
    && apt-get install -y --no-install-recommends libc++1 libc++abi1 ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# Binary + static bundle + data files.
COPY --from=rust-builder /app/target/release/web_app /usr/local/bin/web_app
COPY --from=frontend-builder /app/dist /app/static
COPY lib /app/lib
COPY examples.json /app/examples.json

# The server binary reads:
#   * cwd/lib/                (jq libraries read/write)
#   * cwd/examples.json       (formula examples read/write)
# and, when STATIC_DIR is set, serves that directory at `/` for the frontend.
ENV STATIC_DIR=/app/static
ENV PORT=3001

EXPOSE 3001

# Ensure the writable paths are actually writable when bind-mounted read-only
# filesystems are used — users who want persistence should volume-mount
# /app/lib and /app/examples.json.
CMD ["/usr/local/bin/web_app"]
