#!/bin/bash
# Build the satsuma-iter-kissat Docker image (SAT Comp 2026 winner).
# Prefers the local archive copy of the official tarball; falls back to
# downloading from the competition site.
set -euo pipefail
DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" && pwd )
ARCHIVE="$HOME/projects/sat_benchmarks/archive/anders_satcomp2026.tar.xz"
URL="https://satcompetition.github.io/2026/downloads/solvers/anders.tar.xz"
CTX=$(mktemp -d)
trap 'rm -rf "$CTX"' EXIT
if [ -f "$ARCHIVE" ]; then
    cp "$ARCHIVE" "$CTX/anders.tar.xz"
else
    echo "archive copy not found; downloading from $URL"
    curl -sL --fail -o "$CTX/anders.tar.xz" "$URL"
    mkdir -p "$(dirname "$ARCHIVE")" && cp "$CTX/anders.tar.xz" "$ARCHIVE"
fi
cp "$DIR/Dockerfile" "$CTX/Dockerfile"
docker build -t satsuma-iter-kissat "$CTX"
echo "image satsuma-iter-kissat built"
