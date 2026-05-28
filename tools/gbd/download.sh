#!/usr/bin/env bash
#
# Download CNFs from benchmark-database.de matching a GBD query.
#
# Two-step flow (per the GBD quickstart):
#   1. Fetch a `.uri` file from /getinstances that lists download URLs
#      for all matching instances.
#   2. wget --content-disposition -i that .uri file (saves each as
#      <md5hash>-<filename>.cnf.xz into BENCH_DIR).
#
# Usage:
#   download.sh "<query>" [--limit N] [--dry-run]
#
# Examples:
#   download.sh "track=main_2025 and result=unsat and variables<500"
#   download.sh "track=anni_2022 and family=php" --dry-run
#   download.sh "track=main_2025" --limit 20
#
# Environment:
#   BENCH_DIR    Where the .cnf.xz files land.  Default:
#                /Users/greg/projects/sat_benchmarks
#   DOWNLOAD_PAR Parallel wget workers.  Default: 4

set -euo pipefail

BENCH_DIR=${BENCH_DIR:-/Users/greg/projects/sat_benchmarks}
DOWNLOAD_PAR=${DOWNLOAD_PAR:-4}

QUERY=""
LIMIT=0
DRY_RUN=0

while [ $# -gt 0 ]; do
    case "$1" in
        --limit)   LIMIT=$2; shift 2 ;;
        --dry-run) DRY_RUN=1; shift ;;
        --help|-h)
            sed -n '3,25p' "$0"
            exit 0
            ;;
        -*) echo "unknown flag: $1" >&2; exit 1 ;;
        *)
            if [ -z "$QUERY" ]; then QUERY=$1
            else echo "multiple queries given" >&2; exit 1; fi
            shift
            ;;
    esac
done

if [ -z "$QUERY" ]; then
    echo "usage: $0 \"<query>\" [--limit N] [--dry-run]" >&2
    exit 1
fi

mkdir -p "$BENCH_DIR"

# Build the URI request URL.  The /getinstances endpoint serves a
# wget-compatible file: one download URL per line, plus
# Content-Disposition headers so wget saves each with its proper name.
# Escape spaces + special chars in the query for URL embedding.
encoded=$(python3 -c "import urllib.parse, sys; print(urllib.parse.quote(sys.argv[1]))" "$QUERY")
uri_url="https://benchmark-database.de/getinstances?query=${encoded}&context=cnf"
uri_file=$(mktemp -t gbd-uri.XXXXXX)
trap 'rm -f "$uri_file"' EXIT

echo "query:      $QUERY"
echo "uri url:    $uri_url"
echo "uri file:   $uri_file"
echo

# Step 1: fetch the .uri file.
wget --quiet -O "$uri_file" "$uri_url"
n_uri=$(wc -l < "$uri_file" | tr -d ' ')
echo "matched:    $n_uri instances"

# Optional limit.
if [ "$LIMIT" -gt 0 ] && [ "$LIMIT" -lt "$n_uri" ]; then
    head -n "$LIMIT" "$uri_file" > "$uri_file.limited"
    mv "$uri_file.limited" "$uri_file"
    echo "limited to: $LIMIT instances"
fi

# Filter out files we already have.  GBD names them
# <md5>-<original_basename>.cnf.xz; we match by md5 prefix.
already=0
declare -a need_urls
while IFS= read -r url; do
    [ -z "$url" ] && continue
    # The md5 is in the URL path: /file/<md5>
    md5=$(echo "$url" | sed -E 's|.*/||; s|\?.*||')
    if compgen -G "$BENCH_DIR/${md5}-*.cnf.xz" >/dev/null; then
        already=$((already + 1))
    else
        need_urls+=("$url")
    fi
done < "$uri_file"
echo "already on disk: $already"
echo "to download:     ${#need_urls[@]}"

if [ "$DRY_RUN" -eq 1 ]; then
    echo
    echo "--- dry-run: first 5 URLs would be fetched ---"
    printf '%s\n' "${need_urls[@]:0:5}"
    exit 0
fi

if [ "${#need_urls[@]}" -eq 0 ]; then
    echo "nothing to do."
    exit 0
fi

# Step 2: download in parallel via wget -P.  wget natively handles
# the Content-Disposition rename so files land as <md5>-<name>.cnf.xz.
echo
echo "downloading ${#need_urls[@]} files (parallel=$DOWNLOAD_PAR) into $BENCH_DIR..."
cd "$BENCH_DIR"
printf '%s\n' "${need_urls[@]}" \
    | xargs -n 1 -P "$DOWNLOAD_PAR" wget -q --content-disposition

echo "done."
echo "current $BENCH_DIR size: $(du -sh "$BENCH_DIR" | cut -f1)"
