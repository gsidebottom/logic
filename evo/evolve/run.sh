#!/usr/bin/env bash
#
# run.sh — one-shot launcher for an OpenEvolve run on the eff
# backend.  Wires up:
#
#   1. LiteLLM proxy on localhost:4000 (translates OpenAI-shape
#      calls to Bedrock / direct Anthropic / etc.)
#   2. openevolve-run.py pointed at the proxy
#   3. Cleanup on exit (proxy killed, worktrees removed)
#
# Prereqs:
#   * `./setup.sh` from repo root (uv venv with openevolve + litellm)
#   * One of:
#       (a) AWS creds + Bedrock model access enabled (default)
#       (b) ANTHROPIC_API_KEY for direct Anthropic
#       (c) OPENAI_API_KEY for direct OpenAI
#     Select via PROVIDER env (`bedrock` / `anthropic` / `openai`).
#
# Override via env:
#   PROVIDER       — bedrock | anthropic | openai      (default: bedrock)
#   ITERATIONS     — generations to run                 (default: from config.yaml)
#   MODEL_OPUS     — model id for the "opus" slot       (default: provider-specific)
#   MODEL_SONNET   — model id for the "sonnet" slot     (default: provider-specific)
#   AWS_REGION     — Bedrock region                     (default: us-east-1)
#   LITELLM_PORT   — proxy port                         (default: 4000)
#
# Example invocations:
#   ./run.sh                              # 50-iter pilot on Bedrock+Opus
#   ITERATIONS=5 ./run.sh                 # smoke test
#   PROVIDER=anthropic ./run.sh           # direct API, no Bedrock
#   ITERATIONS=200 ./run.sh               # full run

set -euo pipefail

HERE=$(cd "$(dirname "$0")" && pwd)
REPO_ROOT=$(cd "$HERE/../.." && pwd)
cd "$REPO_ROOT"

PROVIDER=${PROVIDER:-bedrock}
LITELLM_PORT=${LITELLM_PORT:-4000}
AWS_REGION=${AWS_REGION:-us-east-1}
# Adaptive-thinking effort for Opus 4.8 / Sonnet 4.6.  Controls how
# many reasoning tokens the model spends — the main cost lever.
#   low      thriftiest (smallest thinking budget) — good for piloting
#   medium   balanced
#   high     deepest reasoning (the model's own default) — priciest
#   none     disable thinking entirely (cheapest, but worse mutations)
# LiteLLM maps this OpenAI-style `reasoning_effort` to Anthropic's
# native `output_config.effort` for these models.
EFFORT=${EFFORT:-low}

# ─── Provider-specific model IDs ────────────────────────────────────
# LiteLLM model name format varies per provider.  Defaults aim at
# the current-generation Opus/Sonnet on each.  If a default goes
# stale (Anthropic version bumps), set MODEL_OPUS / MODEL_SONNET
# explicitly.
case "$PROVIDER" in
    bedrock)
        # Bedrock IDs (Claude 4.6+ use the dateless form on Bedrock
        # too).  The `us.` prefix selects a cross-region inference
        # profile for higher quota.  VERIFY the exact ID for your
        # region with:
        #   aws bedrock list-foundation-models --region $AWS_REGION \
        #       --query 'modelSummaries[?contains(modelId,`opus`)].modelId'
        : "${MODEL_OPUS:=bedrock/us.anthropic.claude-opus-4-8}"
        : "${MODEL_SONNET:=bedrock/us.anthropic.claude-sonnet-4-6}"
        # LiteLLM uses standard AWS SDK auth — env or ~/.aws/credentials.
        : "${AWS_REGION_NAME:=$AWS_REGION}"
        export AWS_REGION_NAME
        ;;
    anthropic)
        # LiteLLM routes to the Anthropic provider when the model
        # string carries the `anthropic/` prefix.  IDs are the
        # dateless pinned-snapshot form (Claude 4.6+ convention).
        : "${MODEL_OPUS:=anthropic/claude-opus-4-8}"
        : "${MODEL_SONNET:=anthropic/claude-sonnet-4-6}"
        if [ -z "${ANTHROPIC_API_KEY:-}" ]; then
            echo "ERROR: PROVIDER=anthropic requires ANTHROPIC_API_KEY" >&2
            exit 1
        fi
        ;;
    openai)
        : "${MODEL_OPUS:=gpt-4o}"           # closest "smart" stand-in
        : "${MODEL_SONNET:=gpt-4o-mini}"
        if [ -z "${OPENAI_API_KEY:-}" ]; then
            echo "ERROR: PROVIDER=openai requires OPENAI_API_KEY" >&2
            exit 1
        fi
        ;;
    *)
        echo "ERROR: PROVIDER must be one of: bedrock | anthropic | openai" >&2
        exit 1
        ;;
esac

echo "→ provider:   $PROVIDER"
echo "→ opus model: $MODEL_OPUS"
echo "→ sonnet:     $MODEL_SONNET"
echo "→ effort:     $EFFORT  (reasoning budget — cost lever; EFFORT=high to deepen)"
echo

# ─── Spin up LiteLLM proxy ──────────────────────────────────────────
# Write a minimal config.yaml on the fly that maps the human-friendly
# "claude-opus" / "claude-sonnet" aliases (referenced in our OpenEvolve
# config.yaml) to the provider-specific model IDs above.
PROXY_CFG=$(mktemp -t litellm-cfg.XXXXXX.yaml)
cat > "$PROXY_CFG" <<EOF
model_list:
  - model_name: claude-opus
    litellm_params:
      model: $MODEL_OPUS
      # Adaptive-thinking effort (cost lever).  LiteLLM maps this to
      # Anthropic's native \`output_config.effort\` for Opus 4.8 /
      # Sonnet 4.6.  Injected here so OpenEvolve doesn't need to know
      # about it.  Override per-run with EFFORT=high ./run.sh etc.
      reasoning_effort: $EFFORT
      # Force-drop the sampling params Opus 4.8 / adaptive-thinking
      # models deprecated.  \`drop_params\` (below) won't catch these
      # because LiteLLM's static map says "Anthropic supports
      # temperature/top_p" — true in general, but these specific
      # models reject them with a 400.  \`additional_drop_params\`
      # strips them unconditionally before the call.  Harmless on
      # models that DO accept them (they just fall back to defaults).
      additional_drop_params: ["temperature", "top_p"]
  - model_name: claude-sonnet
    litellm_params:
      model: $MODEL_SONNET
      reasoning_effort: $EFFORT
      additional_drop_params: ["temperature", "top_p"]
litellm_settings:
  # Drop params the target provider's static support map rejects —
  # notably \`seed\` (OpenEvolve sends it; Anthropic has no
  # equivalent).  Safe: \`seed\` only affects LLM-sampling
  # reproducibility; OpenEvolve's own candidate-selection RNG
  # (random_seed in config.yaml) is unaffected.
  drop_params: true
general_settings:
  master_key: sk-evo-local-noauth-needed
EOF

# We need a "key" for the OpenAI-compatible API; LiteLLM accepts any
# string when no auth is enforced and the master_key matches.
export OPENAI_API_KEY="sk-evo-local-noauth-needed"

# Resolve litellm from the uv venv so run.sh works WITHOUT the venv
# activated (mirrors the `uv run openevolve-run` call below).  Calling
# the binary directly — rather than `uv run litellm` — keeps `$!`
# pointing at the real proxy process so the cleanup trap kills it.
LITELLM_BIN="$REPO_ROOT/.venv/bin/litellm"
[ -x "$LITELLM_BIN" ] || LITELLM_BIN=$(command -v litellm || true)
if [ -z "$LITELLM_BIN" ]; then
    echo "ERROR: litellm not found (looked in $REPO_ROOT/.venv/bin and PATH)." >&2
    echo "       Run ./setup.sh from the repo root to build the uv venv." >&2
    exit 1
fi

echo "→ starting LiteLLM proxy on :$LITELLM_PORT ..."
# Background the proxy; capture pid so we can kill it on exit.
"$LITELLM_BIN" --config "$PROXY_CFG" --port "$LITELLM_PORT" --num_workers 1 \
        > "$HERE/runs/.litellm.log" 2>&1 &
PROXY_PID=$!

cleanup() {
    echo
    echo "→ shutting down LiteLLM proxy (pid=$PROXY_PID) ..."
    kill "$PROXY_PID" 2>/dev/null || true
    wait "$PROXY_PID" 2>/dev/null || true
    rm -f "$PROXY_CFG"
}
trap cleanup EXIT INT TERM

# Wait for the proxy to come up (LiteLLM logs "Uvicorn running" when
# ready).  Bail after 30s if it never starts.
for i in $(seq 1 30); do
    if curl -sf "http://localhost:$LITELLM_PORT/health/readiness" >/dev/null 2>&1; then
        echo "✓ proxy ready"
        break
    fi
    if ! kill -0 "$PROXY_PID" 2>/dev/null; then
        echo "ERROR: LiteLLM proxy crashed.  Tail of log:" >&2
        tail -30 "$HERE/runs/.litellm.log" >&2
        exit 1
    fi
    sleep 1
done

# ─── Run OpenEvolve ─────────────────────────────────────────────────
RUN_TAG=$(date +%Y%m%d-%H%M%S)
RUN_OUT="$HERE/runs/$RUN_TAG"
mkdir -p "$RUN_OUT"

ITER_FLAG=()
if [ -n "${ITERATIONS:-}" ]; then
    ITER_FLAG=(--iterations "$ITERATIONS")
fi

echo "→ launching openevolve (run dir: $RUN_OUT)"
echo

# `openevolve-run` is the console entry point installed by the
# openevolve package (NOT a script file — the `.py` form only
# exists in a cloned repo).  `uv run` resolves it from .venv/bin.
uv run openevolve-run \
    "$HERE/initial_program.rs" \
    "$HERE/evaluator.py" \
    --config "$HERE/config.yaml" \
    --output "$RUN_OUT" \
    "${ITER_FLAG[@]}"

echo
echo "✓ run complete; artifacts in $RUN_OUT"
echo "  best candidates / fitness landscape: $RUN_OUT/best/"
