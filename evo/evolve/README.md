# `evo/evolve/` — OpenEvolve rig for the `eff` backend

This directory drives [OpenEvolve](https://github.com/algorithmicsuperintelligence/openevolve)
to mutate the matrix-method SAT solver's effective-count ordering
policy and score the mutations against the `evo/` benchmark set.

## What gets evolved

Three pure Rust functions in `src/dual/path_effective.rs`, wrapped
in `// EVOLVE-BLOCK-START` / `// EVOLVE-BLOCK-END` markers:

```rust
fn should_reorder_sum(counts: &[f64], tau: f64) -> bool
fn sum_visit_order  (counts: &[f64], tau: f64) -> Vec<usize>
fn prod_visit_order (counts: &[f64])           -> Vec<usize>
```

These decide visit-order at every Sum (visit-all) and Prod
(pick-one) node in the NNF complement.  The surrounding wrapper
glue (count maintenance, prefix tracking, CDCL integration) is
correctness-load-bearing and stays fixed.

`initial_program.rs` is the snapshot OpenEvolve starts from — same
contents as the live `path_effective.rs` evolve block.

## How scoring works (`evaluator.py`)

Each candidate runs in a fresh `git worktree`, so the live source
tree is never touched.  Three-tier cascade:

| Tier  | Subset       | Per-instance timeout | Workers | Wall time |
|-------|--------------|----------------------|---------|-----------|
| smoke | 6 problems   | 5s                   | 4       | ~10s      |
| quick | 20 problems  | 20s                  | 8       | ~50s      |
| full  | 81 problems  | 30s                  | 10      | ~4 min    |

Gates between tiers: any MISMATCH row (wrong-UNSAT) → reject; smoke
tier <3/6 solved → don't bother with quick/full.  Surviving
candidates land in OpenEvolve's MAP-Elites archive with this fitness
shape:

```python
{
    "compiled":         1.0,
    "sound":            1.0,
    "solved":           int,     # primary — maximize
    "neg_time":         -float,  # secondary — maximize (= min CPU)
    "timeout_progress": float,   # tertiary — partial credit for
                                 # paths_fraction on TIMEOUT rows
}
```

## Soundness guards — why an evolved policy can't cheat

The evolve target (`sum_visit_order` / `prod_visit_order` /
`should_reorder_sum`) only controls **visit order and zero-count
filtering** — it can't touch the verdict logic.  But verdict-vs-
ground-truth checking alone would be gameable: a mutation that
"declares UNSAT fast" by unsoundly pruning would get the right
answer on the UNSAT problems (by luck) and only be caught
probabilistically by the SAT problems.  Three layers close that:

1. **`evolve_guard` (the real fix, Rust-side).** The evaluator builds
   `sat` with `--features evolve_guard`, which turns on runtime
   assertions — living *outside* the EVOLVE block so a mutation can't
   disable them — that enforce the two soundness contracts:
   `sum_visit_order` must return a permutation (every Sum child
   visited once); `prod_visit_order` must keep every positive-count
   alt (only provably-blocked zero-count alts may be pruned).  A
   violation **panics** → that candidate's solves crash → it scores
   ~0.  This makes unsound search *inexpressible*, independent of the
   benchmark set's SAT/UNSAT balance — no proof needed.  See
   `enforce_sum_permutation` / `enforce_prod_keeps_reachable` in
   `src/dual/path_effective.rs`.

2. **SAT-witness verification (second line, Python-side).** The
   evaluator passes `--verify-sat-witness`, so every SAT verdict's
   `v`-line model is re-checked against the CNF clauses.  A bogus
   model paired with a correct SAT verdict → recorded as MISMATCH →
   `sound=0`.  Catches witness-reconstruction bugs the contract guard
   wouldn't.

3. **Proof-verified ground truth.** The 81 evo verdicts are
   independently verified — 35 SAT `assignment_verified`, 46 UNSAT
   `drat_verified` (cadical→drat-trim).  So the verdict cross-check
   compares against *proven* answers, not just CaDiCaL's say-so.

> **Note for widening the evolve target.** Guards #1–2 only guarantee
> soundness because the evolve target is *constrained* to pure
> visit-order/zero-drop functions.  If you later open up code where
> soundness isn't structural (cover detection, witness
> reconstruction, learned-clause logic), the construction guarantee
> evaporates and you'll need the backend to emit **verifiable proofs**
> per run.  Today only `cdcl`/`smart` can; the eff family can't.  That
> capability is tracked as a backlog item — keep it on the agenda
> before evolving outside the current block.

## How to run

### 1. Provision the Python env (one-time)

From the repo root:

```bash
./setup.sh                       # installs uv + creates .venv with
                                 # openevolve + litellm[proxy] + boto3
```

### 2. Pick an LLM provider

The `run.sh` launcher supports three:

```bash
PROVIDER=bedrock   ./run.sh      # AWS Bedrock — recommended (default)
PROVIDER=anthropic ./run.sh      # Direct Anthropic API
PROVIDER=openai    ./run.sh      # OpenAI (closest "smart" stand-in)
```

Pick whichever is least painful — they all flow through a local
LiteLLM proxy on `localhost:4000` that translates OpenAI-shaped
requests to the provider's native format.  OpenEvolve only sees the
proxy.

#### Bedrock setup (default `PROVIDER=bedrock`)

1. **Enable model access** in your AWS Bedrock console
   (one-time per account):
   - AWS Console → Bedrock → "Model access" (left nav)
   - Request access to "Anthropic Claude Opus" + "Anthropic Claude Sonnet"
   - Approval is usually instant for established AWS accounts;
     first-time approval can take a few hours.

2. **Confirm access** from the CLI:
   ```bash
   aws bedrock list-foundation-models --region us-east-1 \
       --query 'modelSummaries[?contains(modelId, `opus`)].[modelId,modelLifecycle.status]' \
       --output table
   ```
   You want `ACTIVE` rows for the Claude family.

3. **Set credentials** — any of:
   - `aws configure` (writes `~/.aws/credentials`)
   - Env vars `AWS_ACCESS_KEY_ID` / `AWS_SECRET_ACCESS_KEY` /
     `AWS_SESSION_TOKEN` (if SSO)
   - IAM role on the host (if running on EC2)

4. **Optional**: `AWS_REGION=us-east-1` (default).  Cross-region
   inference profiles (the `us.` prefix on model IDs) give higher
   quotas; if you'd rather pin to one region, drop the prefix
   in `MODEL_OPUS` / `MODEL_SONNET`:
   ```bash
   MODEL_OPUS=bedrock/anthropic.claude-opus-4-5-20251101-v1:0 ./run.sh
   ```

#### Direct Anthropic setup (`PROVIDER=anthropic`)

```bash
export ANTHROPIC_API_KEY=sk-ant-...
PROVIDER=anthropic ./run.sh
```

Same model defaults as Bedrock minus the `bedrock/...` prefix.
Useful when Bedrock access is delayed and you want to smoke-test
the rig.

### 3. Run the evolution

```bash
# Smoke test — 5 iterations, ~5 min wall-time + LLM calls.  Use
# this to verify the loop works before paying for real iterations.
ITERATIONS=5 ./run.sh

# Pilot — 50 iterations, ~3-4 wall hours, ~$5-10 in Opus calls.
./run.sh

# Production — 200 iterations, ~15 wall hours, ~$20-40.
ITERATIONS=200 ./run.sh
```

Per-run artifacts (candidate sources, prompt logs, scores) land in
`evo/evolve/runs/<timestamp>/`.  That directory is gitignored — keep
the interesting candidates by copying them out before re-running.

### 4. Promote the winner

After the run finishes, the best candidate is at
`evo/evolve/runs/<timestamp>/best/program.rs` (OpenEvolve's
convention).  To adopt it:

```bash
# Diff against the current EVOLVE-BLOCK in path_effective.rs to see
# what changed:
diff <(sed -n '/EVOLVE-BLOCK-START/,/EVOLVE-BLOCK-END/p' \
        src/dual/path_effective.rs) \
     <(sed -n '/EVOLVE-BLOCK-START/,/EVOLVE-BLOCK-END/p' \
        evo/evolve/runs/<ts>/best/program.rs)

# Apply by hand (splice the new EVOLVE-BLOCK into path_effective.rs)
# or use the same splice logic from evaluator.py:
.venv/bin/python -c "
import sys; sys.path.insert(0, 'evo/evolve')
from evaluator import extract_evolve_block, splice_evolve_block
from pathlib import Path
target = Path('src/dual/path_effective.rs')
new = extract_evolve_block(Path('evo/evolve/runs/<ts>/best/program.rs').read_text())
target.write_text(splice_evolve_block(target.read_text(), new))
print('promoted')
"

# Rebuild + retest:
cargo test --release --lib
cargo build --release --bin sat
```

## Inspecting / debugging

### Evaluator stand-alone

The evaluator works on any candidate file, not just OpenEvolve
outputs.  Use this to baseline the current code or sanity-check
a candidate by hand:

```bash
# Score the baseline (unchanged initial_program.rs):
uv run evo/evolve/evaluator.py evo/evolve/initial_program.rs --json

# Only run the smoke tier (~10s, no LLM cost):
uv run evo/evolve/evaluator.py evo/evolve/initial_program.rs \
    --tier smoke --json
```

### LiteLLM proxy log

`run.sh` writes the proxy's stderr to `runs/.litellm.log`.  Check
there if requests are failing — auth issues, model-id typos, and
rate-limit responses all surface in that file.

### Worktree leaks

Each evaluator invocation creates `/tmp/openevolve-eff-*` and
cleans it up in a `finally` block.  If a process gets `kill -9`'d
mid-evaluation, the worktree may persist.  Periodically:

```bash
git worktree list
git worktree prune
rm -rf /tmp/openevolve-eff-*
```

## Cost / time estimates

Per evaluator invocation (worst case, full tier hits TIMEOUTs):

- Cargo build (incremental, in worktree): ~5-10s
- Smoke tier:  ~10s
- Quick tier:  ~50s  (only if smoke passes)
- Full tier:   ~4min (only if quick passes)
- **Total**: ~5 min for a strong candidate, <30s for a failing one

LLM token cost per iteration (Opus on Bedrock as of late 2025):

- Mutation prompt: ~3K input + 1K output → ~$0.10 per call
- Plus ~$0.05 if `use_llm_feedback: true` (config default) and
  the candidate failed (LLM critiques + proposes fix)
- **Per 50-iter run**: ~$5-10
- **Per 200-iter run**: ~$20-40

Wall-time per run scales with evaluator time, not LLM time
(evaluator runs synchronously, ~5 min/candidate average):

- 50 iters: ~4 hours
- 200 iters: ~15 hours

## Known limitations

- **Single-host scoring**: timing measurements are sensitive to load
  on the eval machine.  Don't run other CPU-intensive work in
  parallel or fitness will be noisy.
- **No multi-seed averaging**: each candidate is scored on one run.
  CDCL has determinism (we set seeds) but Luby restart cadence
  interacts with wall-clock timeouts.  For a more rigorous final
  ranking, re-score top-K candidates 3× and use the median.
- **Soundness check is via cross-reference with the curated index**,
  not from-scratch SAT/UNSAT verification.  Trust the curated
  `status` fields as ground truth (they came from CaDiCaL).  If a
  mutation produces a different verdict than the curated status,
  `MISMATCH` row → fitness 0.
