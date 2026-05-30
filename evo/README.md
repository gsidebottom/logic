# `evo/` — self-contained benchmark set

A small (~750 KB) bundle of 81 SAT instances curated for evaluating the
matrix-method solver's `eff` backend.  Every file referenced by
`curated_struct_eff.jsonl` lives in this directory, so the suite is
**stand-alone**: no GBD database download, no `$BENCH_DIR` env var,
no network access needed.

## Contents

```
evo/
├── README.md                       (this file)
├── curated_struct_eff.jsonl         81-record index (relative xz_paths)
└── problems/
    └── <81 × *.cnf.xz>             xz-compressed DIMACS CNFs
```

The index has one JSON object per line.  Each record describes a
CNF instance plus the verified verdict CaDiCaL produced when the set
was originally curated:

```json
{
  "hash":     "3c917e77148a8f645a60d28d8fb53fe8",
  "filename": "bench_16516.smt2.cnf.xz",
  "xz_path":  "problems/bench_16516.smt2.cnf.xz",
  "checked_utc": "2026-05-28T19:43:57Z",
  "nvars":    184,
  "nclauses": 416,
  "status":   "UNSAT",
  "time_ms":  194.7
}
```

`xz_path` is **relative**: `run_benchmark.py` resolves it against
the directory the index file lives in, so the set works whether you
invoke it from the repo root, from `evo/`, or from anywhere else on
the filesystem.

### Composition (as of generation)

| Status   | Count |
|----------|-------|
| SAT      | (varies by backend / timeout — see your `curated_struct_eff.jsonl`) |
| UNSAT    | "       " |
| TIMEOUT  | "       " |

The `status` field reflects CaDiCaL's verdict at curation time.
`time_ms` is the wall-clock CaDiCaL solve time on the original
curation host — useful as a difficulty hint but not a binding ground
truth (re-curate with a fresh `--verify-unsat` pass for higher
confidence; see `tools/gbd/curate.py`).

## Running the suite

### 1. Make sure the Python env + `sat` binary are built

```bash
# From the repo root:
./setup.sh                              # Python venv (uv-managed)
cargo build --release --bin sat         # the solver
```

### 2. Run `run_benchmark.py` against the index

```bash
# Either activate the venv:
source .venv/bin/activate
tools/gbd/run_benchmark.py \
    --index evo/curated_struct_eff.jsonl \
    --output-dir evo/results \
    -b eff -t 60 -j 10

# Or use `uv run` (no activation needed):
uv run tools/gbd/run_benchmark.py \
    --index evo/curated_struct_eff.jsonl \
    --output-dir evo/results \
    -b eff -t 60 -j 10
```

`--output-dir evo/results` keeps every artifact (`.md` report, `.json`
sidecar, cactus `.png`) bundled alongside the index and CNFs — handy
if you want to share or check in a full reproducible run.  Without
`--output-dir` the auto-named files land in `doc/` (the repo-wide
default).  Pass a specific `.md` path with `-o` to override the
auto-naming entirely.

### 3. Sweep `--eff-tau` (or any other backend knob)

```bash
uv run tools/gbd/sweep_eff_tau.py \
    --index evo/curated_struct_eff.jsonl \
    --backend eff --timeout 60 -j 10 \
    --taus 0,0.5,1,2,inf \
    --out-dir evo/sweeps/eff_60s
```

The same path-resolution logic applies — each per-τ
`run_benchmark.py` invocation reads `xz_path` relative to `evo/`.
Point `--out-dir` anywhere you like; the example above keeps the
sweep results next to the benchmark set itself.

## How this directory was built

Generated once by hand from a larger curated index that lived under
`/Users/greg/projects/curated_benchmarks/curated_struct_eff.jsonl`.
The build steps (kept for reproducibility):

1. Read every record from the source JSONL.
2. Copy the `.cnf.xz` file each record's `xz_path` points at into
   `evo/problems/`, stripping the GBD content-hash prefix from the
   filename (all 81 filenames were unique without the prefix; the
   hash is still preserved per-record in the `"hash"` field).
3. Rewrite each record so `xz_path` is `problems/<filename>`
   (relative to the index file's directory).
4. Save the rewritten index as `evo/curated_struct_eff.jsonl`.

To regenerate against a different source index:

```bash
python3 <<'EOF'
import json, shutil
from pathlib import Path
src = Path('/path/to/source.jsonl')
dst = Path('/Users/greg/projects/logic/evo')   # or wherever
(dst / 'problems').mkdir(parents=True, exist_ok=True)
out = []
for line in src.read_text().splitlines():
    if not line.strip(): continue
    r = json.loads(line)
    name = r['filename']
    shutil.copy2(r['xz_path'], dst / 'problems' / name)
    r['xz_path'] = f'problems/{name}'
    out.append(json.dumps(r))
(dst / src.name).write_text('\n'.join(out) + '\n')
EOF
```

## Why this set?

The `_struct_eff` suffix indicates these were selected as
**structurally-interesting** instances for the `eff` backend
(matrix.eff / greedy_eff): mix of SAT and UNSAT, mix of families
(VanDerWaerden, Steiner, Break, 3col, pigeonhole, bench/SMT-encoded,
…), with sizes that fit a 60s-per-instance × 10-worker budget on a
typical laptop (~10 min wall-clock for the full sweep).

It's a fixed snapshot — checked into the repo so any contributor can
reproduce the same numbers on the same hardware without depending on
external benchmark mirrors.
