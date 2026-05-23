# Cover certificates and independent UNSAT verification

## Why

The matrix method certifies CNF unsatisfiability by exhibiting a
*complementary cover of all matrix paths*. A "matrix path" picks one
literal from each clause; F is UNSAT iff every such path contains some
complementary pair `(X, ¬X)`. The cover is the set of complementary
pairs the search discovered — together they constitute a sound,
replay-able UNSAT proof.

This proof is normally an *internal artifact* of the search: the
`BacktrackWhenCoveredController` detects each complementary pair, the
search uses it to prune the subtree, and the cover info is discarded.
The `sat --emit-cover` flag and the `sat-cover-verify` binary expose
that proof for independent third-party verification.

Independent verification matters because:

- The prover has known soundness pitfalls (e.g. the bubble-up bug in
  the `effb` family — see `src/nnf_arena.rs::for_each_path_prefix`).
  A separate verifier sidesteps the prover's controllers entirely.
- For UNSAT verdicts on problems where no reference solver (CaDiCaL,
  cdcl) has produced an answer in budget (e.g. the unresolved
  RoundRobin entries in the SAT-competition database), an
  independently-checkable proof is the only way to claim the result
  with confidence.

## Cert format (v3 — var-grouped)

A cert is a UTF-8 text file with one entry per CNF variable:

| Line                                                            | Meaning                              |
|-----------------------------------------------------------------|--------------------------------------|
| `# anything`                                                    | comment (skipped)                    |
| `v <var> + <c>:<l>[,<l>...] ... - <c>:<l>[,<l>...] ...`         | per-variable position list           |

Each variable line lists, after `+`, all positions where the
matrix-method's positive lit `+var` is visited, and after `-`, the
positions where `−var` is visited.  Pairs are **implicit**: every
`(positive_position, negative_position)` cross product is a
complementary cover pair.

Position tokens are clause-grouped: `<c>:<l1>,<l2>,...` means
positions `(c, l1), (c, l2), ...` — equivalent to writing
`c:l1 c:l2 c:l3` but more compact when a variable appears at
multiple alt-indices of the same clause.

A position `(c, l)` corresponds to the matrix-method engine
visiting the lit `−F[c][l]` (the engine walks the *complement*
NNF, so each visited lit is the negation of the original CNF lit).

### Compression vs flat per-pair format

A variable appearing at `K_pos` positive-side positions and `K_neg`
negative-side positions contributes `K_pos × K_neg` implied pairs
to the cover.  The v3 cert stores `K_pos + K_neg` positions and
expands at verification time — quadratic-to-linear compression per
variable.

Concrete numbers from the test corpus (the implementation):

| Problem               | Implied pairs | v3 cert size | Hypothetical v2 size |
|-----------------------|---------------|--------------|----------------------|
| tiny (4 cls UNSAT)    | 8             | 200 B        | 200 B                |
| PHP-3-2               | 12            | 240 B        | 240 B                |
| PHP-4-3               | 36            | 500 B        | 700 B                |
| PHP-5-4               | 80            | 770 B        | 1.5 KB               |
| **RoundRobin n16_d13**| **62,400**    | **493 KB**   | **~940 KB** flat;   |
|                       |               |              | (full static cover ~5 MB) |

For very asymmetric problems like RoundRobin where one polarity
dominates, the savings are modest (~2×); for symmetric problems
with many positions per polarity, savings reach ~100×.

### Example: tiny UNSAT (`(a∨b)(a∨¬b)(¬a∨b)(¬a∨¬b)`)

```text
# sat-cover-verify cert v3
# source: tiny.cover backend=cdcl preprocess=off
v 1 + 2:0 3:0 - 0:0 1:0
v 2 + 1:1 3:1 - 0:1 2:1
# verdict UNSAT (2 vars, 8 implied pairs)
```

Var 1: positive lit `+1` (= original CNF `−1`) appears at clauses 2
and 3, alt-index 0.  Negative lit `−1` (= original `+1`) appears at
clauses 0 and 1, alt-index 0.  Implied pairs: `(2:0, 0:0)`,
`(2:0, 1:0)`, `(3:0, 0:0)`, `(3:0, 1:0)` — all 4 cross-products.
Var 2 contributes another 4.  Total 8 implied pairs, captured by 8
positions across 2 var lines.

### Deduplication

The prover accumulates positions per variable in `HashSet`s and
emits at finalization, so repeated cover events for the same pair
(common in CDCL where the same pair fires across many restarts) are
collapsed.

## Producing a certificate

```bash
sat --backend cdcl  --no-preprocess --emit-cover proof.cover < problem.cnf
sat --backend smart --no-preprocess --emit-cover proof.cover < problem.cnf
```

Only the `cdcl` and `smart` backends are supported — they use the
NNF engine with positions tracked, which the cert format requires.
The arena (`eff` / `effb`) and dual (`*_eff*`) backends emit cover
events through internal channels that bypass the file emitter, and
the arena engine doesn't track positional info at all.

Caveat: `--preprocess` works (the cert references positions in the
preprocessed CNF), but the verifier expects the original CNF on its
CLI. Use `--no-preprocess` when the cert needs to be checked against
the input CNF. (Adding cert-side preprocessed-CNF dump is a
worthwhile follow-up.)

### Backend choice — `cdcl` (fast, often complete) vs `smart` (always complete, slow)

Both supported backends emit cover pairs at every covered prefix the
matrix DFS detects.  The difference is what they do on CDCL-style
propagation conflicts plus what additional sources they tap.

#### `cdcl` — three layers of cover emission

1. **BacktrackWhenCovered events** — every covered prefix the
   matrix DFS hits during search fires a `k` pair, same as `smart`.
2. **Conflict cover with provenance** — every CDCL propagation
   conflict triggers `emit_conflict_cover`, which computes the
   *complete resolution provenance* (the set of all original CNF
   clauses involved in the conflict's 1UIP resolution chain, with
   transitive expansion of any learned clauses encountered).  For
   each original `Q` in the provenance, the emitter iterates Q's
   alts and grounds each alt's complement through the trail's
   `Reason::Implied(R)` chain back to DFS-pushed lits (or to
   positions reached via Q's per-alt case-splits).  Each ground
   emits one `k` pair per case-split, deduped at the writer.
3. **Static structural cover** — at `for_nnf_with_cover` time,
   before the search starts, enumerate every complementary pair in
   `F` (every `(p1, p2)` with lit at p1 = `X`, lit at p2 = `¬X`).
   This is the matrix-method's natural "connection" set; for any
   UNSAT `F` it covers every matrix path by definition.  Capped at
   `MAX_STATIC_COVER_PAIRS = 100_000` — if the formula's static
   cover would exceed the cap (RoundRobin-scale), this layer is
   skipped and the cert relies on layers 1 + 2 only (which may be
   partial).

The combination makes `cdcl --emit-cover` produce **complete certs
on all small-to-medium UNSAT inputs** the static cover can fit
(PHP family up through PHP-5-4, etc.), and partial certs above
that.  Even where partial, the cert is much richer than before
(thousands to tens-of-thousands of pairs) and can serve as raw
material for further analysis or a heavier verifier.

#### `smart` — pure matrix DFS, always-complete cert

Pure matrix DFS with propagation-aware prod-ord but no learned
clauses.  Every covered prefix it encounters fires a cover event.
No static-cover overlay, no conflict-cover synthesis.  Always
produces a sound, complete cert when the search itself finishes;
on hard inputs the *search* may not finish in time.

#### Rule of thumb

| Input size              | Try first         | Fallback                  |
|-------------------------|-------------------|---------------------------|
| Tiny / toy UNSAT        | `cdcl`            | (rarely needed)           |
| PHP-3-2 .. PHP-5-4      | `cdcl`            | smart (slower search)     |
| Mid-size structured     | `cdcl`            | accept partial cert       |
| RoundRobin-scale UNSAT  | `cdcl` (partial)  | currently no full cert    |

`cdcl --emit-cover` is the recommended default: fast UNSAT
verdict, fast cert production for any formula whose static-cover
size is under the cap, full provenance + static cover combined.

## Verifying

```bash
sat-cover-verify <cnf-file> <cert-file>
```

Exit codes:
- **0** — `VALID UNSAT CERTIFICATE`. Cert is well-formed and every
  matrix path is covered.
- **1** — invalid cert (per-pair malformed OR an uncovered matrix
  path exists).
- **2** — I/O or argv error (file missing, parse error, etc.).

The verifier prints diagnostic info to stderr (`c` lines) and the
verdict to stdout (`VALID UNSAT CERTIFICATE` or `INVALID
CERTIFICATE (...)`), so it's pipeline-friendly.

## What the verifier checks

### 1. Per-pair validity (linear pass)

For each cert pair:
- Both `<c>:<l>` positions have `c < num_clauses` and `l < |F[c]|`.
- The lits at the two positions are genuinely complementary: same
  variable, opposite signs.
- Pair is not a self-pair (`a != b`).

If any pair fails this, the cert is rejected immediately.

### 2. Completeness (pruned DFS over matrix paths)

Walk the matrix tree clause by clause. Track per cover pair:
- `remaining`: number of constraints not yet matched. Initially 2
  (one per cover position); decremented when a position is matched.
- `compatible`: still consistent with the current partial?
- A counter `covered_count` of pairs with `compatible && remaining
  == 0` — pairs currently proving the subtree covered.

At each DFS step:
- Choose a lit-index for the next clause.
- For each cover pair that constrains this clause:
  - Match (decrement `remaining`) OR invalidate (`compatible = false`).
- If `covered_count > 0`, prune the subtree — some pair's two
  positions are both in the current partial, so every extension has
  the `(X, ¬X)` pair.
- If we reach a full matrix path (all clauses chosen) without
  pruning, the cert is incomplete and the verifier reports the
  uncovered path.

On backtrack, the per-pair state changes are undone exactly so the
counters stay consistent.

## Soundness

The verifier doesn't trust the prover's controllers (CDCL, Effective
layer, bubble-up, learned clauses). Its surface area is:

- DIMACS parsing (`parse_dimacs`, ~30 lines).
- Cert parsing (`parse_cert`, ~25 lines).
- Per-pair validation (`validate_pair`, ~12 lines).
- Pruned DFS (`CoverDfs::verify` + `dfs`, ~90 lines).

If the verifier and prover disagree, the cert is wrong. (Or the
verifier has a bug — but the verifier is small enough to inspect by
eye; see `src/bin/sat_cover_verify.rs`.)

## Limitations and future work

1. **Static cover cap (`MAX_STATIC_COVER_PAIRS = 100_000`).**
   Formulas whose static structural cover exceeds the cap (e.g.
   RoundRobin_n16_d13's ~62M-pair static cover) fall back to
   CDCL-conflict-only emission, which can still be partial.  Raising
   the cap is straightforward but the corresponding cert file would
   grow to hundreds of MB to GB; better long-term solutions are
   compressed cert formats (e.g. trie-structured) or a smarter
   cover-derivation algorithm that picks a minimal sub-cover
   rather than enumerating every pair.

2. **Verifier completeness DFS is exponential in worst case.**
   Even with a complete cert, the verifier walks the matrix tree
   pruning at each pair-match.  On medium-large formulas (PHP-5-4
   and up) the pruning isn't always tight enough to keep the DFS
   polynomial, and the verifier can take many minutes.  Two
   complementary improvements: (a) build a constraint-trie of
   the cover pairs so each DFS node's match-check is O(log #pairs)
   instead of O(#pairs); (b) reorder DFS clauses by "hits most
   pairs" heuristic to prune faster.

3. **Preprocessed input.** If `--preprocess` was on, the cert
   references the preprocessed CNF's clause indices, not the input
   CNF's. The verifier currently expects the input CNF. Either
   re-run with `--no-preprocess`, or extend the cert format to embed
   the preprocessed CNF (so the verifier reads it from the cert
   file).

4. **`smart` doesn't get the static cover.** Currently only
   `cdcl --emit-cover` does up-front static cover enumeration
   (smart relies on its own cover-event emission).  For tiny inputs
   where smart could benefit from a guaranteed-complete cert, the
   static cover code path could be hoisted into `SmartController` —
   straightforward extension.

## Worked example: tiny UNSAT

```bash
$ cat tiny.cnf
p cnf 2 4
1 2 0
1 -2 0
-1 2 0
-1 -2 0

$ sat --backend smart --no-preprocess --emit-cover tiny.cover < tiny.cnf
c parsed 2 variables, 4 clauses
c backend: matrix.smart
c UNSAT in 0.5ms
s UNSATISFIABLE

$ cat tiny.cover
# sat-cover-verify cert v2
# source: tiny.cover backend=smart preprocess=off
k 0:0 2:0
k 0:0 3:0
k 2:1 3:1
k 1:1 2:1
k 1:0 2:0
k 1:0 3:0
k 0:1 3:1
k 0:1 1:1
# verdict UNSAT (8 distinct pairs)

$ sat-cover-verify tiny.cnf tiny.cover
c F: vars=2 clauses=4
c cert: 8 cover pairs
c per-pair validity: OK (8 pairs)
c completeness: OK (0.0ms)
VALID UNSAT CERTIFICATE
$ echo $?
0
```

## Worked example: cdcl partial cert (PHP-4-3)

Showing the learned-clause limitation in action.  PHP-4-3 has only
12 vars and 22 clauses — still tiny — but CDCL's propagation chain
already involves learned clauses, so `cdcl --emit-cover` leaves the
cert partial:

```bash
$ sat --backend cdcl  --no-preprocess --emit-cover php43.cdcl < php43.cnf
$ sat --backend smart --no-preprocess --emit-cover php43.smart < php43.cnf

$ wc -l php43.cdcl php43.smart
  34  php43.cdcl       # ~30 pairs
  40  php43.smart      # 36 pairs

$ sat-cover-verify php43.cnf php43.cdcl
c cert: 30 cover pairs
c per-pair validity: OK (30 pairs)
INCOMPLETE CERT: matrix path not covered by any entry
  uncovered path (clause:lit_idx → lit): 0:0=-1 1:0=-4 2:1=-8 ...
INVALID CERTIFICATE (incomplete)

$ sat-cover-verify php43.cnf php43.smart
c cert: 36 cover pairs
c per-pair validity: OK (36 pairs)
c completeness: OK (3.1ms)
VALID UNSAT CERTIFICATE
```

cdcl's cert is sound for the 30 pairs it emits (per-pair validation
passes), but the verifier finds a matrix path none of those 30 pairs
cover.  Smart's 36 pairs are enough.

## Worked example: SAT problem (cert must FAIL)

```bash
$ cat sat_simple.cnf
p cnf 3 2
1 2 0
-1 3 0

$ sat --backend smart --no-preprocess --emit-cover sat.cover < sat_simple.cnf
c SAT in 0.6ms
s SATISFIABLE
v 1 2 3 0

$ sat-cover-verify sat_simple.cnf sat.cover
c F: vars=3 clauses=2
c cert: 1 cover pairs
c per-pair validity: OK (1 pairs)
INCOMPLETE CERT: matrix path not covered by any entry
  uncovered path (clause:lit_idx → lit): 0:0=-1 1:1=-3
INVALID CERTIFICATE (incomplete)
$ echo $?
1
```

The SAT search emitted one cover event before finding an uncovered
SAT path; the cert is partial by construction. The verifier reports
the specific uncovered matrix path, confirming the cert wouldn't
suffice as a UNSAT proof.

## Failure modes the verifier catches

- **Per-pair corruption** — cover positions point at non-existent
  clauses or lit indices, or the cover pair isn't actually
  complementary.
- **Incomplete cert** — the cert misses some matrix path; the
  verifier surfaces the specific uncovered choice sequence.
- **Format errors** — unrecognized line.

What the verifier does NOT catch (out of scope):
- A wrong CNF on the command line (it just verifies the cert against
  whatever CNF you hand it).
- A correct cert for a *different* CNF (same caveat).

## See also

- `src/bin/sat.rs` (`write_cover_entry`, `CoverWriter`,
  `--emit-cover` flag wiring).
- `src/bin/sat_cover_verify.rs` (the verifier itself).
- `src/controller/backtrack.rs::BacktrackWhenCoveredController`
  (where covers are detected during search).
- `src/matrix.rs::CoveredPathPrefix` (the in-memory event the
  prover emits; the cert format keeps only its `cover` field).
