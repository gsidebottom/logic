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
| **RoundRobin n16_d13**| **62,400**    | **493 KB**   | **~940 KB** flat     |
|                       | (= full static cover, 100%) |   |                      |

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
   `MAX_STATIC_COVER_POSITIONS = 2_000_000` v3-positions — if the
   formula's static cover would exceed the cap, this layer is
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
sat-cover-verify <cnf-file> <cert-file>           # default: SAT-based
sat-cover-verify --dfs <cnf-file> <cert-file>     # legacy pruned DFS
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

## Completeness check: SAT-based verifier (default)

The completeness check — "every matrix path picks at least two
positions whose lits are complementary, witnessed by some cover
entry" — is itself a SAT problem.  Encode it as a CNF and feed it
to CaDiCaL.

### Encoding

For each clause `c` with arity `k_c`, allocate `k_c` boolean
variables `x_{c,0}, ..., x_{c, k_c−1}`.  Read `x_{c,a} = 1` as "the
matrix path picks alt `a` of clause `c`".

Add:

1. **At-least-one per clause** (path picks ≥1 alt per clause):
   `(x_{c,0} ∨ x_{c,1} ∨ ... ∨ x_{c, k_c−1})` for each `c`.

2. **At-most-one per clause** (path picks ≤1 alt per clause):
   `(¬x_{c,a} ∨ ¬x_{c,b})` for each `a < b` in clause `c`.

3. **Ban each implied cover pair**: for each cert var entry,
   iterate every (positive position, negative position) cross-product
   and add `(¬x_{c_p, l_p} ∨ ¬x_{c_n, l_n})`.

The expanded ban set is exactly the implied-pairs view of the
cert (all `K_pos × K_neg` per variable).  The encoding is built
once with `K_pos + K_neg` reads of the cert per variable, not
`K_pos × K_neg`.

### Decision

- **CaDiCaL returns UNSAT** → every matrix-path assignment
  contradicts some ban → the cert covers every matrix path →
  print `VALID UNSAT CERTIFICATE`, exit 0.
- **CaDiCaL returns SAT** → some `x_{c,a}` assignment satisfies
  exactly-one-per-clause and avoids every ban → uncovered matrix
  path exists → decode the model into the clause-by-clause alt
  selection, print it, exit 1.

### Why it's better than DFS

The DFS-based verifier is fundamentally exponential — it walks
the matrix tree pruning at each cover hit, but with `n` clauses
of arity `k` the tree has `k^n` leaves.  On PHP-5-4 (5 clauses
of arity 4 + 20 negation chains) the pruning isn't tight enough
and the DFS hangs for minutes.

The SAT-based verifier reuses 30 years of conflict-driven
backjumping and clause learning to find the uncovered path (or
prove there isn't one) — and on PHP-style problems where CaDiCaL
is strong, this is orders of magnitude faster than the DFS.
Quick measurements (May 2026, release build):

| Input                  | DFS verifier  | SAT verifier (CaDiCaL) |
|------------------------|---------------|-------------------------|
| tiny (4-cls UNSAT)     | <1 ms         | <1 ms                   |
| PHP-3-2                | <1 ms         | <1 ms                   |
| PHP-4-3                | 3 ms          | <1 ms                   |
| PHP-5-4                | hangs (4+min) | <1 ms                   |
| RoundRobin n16_d13     | hangs         | hangs (see below)       |

The SAT-based verifier is now the default.  Pass `--dfs` to fall
back to the explicit pruned DFS — useful for tiny inputs where you
want maximally simple verification logic, or as a sanity check
against a SAT-side bug.

### Verifier hardness is bounded below by original-problem hardness

A subtle but important property of the SAT-based verifier on
**static-cover** certs (= certs containing every complementary
pair in F's matrix):

> If the cert is the full static cover of F, then the
> verification SAT instance is *equivalent* to F itself.

Why: the encoded CSP says "pick one alt per clause, avoiding
every ban".  A satisfying assignment is a matrix path that
includes no cover pair.  When the cover is the full static cover
of F, this is exactly a matrix path with no complementary pair —
i.e., a satisfying assignment for F.  CSP is UNSAT iff F is
UNSAT, and the proof difficulty matches.

For inputs whose UNSAT proof is structurally easy for CDCL
(PHP-family, most SAT-competition UNSAT instances), the SAT
verifier inherits that easiness and runs in <1 ms.  For inputs
where the UNSAT proof is *hard* for CDCL (RoundRobin n16_d13
takes minutes for CaDiCaL even directly on the CNF), the SAT
verifier inherits that hardness — there is no shortcut from
verifying the cover.

This is fundamental rather than an artifact of the encoding:
any sound verifier capable of checking arbitrary covers must, in
the worst case, do work proportional to the underlying UNSAT
proof.  The win the SAT-based approach offers is *delegating
that work to a vetted CDCL solver instead of an exponential
explicit DFS*.

A specialized format that embeds resolution-style replay info
(beyond just the cover-pair list) could break this barrier, at
the cost of larger certs and more prover-side bookkeeping —
e.g., DRAT-style verifiers run in time linear in the proof
trace.  An experimental `--emit-drat` flag exists for this
purpose; see [`drat_emission.md`](drat_emission.md).  It works
on small inputs but has known incompleteness on PHP-family and
RoundRobin-style problems where the matrix-method's non-
resolution inference paths can't be fully captured as RUP-valid
clauses.

### Soundness considerations

The SAT-based verifier *does* add a SAT solver (CaDiCaL) to the
trusted base, which is bigger surface area than the DFS.  But:

- CaDiCaL is already a dependency of this codebase (used in
  cross-checking) and has been vetted as a SAT-competition
  reference implementation.
- The encoding is short (~40 lines) and easy to inspect.
- A bug in CaDiCaL would have to falsely report UNSAT — i.e.
  declare a SAT instance unsatisfiable — to make this verifier
  wrongly accept an incomplete cert.  This is the SAT-solver
  bug class with the most external attention.

If even CaDiCaL is too much trusted base for your use case, run
the verifier with `--dfs` on tiny inputs.

## What the verifier checks

### 1. Per-entry validity (linear pass)

For each cert var-entry `v X + ... - ...`:
- All positions `<c>:<l>` have `c < num_clauses` and `l < |F[c]|`.
- Positions after `+` actually visit `+X` in the complement-NNF
  walk (i.e., `−F[c][l] == +X`).
- Positions after `-` actually visit `−X`.
- Both the positive and negative position sets are non-empty
  (otherwise the entry implies no pairs).

If any entry fails this, the cert is rejected immediately.

### 2. Completeness

Two algorithms are implemented, both checking the same property
("every matrix path is covered"):

- **SAT-based (default)** — encode the negation of cert
  completeness as a CNF and feed to CaDiCaL.  See the [SAT-based
  verifier](#completeness-check-sat-based-verifier-default)
  section above for the encoding and the speed numbers.

- **Pruned DFS (`--dfs`)** — explicit walk of the matrix tree.
  Per cert var-entry, track how many positive-side positions and
  how many negative-side positions are currently matched by the
  partial.  A running `active_var_count` counts vars with both
  polarities matched — when `> 0`, prune the subtree.  On
  backtrack, the state is reversed.  Exponential worst case;
  hangs on PHP-5-4 and up.

## Soundness

The verifier doesn't trust the prover's controllers (CDCL, Effective
layer, bubble-up, learned clauses). Its surface area is:

- DIMACS parsing (`parse_dimacs`, ~30 lines).
- Cert parsing (`parse_cert`, ~50 lines).
- Per-entry validation (`validate_entry`, ~30 lines).
- SAT-based completeness check (`sat_verify`, ~45 lines around
  the CaDiCaL encoding).
- Pruned DFS (`CoverDfs::verify` + `dfs`, ~90 lines), used when
  `--dfs` is passed.

If the verifier and prover disagree, the cert is wrong. (Or the
verifier has a bug — but the verifier is small enough to inspect by
eye; see `src/bin/sat_cover_verify.rs`.)

## Limitations and future work

1. **Static cover cap (`MAX_STATIC_COVER_POSITIONS = 2_000_000`).**
   Formulas whose static structural cover would require more than
   2M positions in the v3 cert fall back to CDCL-conflict-only
   emission, which can still be partial.  Most SAT-competition
   inputs fit easily — even RoundRobin n16_d13 needs only 63,960
   positions and the full static cover is just 62,400 pairs.
   Raising the cap is straightforward, but beyond a few million
   positions the cert file approaches GB sizes — at which point
   better long-term solutions are compressed cert formats (e.g.
   trie-structured) or a smarter cover-derivation algorithm that
   picks a minimal sub-cover rather than enumerating every pair.

2. **Verifier hardness is lower-bounded by original-problem
   hardness.**  For static-cover certs, the SAT verifier's CSP
   is equivalent to F (see "Verifier hardness is bounded below
   by original-problem hardness" above).  RoundRobin n16_d13's
   cert has 62,400 pairs and verifies-in-principle, but the
   verification SAT instance is itself a structured CSP that
   CaDiCaL doesn't crack in a usable budget — same hardness
   wall as solving RoundRobin directly with CaDiCaL.  Breaking
   this wall requires a richer cert format that embeds
   resolution-style replay info (DRAT-equivalent), not just the
   complementary-pair list.

3. **SAT-encoding size on huge certs.** The default SAT-based
   verifier expands every implied pair into one ban clause, so
   the encoding has `Σ K_pos×K_neg` clauses (the flat-pair count).
   On RoundRobin n16_d13 this is 62,400 ban clauses — small for
   CaDiCaL.  A cert with millions of implied pairs would push the
   encoding into hundreds of MB; if that ever becomes a real
   problem, switch to per-entry encoding: introduce auxiliary
   vars `pos_picked_X` = OR of `x_{c,l}` over var X's positive
   positions, same for negative, then ban `pos_picked_X ∧
   neg_picked_X` per var — encoding size becomes linear in
   positions, not pairs.

4. **Preprocessed input.** If `--preprocess` was on, the cert
   references the preprocessed CNF's clause indices, not the input
   CNF's. The verifier currently expects the input CNF. Either
   re-run with `--no-preprocess`, or extend the cert format to embed
   the preprocessed CNF (so the verifier reads it from the cert
   file).

5. **`smart` doesn't get the static cover.** Currently only
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
# sat-cover-verify cert v3
# source: tiny.cover backend=smart preprocess=off
v 1 + 2:0 3:0 - 0:0 1:0
v 2 + 1:1 3:1 - 0:1 2:1
# verdict UNSAT (2 vars, 8 implied pairs)

$ sat-cover-verify tiny.cnf tiny.cover
c F: vars=2 clauses=4
c cert: 2 vars, 8 positions, 8 implied pairs
c per-entry validity: OK (2 entries)
c completeness: OK via SAT (0.1ms, encoding: 8 vars 16 clauses)
VALID UNSAT CERTIFICATE
$ echo $?
0
```

## Worked example: PHP-5-4 (where the SAT verifier shines)

PHP-5-4 has 20 vars and 45 clauses.  Static cover is 80 implied
pairs.  The pruned DFS hangs for 4+ minutes on this input; the
SAT-based verifier confirms in <1 ms:

```bash
$ sat --backend cdcl --no-preprocess --emit-cover php54.cover < php54.cnf
c backend: matrix.cdcl
c UNSAT in 2.0ms
s UNSATISFIABLE

$ sat-cover-verify php54.cnf php54.cover
c F: vars=20 clauses=45
c cert: 20 vars, 100 positions, 80 implied pairs
c per-entry validity: OK (20 entries)
c completeness: OK via SAT (0.2ms, encoding: 100 vars 195 clauses)
VALID UNSAT CERTIFICATE

$ sat-cover-verify --dfs php54.cnf php54.cover
# ... runs for many minutes, eventually finishes or hits Ctrl-C
```

The pigeon-hole structure CDCL handles trivially also makes the
matrix-path CSP easy for CaDiCaL — the SAT verifier finishes
in microseconds.

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
c cert: 1 vars, 2 positions, 1 implied pairs
c per-entry validity: OK (1 entries)
c SAT-based completeness: incomplete (0.1ms)
INCOMPLETE CERT: matrix path not covered by any entry
  uncovered path (clause:lit_idx → lit): 0:0=-1 1:1=-3
INVALID CERTIFICATE (incomplete)
$ echo $?
1
```

The SAT search emitted one cover event before finding an uncovered
SAT path; the cert is partial by construction. The verifier
extracts the uncovered matrix path from CaDiCaL's satisfying model
and reports it, confirming the cert wouldn't suffice as a UNSAT
proof.

## Failure modes the verifier catches

- **Per-entry corruption** — a position points at a non-existent
  clause or lit index, or a position's visited lit doesn't match
  the entry's polarity declaration.
- **Empty positive or negative side** — an entry that doesn't
  imply any pairs (probably a writer bug).
- **Incomplete cert** — the cert misses some matrix path; the
  verifier surfaces the specific uncovered choice sequence
  (decoded from CaDiCaL's satisfying model under the SAT
  backend, or from the DFS state under `--dfs`).
- **Format errors** — unrecognized line, bad position token,
  position-before-marker, etc.

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
