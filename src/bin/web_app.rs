#![allow(clippy::type_complexity)]

use axum::{
    extract::{Json, Query, State},
    http::Method,
    routing::{delete, get, post},
    Router,
};
use logic::matrix::{PathClassificationHandle, Matrix, NNF, Lit};
use logic::jqlib::{split_file, join_file, split_boxes, join_boxes, resolve_preamble, parse_box_decl, box_formula};
use logic::boxes::compile::{compile_box, Table};
use logic::boxes::expand::{expand_box_calls, atomize_box_calls, Arg, BoxCall, BoxSig};
use logic::boxes::compile::{compile_box_polarity, implication_box, ArgBinding};
use logic::boxes::{Engine, TableBox, Verdict};
use serde::{Deserialize, Serialize};
use std::{collections::HashMap, path::PathBuf, sync::{Arc, Mutex}};
use tower_http::cors::{Any, CorsLayer};
use xq::{module_loader::PreludeLoader, run_query, Value as XqValue};

// ── App state ─────────────────────────────────────────────────────────────────

#[derive(Clone, Serialize)]
struct JqLibEntry {
    path:    String,
    name:    String,
    /// Other `.jq` files this library depends on.  Each entry is a filename
    /// in `lib/` (same form the loader accepts).  Resolved transitively and
    /// deduplicated when building a jq preamble; see [`resolve_preamble`].
    deps:    Vec<String>,
    /// Library source code (no dep header, no tests).
    content: String,
    /// Saved test filter.  Empty string if there are no tests.
    tests:   String,
    /// Box declarations (`name(p1;p2;…) [expose …]`) from the `# === boxes ===`
    /// block, kept out of `content`; compiled on load and on save.
    boxes:   Vec<String>,
}

const PREFIX_DETAIL_LIMIT: usize = 1000;

/// A deduplicated cover group: one unique complementary pair with stats about
/// how many path prefixes it covers.
#[derive(Clone, Default, Serialize)]
struct CoverGroup {
    pair: (Vec<usize>, Vec<usize>),
    count: usize,
    prefix_length_min: usize,
    prefix_length_max: usize,
    /// Full prefix position arrays — only populated when total prefix count ≤ PREFIX_DETAIL_LIMIT.
    prefixes: Vec<Vec<Vec<usize>>>,
}

fn pair_key(pair: &(Vec<usize>, Vec<usize>)) -> String {
    format!("{}|{}", pair.0.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","),
                     pair.1.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","))
}


/// Snapshot of an in-progress classify job (shared by valid, satisfiable, paths).
#[derive(Default, Clone)]
struct ClassifySnapshot {
    uncovered_paths:          Vec<String>,
    uncovered_path_positions: Vec<Vec<Vec<usize>>>,
    cover_groups:             Vec<CoverGroup>,
    group_map:                HashMap<String, usize>,
    total_prefix_count:       usize,
    classified_count:         f64,
    hit_limit:                bool,
    /// Set when preprocessing reduced the search target to a constant
    /// — `Some("TRUE")` for `Prod([])` (preprocessing alone proved
    /// the search target valid, i.e. the formula's question was
    /// answered without any matrix-method search) or `Some("FALSE")`
    /// for `Sum([])` (proved unsat).  `None` otherwise.  The UI uses
    /// this to display a message like "Preprocessing covered every
    /// path in the original matrix" when there are no concrete covers
    /// from the search to show.
    preprocessed_to:          Option<String>,
}

struct ClassifyJob {
    snapshot: ClassifySnapshot,
    total_path_count:         f64,
    start_time:               Option<std::time::Instant>,
    cancel:   Option<PathClassificationHandle>,
    running:  bool,
    error:    Option<String>,
    is_complement: bool,
    /// Set to `true` when the job's search ran on a preprocessed NNF
    /// rather than the matrix's raw `nnf` / `nnf_complement`.  Cover
    /// pairs and path positions in `snapshot` are already translated
    /// back to original-NNF positions so the UI can render them on
    /// the original formula's diagram; this flag is informational
    /// (e.g. for the cover-group display to label lemma covers).
    preprocessed: bool,
}

impl Default for ClassifyJob {
    fn default() -> Self {
        Self {
            snapshot: ClassifySnapshot::default(),
            cancel: None,
            running: false,
            error: None,
            is_complement: false,
            preprocessed: false,
            total_path_count: 0.0,
            start_time: None,
        }
    }
}

/// State for a CaDiCaL solver job.
#[derive(Default, Clone, Serialize)]
struct CaDiCaLJobResult {
    /// The assignment (if any). Each entry is [var_index, neg_bool].
    assignment:      Option<Vec<(u32, bool)>>,
    /// Learned clauses as raw cadical literal vectors.
    learned_clauses: Vec<Vec<i32>>,
    elapsed_secs:    f64,
}

#[derive(Default)]
struct CaDiCaLJob {
    result:   Option<CaDiCaLJobResult>,
    cancel:   Option<PathClassificationHandle>,
    running:  bool,
    error:    Option<String>,
}


#[derive(Serialize)]
struct CaDiCaLStatusResponse {
    result:       Option<CaDiCaLJobResult>,
    running:      bool,
    error:        Option<String>,
}

#[derive(Clone)]
struct AppState {
    jq_libs:     Arc<Mutex<Vec<JqLibEntry>>>,
    /// Boxes compiled from the loaded libraries' `# === boxes ===` declarations.
    compiled_boxes: Arc<Mutex<Vec<CompiledBox>>>,
    server_root: PathBuf,
    valid_job:   Arc<Mutex<ClassifyJob>>,
    sat_job:     Arc<Mutex<ClassifyJob>>,
    paths_job:   Arc<Mutex<ClassifyJob>>,
    cadical_valid_job: Arc<Mutex<CaDiCaLJob>>,
    cadical_sat_job:   Arc<Mutex<CaDiCaLJob>>,
}


/// Expand box calls (`name(a, b, …)`) against the compiled boxes.  Every
/// formula-taking handler runs this first, so the backends and the client's
/// live parser agree on what a formula with boxes means.
fn expand_formula(state: &AppState, formula: &str) -> Result<String, String> {
    let store = state.compiled_boxes.lock().unwrap().clone();
    expand_box_calls(formula, &|name| store.iter().find(|b| b.name == name).map(|b| BoxSig {
        params: b.vars.clone(), internals: b.internals.clone(), formula: b.formula.clone(),
    }))
}


/// A formula's box calls turned into atoms, with the compiled boxes they name.
#[derive(Clone)]
struct BoxContext {
    calls: Vec<BoxCall>,
    boxes: HashMap<String, CompiledBox>,
}

/// Atomize the box calls of `formula` (`BOXCALL_k` per call) and collect the
/// compiled boxes involved.  Returns the atomized text and the context.
fn build_box_context(state: &AppState, formula: &str) -> Result<(String, BoxContext), String> {
    let store = state.compiled_boxes.lock().unwrap().clone();
    let at = atomize_box_calls(formula, &|name| store.iter().find(|b| b.name == name).map(|b| BoxSig {
        params: b.vars.clone(), internals: b.internals.clone(), formula: b.formula.clone(),
    }))?;
    let mut boxes = HashMap::new();
    for c in &at.calls {
        if !boxes.contains_key(&c.name) {
            let cb = store.iter().find(|b| b.name == c.name).cloned().ok_or_else(|| format!("unknown box `{}`", c.name))?;
            boxes.insert(c.name.clone(), cb);
        }
    }
    Ok((at.text, BoxContext { calls: at.calls, boxes }))
}

/// Variable ids for a box-aware run: the atomized formula's variables plus
/// fresh ids for call arguments that occur only inside calls.
struct VarAlloc { index: HashMap<String, u32>, names: Vec<String> }
impl VarAlloc {
    fn new(m: &Matrix) -> VarAlloc { VarAlloc { index: m.ast.var_index.clone(), names: m.ast.vars.clone() } }
    fn id(&mut self, name: &str) -> u32 {
        if let Some(&i) = self.index.get(name) { return i; }
        let i = self.names.len() as u32;
        self.names.push(name.to_string());
        self.index.insert(name.to_string(), i);
        i
    }
    fn bind(&mut self, args: &[Arg]) -> Vec<ArgBinding> {
        args.iter().map(|a| match a {
            Arg::Const(b) => ArgBinding::Const(*b),
            Arg::Var { name, neg } => ArgBinding::Var { id: self.id(name), neg: *neg },
        }).collect()
    }
}

/// One call's tables over problem variables: rows of the box (`pos`) and of
/// its negation (`neg`), and the id of the atom standing for the call.
struct CallTables { atom: u32, pos: Vec<Vec<Lit>>, neg: Vec<Vec<Lit>> }

/// Instantiate every call of `ctx`; relabels the atoms in `m.ast.vars` with the
/// call text so path / model strings read `full_adder(x,y,c_in,s,c_out)`.
fn instantiate_calls(ctx: &BoxContext, m: &mut Matrix, alloc: &mut VarAlloc) -> Result<Vec<CallTables>, String> {
    let mut out = Vec::new();
    for call in &ctx.calls {
        let cb = ctx.boxes.get(&call.name).ok_or_else(|| format!("unknown box `{}`", call.name))?;
        let atom = *m.ast.var_index.get(&call.atom).ok_or_else(|| format!("internal: atom {} missing", call.atom))?;
        m.ast.vars[atom as usize] = call.label.clone();
        alloc.names[atom as usize] = call.label.clone();
        let b = alloc.bind(&call.args);
        let pos = cb.table.instantiate_args(&b)?;
        let neg = cb.table_neg.as_ref()
            .ok_or_else(|| format!("box `{}`: negative table unavailable (too many columns?)", call.name))?
            .instantiate_args(&b)?;
        out.push(CallTables { atom, pos, neg });
    }
    Ok(out)
}

/// Box-aware paths: a candidate uncovered path of the atomized matrix is kept
/// iff its literals (negated — model polarity) are consistent with the tables
/// of the box atoms it fixes: `atom'` on the path means the call holds (rows
/// of the box), `atom` that it fails (rows of the negation).
fn box_path_filter(ctx: &BoxContext, m: &mut Matrix) -> Result<Arc<dyn Fn(&[Lit]) -> bool + Send + Sync>, String> {
    let mut alloc = VarAlloc::new(m);
    let tables = instantiate_calls(ctx, m, &mut alloc)?;
    let nvars = alloc.names.len();
    Ok(Arc::new(move |path: &[Lit]| {
        let units: Vec<Vec<i32>> = path.iter().map(|l| { let v = l.var as i32 + 1; vec![if l.neg { v } else { -v }] }).collect();
        let mut eng = Engine::from_cnf(nvars, &units);
        for t in &tables {
            if let Some(l) = path.iter().find(|l| l.var == t.atom) {
                eng.add_box(TableBox::new(if l.neg { t.pos.clone() } else { t.neg.clone() }));
            }
        }
        eng.max_decisions = Some(1_000_000);
        matches!(eng.solve(), Verdict::Sat(_))
    }))
}

/// Occurrence polarities of each variable in an NNF: (positive, negative).
fn nnf_polarities(nnf: &NNF, out: &mut HashMap<u32, (bool, bool)>) {
    match nnf {
        NNF::Lit(l) => { let e = out.entry(l.var).or_insert((false, false)); if l.neg { e.1 = true } else { e.0 = true } }
        NNF::Sum(ch) | NNF::Prod(ch) => for c in ch { nnf_polarities(c, out); },
    }
}

/// The `boxes` backend for Valid? / Satisfiable?: keep box calls as atoms,
/// Tseitin-encode the (complemented) formula, tie each atom to its box with
/// `atom ⇒ rows(box)` and `¬atom ⇒ rows(¬box)` tables (only the polarities the
/// NNF uses), and run the row engine.  A model is reported as one "uncovered
/// path" in the UI's display polarity (the user negates to read the witness).
fn start_boxes_job(job_state: Arc<Mutex<ClassifyJob>>, state: &AppState, formula: &str, complement: bool) -> Result<(), String> {
    use logic::matrix::{format_lits, PathClassificationHandle};
    let (text, ctx) = build_box_context(state, formula)?;
    let mut matrix = Matrix::try_from(text.as_str()).map_err(|e| e.to_string())?;
    // `target` is the matrix the paths view shows; its uncovered paths, negated,
    // are models of ¬target (paths are falsification branches).  So the engine
    // searches models of the *other* NNF: NNF(φ) for Satisfiable?, NNF(¬φ)
    // (countermodels) for Valid?.
    let target = if complement { matrix.nnf_complement.clone() } else { matrix.nnf.clone() };
    let total_paths = target.path_count();
    let search = if complement { matrix.nnf.clone() } else { matrix.nnf_complement.clone() };
    let mut pol = HashMap::new();
    nnf_polarities(&search, &mut pol);
    let mut alloc = VarAlloc::new(&matrix);
    let tables = instantiate_calls(&ctx, &mut matrix, &mut alloc)?;
    let n_display = alloc.names.len();
    let names = alloc.names.clone();
    let atoms: std::collections::HashSet<u32> = tables.iter().map(|t| t.atom).collect();
    let mut next_var = n_display as i32 + 1;
    let (root, mut clauses) = logic::cadical::tseitin_encode(&search, &mut next_var);
    clauses.push(vec![root]);
    let mut engine = Engine::from_cnf((next_var - 1) as usize, &clauses);
    for t in tables {
        let (p, n) = pol.get(&t.atom).copied().unwrap_or((false, false));
        if p { engine.add_box(implication_box(t.pos, t.atom, true)); }
        if n { engine.add_box(implication_box(t.neg, t.atom, false)); }
    }
    let handle = PathClassificationHandle::new();
    engine.cancel = Some(handle.cancel_flag());
    {
        let mut job = match job_state.lock() { Ok(g) => g, Err(p) => p.into_inner() };
        job.cancel = Some(handle);
        job.total_path_count = total_paths;
        job.start_time = Some(std::time::Instant::now());
    }
    tokio::task::spawn_blocking(move || {
        let verdict = engine.solve();
        let mut job = match job_state.lock() { Ok(g) => g, Err(p) => p.into_inner() };
        match verdict {
            Verdict::Sat(model) => {
                let lits: Vec<Lit> = (0..n_display).filter(|v| !atoms.contains(&(*v as u32)))
                    .map(|v| Lit { var: v as u32, neg: model[v] }).collect();
                job.snapshot.uncovered_paths.push(format_lits(&lits, &names));
                job.snapshot.uncovered_path_positions.push(Vec::new());
            }
            Verdict::Unsat => {}
            Verdict::Unknown => { job.error = Some("boxes: search cancelled".into()); }
        }
        job.snapshot.classified_count = engine.stats.decisions as f64;
        job.running = false;
    });
    Ok(())
}

fn reset_and_start_boxes(job_state: &Arc<Mutex<ClassifyJob>>, state: &AppState, formula: &str, complement: bool) -> Json<serde_json::Value> {
    {
        let mut job = match job_state.lock() { Ok(g) => g, Err(p) => p.into_inner() };
        if let Some(c) = job.cancel.take() { c.cancel(); }
        *job = ClassifyJob::default();
        job.running = true;
        job.is_complement = complement;
    }
    if let Err(e) = start_boxes_job(job_state.clone(), state, formula, complement) {
        let mut job = match job_state.lock() { Ok(g) => g, Err(p) => p.into_inner() };
        job.running = false;
        job.error = Some(e);
    }
    Json(serde_json::json!({ "ok": true }))
}

#[derive(Deserialize)]
struct ExpandRequest { formula: String }

async fn expand_handler(State(state): State<AppState>, Json(req): Json<ExpandRequest>) -> Json<serde_json::Value> {
    match expand_formula(&state, &req.formula) {
        Ok(expanded) => Json(serde_json::json!({ "expanded": expanded })),
        Err(e) => Json(serde_json::json!({ "error": e })),
    }
}

// ── jq handlers ───────────────────────────────────────────────────────────────

#[derive(Deserialize)]
struct JqRequest {
    filter: String,
    /// If set, used as the library body of an ad-hoc override — typically
    /// the unsaved editor buffer.  Combined with `preamble_path` / `deps` to
    /// drive transitive dependency resolution.
    #[serde(default)]
    preamble: Option<String>,
    /// Virtual path for `preamble` when resolving dependencies.  Only used
    /// when `preamble` is set.  Defaults to `"__editor__"`.
    #[serde(default)]
    preamble_path: Option<String>,
    /// Dependencies declared by the editor buffer.  Resolved transitively
    /// the same way the loaded libraries' `deps` are.
    #[serde(default)]
    deps: Vec<String>,
}

#[derive(Serialize)]
struct JqResponse {
    results: Option<Vec<serde_json::Value>>,
    error:   Option<String>,
}

async fn jq_handler(
    State(state): State<AppState>,
    Json(req): Json<JqRequest>,
) -> Json<JqResponse> {
    // Build preamble: resolve transitive deps of the roots, pull each
    // library's content once.  Loaded libs contribute their in-memory
    // `content`; unknown deps are read from disk.  If an editor override is
    // supplied, inject it into the overrides map and seed it as a root.
    let libs = state.jq_libs.lock().unwrap().clone();
    let mut overrides: HashMap<String, (Vec<String>, String)> = HashMap::new();
    for lib in &libs {
        overrides.insert(lib.path.clone(), (lib.deps.clone(), lib.content.clone()));
    }

    let mut roots: Vec<String> = libs.iter().map(|l| l.path.clone()).collect();
    if let Some(body) = &req.preamble {
        let virt_path = req.preamble_path.clone().unwrap_or_else(|| "__editor__".into());
        overrides.insert(virt_path.clone(), (req.deps.clone(), body.clone()));
        // When the editor overrides a library already loaded, re-order roots so
        // the override appears last (its content wins without duplication).
        roots.retain(|p| p != &virt_path);
        roots.push(virt_path);
    }

    let preamble = match resolve_preamble(&roots, &overrides, &state.server_root.join("lib")) {
        Ok(s) => s,
        Err(e) => return Json(JqResponse { results: None, error: Some(e) }),
    };

    let combined = format!("{}{}", preamble, req.filter);
    let loader  = PreludeLoader();
    let context = std::iter::once(Ok::<XqValue, xq::InputError>(XqValue::Null));
    let input   = std::iter::empty::<Result<XqValue, xq::InputError>>();

    match run_query(&combined, context, input, &loader) {
        Err(e) => Json(JqResponse { results: None, error: Some(e.to_string()) }),
        Ok(iter) => {
            let mut results = Vec::new();
            let mut err_msg = None;
            for item in iter {
                match item {
                    Err(e) => { err_msg = Some(e.to_string()); break; }
                    Ok(v)  => match serde_json::from_str::<serde_json::Value>(&v.to_string()) {
                        Err(e) => { err_msg = Some(e.to_string()); break; }
                        Ok(jv) => results.push(jv),
                    },
                }
            }
            match err_msg {
                Some(e) => Json(JqResponse { results: None, error: Some(e) }),
                None    => Json(JqResponse { results: Some(results), error: None }),
            }
        }
    }
}


// ── boxes: compile declared jq boxes into tables (doc/box_backend_design.md §5) ──

/// A box compiled from a loaded library, held in memory for this server.
#[derive(Clone, Serialize)]
struct CompiledBox {
    name: String,
    lib: String,
    params: Vec<String>,
    expose: Vec<String>,
    vars: Vec<String>,
    rows: usize,
    uncovered_paths: usize,
    formula: String,
    /// Projected internals of the definition (renamed per call site on expansion).
    internals: Vec<String>,
    /// Rows of the negative table (models of ¬box over the same columns).
    rows_neg: usize,
    #[serde(skip)]
    table: Table,
    /// The negative table — compiled from the definition's own NNF when nothing
    /// is projected, else the complement of `table` (¬∃U.B = ∀U.¬B).
    #[serde(skip)]
    table_neg: Option<Table>,
}

#[derive(Deserialize)]
struct BoxesCompileRequest {
    /// Only these libraries (paths); default: every loaded library.
    #[serde(default)] libs: Vec<String>,
    #[serde(default = "BoxesCompileRequest::default_max")] max_uncovered_paths: usize,
    #[serde(default = "BoxesCompileRequest::default_timeout")] timeout_secs: u64,
    /// Also write `<server_root>/boxes/<name>.json` (the `sat --boxes` table format).
    #[serde(default)] save: bool,
}
impl BoxesCompileRequest {
    fn default_max() -> usize { 1_000_000 }
    fn default_timeout() -> u64 { 120 }
}

/// Compile (or recompile) the boxes declared by one loaded library, replacing
/// that library's entries in the store — so a declaration that was removed or
/// now fails disappears.  Returns one status per declaration.
async fn compile_lib_boxes(state: &AppState, lib_path: &str, max_paths: usize, timeout_secs: u64) -> Vec<serde_json::Value> {
    let libs = state.jq_libs.lock().unwrap().clone();
    let Some(lib) = libs.iter().find(|l| l.path == lib_path).cloned() else {
        return vec![serde_json::json!({ "error": format!("{lib_path} is not loaded") })];
    };
    if lib.boxes.is_empty() {
        state.compiled_boxes.lock().unwrap().retain(|b| b.lib != lib.path);
        return Vec::new();
    }
    let roots: Vec<String> = libs.iter().map(|l| l.path.clone()).collect();
    let mut overrides = HashMap::new();
    for l in &libs { overrides.insert(l.path.clone(), (l.deps.clone(), l.content.clone())); }
    let preamble = match resolve_preamble(&roots, &overrides, &state.server_root.join("lib")) {
        Ok(p) => p,
        Err(e) => return vec![serde_json::json!({ "error": e })],
    };
    let (mut statuses, mut compiled_now) = (Vec::new(), Vec::new());
    for line in &lib.boxes {
        let d = match parse_box_decl(line) {
            Ok(d) => d,
            Err(e) => { statuses.push(serde_json::json!({ "decl": line, "name": line.split('(').next().unwrap_or("").trim(), "error": e })); continue; }
        };
        let formula = match box_formula(&preamble, &d, None) {
            Ok(f) => f,
            Err(e) => { statuses.push(serde_json::json!({ "name": d.name, "error": e })); continue; }
        };
        // A definition may call boxes declared earlier (in this library or a
        // loaded one): expand those before compiling.
        let formula = {
            let store = state.compiled_boxes.lock().unwrap().clone();
            let lookup = |name: &str| compiled_now.iter().chain(store.iter()).find(|b: &&CompiledBox| b.name == name)
                .map(|b| BoxSig { params: b.vars.clone(), internals: b.internals.clone(), formula: b.formula.clone() });
            match expand_box_calls(&formula, &lookup) {
                Ok(f) => f,
                Err(e) => { statuses.push(serde_json::json!({ "name": d.name, "error": format!("definition: {e}") })); continue; }
            }
        };
        let mut cols = d.params.clone();
        for e in &d.expose { if !cols.contains(e) { cols.push(e.clone()); } }
        let dur = std::time::Duration::from_secs(timeout_secs);
        let fut = compile_box(&d.name, &formula, &cols, max_paths);
        match tokio::time::timeout(dur, fut).await {
            Err(_) => statuses.push(serde_json::json!({ "name": d.name, "error": format!("compile timed out after {timeout_secs} s") })),
            Ok(Err(e)) => statuses.push(serde_json::json!({ "name": d.name, "error": e })),
            Ok(Ok(table)) => {
                // The negative table (§2.2: two tables per box).  Exact from the
                // definition's own NNF only when nothing is projected.
                let table_neg: Option<Table> = if table.internals_projected.is_empty() {
                    match tokio::time::timeout(dur, compile_box_polarity(&d.name, &formula, &cols, max_paths, true)).await {
                        Ok(Ok(t)) => Some(t),
                        _ => table.complement(20).ok(),
                    }
                } else { table.complement(20).ok() };
                let rows_neg = table_neg.as_ref().map_or(0, |t| t.rows.len());
                statuses.push(serde_json::json!({
                    "name": d.name, "vars": table.vars, "rows": table.rows.len(), "rows_neg": rows_neg,
                    "uncovered_paths": table.uncovered_paths, "formula": table.formula,
                }));
                compiled_now.push(CompiledBox {
                    name: d.name.clone(), lib: lib.path.clone(), params: d.params.clone(), expose: d.expose.clone(),
                    vars: table.vars.clone(), rows: table.rows.len(), uncovered_paths: table.uncovered_paths,
                    formula: table.formula.clone(), internals: table.internals_projected.clone(), rows_neg, table, table_neg,
                });
            }
        }
    }
    let mut store = state.compiled_boxes.lock().unwrap();
    store.retain(|b| b.lib != lib.path);
    store.extend(compiled_now);
    statuses
}

/// Recompile the boxes of the loaded libraries (all, or `libs`).  Boxes are
/// compiled automatically on library load and save; this is the manual /
/// scripted entry point, and the one that can `save` the tables to disk.
async fn boxes_compile_handler(
    State(state): State<AppState>,
    Json(req): Json<BoxesCompileRequest>,
) -> Json<serde_json::Value> {
    let paths: Vec<String> = state.jq_libs.lock().unwrap().iter()
        .map(|l| l.path.clone()).filter(|p| req.libs.is_empty() || req.libs.contains(p)).collect();
    let (mut compiled, mut errors) = (Vec::new(), Vec::new());
    for path in &paths {
        for st in compile_lib_boxes(&state, path, req.max_uncovered_paths, req.timeout_secs).await {
            if let Some(e) = st.get("error").and_then(|e| e.as_str()) { errors.push(format!("{}: {}", path, e)); } else { compiled.push(st); }
        }
    }
    if req.save {
        let dir = state.server_root.join("boxes");
        let _ = std::fs::create_dir_all(&dir);
        let store = state.compiled_boxes.lock().unwrap();
        for b in store.iter().filter(|b| paths.contains(&b.lib)) {
            if let Err(e) = std::fs::write(dir.join(format!("{}.json", b.name)), serde_json::to_string_pretty(&b.table.to_json()).unwrap()) {
                errors.push(format!("{}: save: {}", b.name, e));
            }
        }
    }
    Json(serde_json::json!({ "compiled": compiled, "errors": errors }))
}

async fn boxes_list_handler(State(state): State<AppState>) -> Json<serde_json::Value> {
    let boxes = state.compiled_boxes.lock().unwrap().clone();
    Json(serde_json::json!({ "boxes": boxes }))
}

async fn boxes_table_handler(
    State(state): State<AppState>,
    Query(q): Query<HashMap<String, String>>,
) -> Json<serde_json::Value> {
    let name = q.get("name").cloned().unwrap_or_default();
    let store = state.compiled_boxes.lock().unwrap();
    match store.iter().find(|b| b.name == name) {
        Some(b) => Json(b.table.to_json()),
        None => Json(serde_json::json!({ "error": format!("no compiled box named {name}") })),
    }
}

async fn boxes_delete_handler(
    State(state): State<AppState>,
    Query(q): Query<HashMap<String, String>>,
) -> Json<serde_json::Value> {
    let name = q.get("name").cloned().unwrap_or_default();
    let mut store = state.compiled_boxes.lock().unwrap();
    let before = store.len();
    store.retain(|b| b.name != name);
    Json(serde_json::json!({ "ok": true, "removed": before - store.len() }))
}

// ── jq-lib handlers ───────────────────────────────────────────────────────────

#[derive(Deserialize)]
struct JqLibRequest {
    path: String,
}

async fn jq_lib_list_handler(State(state): State<AppState>) -> Json<serde_json::Value> {
    let libs = state.jq_libs.lock().unwrap().clone();
    Json(serde_json::json!({ "libs": libs }))
}

async fn jq_lib_files_handler(State(state): State<AppState>) -> Json<serde_json::Value> {
    let lib_dir = state.server_root.join("lib");
    match std::fs::read_dir(&lib_dir) {
        Err(_) => Json(serde_json::json!({ "files": [] })),
        Ok(entries) => {
            let mut files: Vec<String> = entries
                .filter_map(|e| e.ok())
                .filter(|e| e.path().extension().and_then(|x| x.to_str()) == Some("jq"))
                .filter_map(|e| e.file_name().into_string().ok())
                .collect();
            files.sort();
            Json(serde_json::json!({ "files": files }))
        }
    }
}

/// Build a library entry from a `.jq` file's raw text: split off deps, tests
/// and the box declarations.
fn lib_entry_from_raw(path: &str, raw: &str) -> Result<JqLibEntry, String> {
    let (deps, content_raw, tests) = split_file(raw);
    let (content, boxes) = split_boxes(&content_raw);
    let name = std::path::Path::new(path).file_stem().and_then(|s| s.to_str())
        .ok_or_else(|| "invalid file path".to_string())?.to_string();
    Ok(JqLibEntry { path: path.to_string(), name, deps, content, tests, boxes })
}

async fn jq_lib_load_handler(
    State(state): State<AppState>,
    Json(req): Json<JqLibRequest>,
) -> Json<serde_json::Value> {
    let full_path = state.server_root.join("lib").join(&req.path);
    let raw = match std::fs::read_to_string(&full_path) {
        Ok(c)  => c,
        Err(e) => return Json(serde_json::json!({ "error": e.to_string() })),
    };
    let entry = match lib_entry_from_raw(&req.path, &raw) {
        Ok(e)  => e,
        Err(e) => return Json(serde_json::json!({ "error": e })),
    };
    {
        let mut libs = state.jq_libs.lock().unwrap();
        if let Some(pos) = libs.iter().position(|e| e.path == req.path) { libs[pos] = entry; } else { libs.push(entry); }
    }
    // Boxes follow the library: compile its declarations now.
    let boxes = compile_lib_boxes(&state, &req.path, BoxesCompileRequest::default_max(), BoxesCompileRequest::default_timeout()).await;
    Json(serde_json::json!({ "ok": true, "boxes": boxes }))
}

async fn jq_lib_unload_handler(
    State(state): State<AppState>,
    Json(req): Json<JqLibRequest>,
) -> Json<serde_json::Value> {
    state.jq_libs.lock().unwrap().retain(|e| e.path != req.path);
    state.compiled_boxes.lock().unwrap().retain(|b| b.lib != req.path);
    Json(serde_json::json!({ "ok": true }))
}

/// Delete a `.jq` file from `lib/` on disk.  Refuses if any other `.jq` file
/// in `lib/` lists the target as a dep — the dependants must be fixed or
/// deleted first.  On success also unloads the file from the in-memory libs.
async fn jq_lib_delete_handler(
    State(state): State<AppState>,
    Json(req): Json<JqLibRequest>,
) -> Json<serde_json::Value> {
    if req.path.is_empty() || req.path.contains('/') || req.path.contains('\\') || req.path.contains("..") {
        return Json(serde_json::json!({ "error": "invalid path" }));
    }
    let lib_dir = state.server_root.join("lib");
    let full_path = lib_dir.join(&req.path);
    if !full_path.exists() {
        return Json(serde_json::json!({ "error": format!("{} does not exist", req.path) }));
    }

    // Scan every other .jq file in lib/ and see whose deps list names this one.
    let mut dependants: Vec<String> = Vec::new();
    match std::fs::read_dir(&lib_dir) {
        Err(e) => return Json(serde_json::json!({ "error": format!("listing lib/: {}", e) })),
        Ok(entries) => {
            for entry in entries.filter_map(|e| e.ok()) {
                let p = entry.path();
                if p.extension().and_then(|x| x.to_str()) != Some("jq") { continue; }
                let Some(name) = p.file_name().and_then(|s| s.to_str()) else { continue; };
                if name == req.path { continue; } // skip self
                if let Ok(raw) = std::fs::read_to_string(&p) {
                    let (deps, _c, _t) = split_file(&raw);
                    if deps.iter().any(|d| d == &req.path) {
                        dependants.push(name.to_string());
                    }
                }
            }
        }
    }
    if !dependants.is_empty() {
        dependants.sort();
        return Json(serde_json::json!({
            "error": format!(
                "cannot delete {}: still referenced by {}",
                req.path,
                dependants.join(", "),
            ),
            "dependants": dependants,
        }));
    }

    if let Err(e) = std::fs::remove_file(&full_path) {
        return Json(serde_json::json!({ "error": e.to_string() }));
    }
    // Drop from in-memory loaded libs if present.
    state.jq_libs.lock().unwrap().retain(|e| e.path != req.path);
    Json(serde_json::json!({ "ok": true }))
}

#[derive(Deserialize)]
struct JqLibSaveRequest {
    path:    String,
    #[serde(default)]
    deps:    Vec<String>,
    content: String,
    #[serde(default)]
    tests:   String,
    #[serde(default)]
    boxes:   Vec<String>,
}

/// Write a library's deps / content / tests back to `lib/{path}` on disk and
/// refresh the in-memory copy so subsequent `/jq` requests see the change.
async fn jq_lib_save_handler(
    State(state): State<AppState>,
    Json(req): Json<JqLibSaveRequest>,
) -> Json<serde_json::Value> {
    // Reject anything that would escape the lib/ directory.  `PathBuf::file_name`
    // exists for exactly this reason but we need the raw component — disallow
    // separators and parent references explicitly.
    if req.path.contains('/') || req.path.contains('\\') || req.path.contains("..") {
        return Json(serde_json::json!({ "error": "invalid path" }));
    }
    // Validate each dep the same way.
    for d in &req.deps {
        if d.is_empty() || d.contains('/') || d.contains('\\') || d.contains("..") {
            return Json(serde_json::json!({ "error": format!("invalid dependency path: {}", d) }));
        }
        if d == &req.path {
            return Json(serde_json::json!({ "error": "a library cannot depend on itself" }));
        }
    }
    // Validate the box declarations before anything touches the disk.
    let boxes: Vec<String> = req.boxes.iter().map(|b| b.trim().to_string()).filter(|b| !b.is_empty()).collect();
    for b in &boxes {
        if let Err(e) = parse_box_decl(b) {
            return Json(serde_json::json!({ "error": format!("box declaration {b:?}: {e}") }));
        }
    }
    let full_path = state.server_root.join("lib").join(&req.path);
    let on_disk = join_file(&req.deps, &join_boxes(&req.content, &boxes), &req.tests);
    if let Err(e) = std::fs::write(&full_path, &on_disk) {
        return Json(serde_json::json!({ "error": e.to_string() }));
    }
    // Update any loaded in-memory copy, then recompile its boxes.
    let loaded = {
        let mut libs = state.jq_libs.lock().unwrap();
        match libs.iter_mut().find(|e| e.path == req.path) {
            Some(entry) => { entry.deps = req.deps; entry.content = req.content; entry.tests = req.tests; entry.boxes = boxes; true }
            None => false,
        }
    };
    let statuses = if loaded {
        compile_lib_boxes(&state, &req.path, BoxesCompileRequest::default_max(), BoxesCompileRequest::default_timeout()).await
    } else { Vec::new() };
    Json(serde_json::json!({ "ok": true, "boxes": statuses }))
}

// ── Examples handlers ─────────────────────────────────────────────────────────

const EXAMPLES_FILE: &str = "examples.json";

#[derive(Serialize, Deserialize, Clone)]
struct Example {
    label: String,
    f:     String,
}

async fn load_examples_handler() -> Json<serde_json::Value> {
    match std::fs::read_to_string(EXAMPLES_FILE) {
        Err(_)      => Json(serde_json::json!({ "examples": null })),
        Ok(content) => match serde_json::from_str::<Vec<Example>>(&content) {
            Err(e)   => Json(serde_json::json!({ "error": e.to_string() })),
            Ok(list) => Json(serde_json::json!({ "examples": list })),
        },
    }
}

async fn save_examples_handler(Json(list): Json<Vec<Example>>) -> Json<serde_json::Value> {
    match serde_json::to_string_pretty(&list) {
        Err(e)      => Json(serde_json::json!({ "error": e.to_string() })),
        Ok(content) => match std::fs::write(EXAMPLES_FILE, content) {
            Err(e)  => Json(serde_json::json!({ "error": e.to_string() })),
            Ok(_)   => Json(serde_json::json!({ "ok": true })),
        },
    }
}

// ── Logic handlers ────────────────────────────────────────────────────────────

#[derive(Deserialize)]
struct FormulaRequest {
    formula: String,
    #[serde(default)]
    no_cover: bool,
    /// Backend selector — one of "smart", "cdcl", "eff",
    /// "greedy_cdcl", "greedy_eff".  Defaults to `greedy_eff`
    /// (matches the UI selector's initial value).
    #[serde(default = "default_backend")]
    backend: String,
}

fn default_backend() -> String { "greedy_eff".to_string() }

/// Internal enum form of the request's `backend` string.  Constructed
/// in the handler via `parse_backend(&req.backend)`; on unknown
/// strings we fall back to `GreedyEff` rather than erroring (the UI
/// only sends a value from its known list, but a stale client could
/// send anything).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Backend {
    /// Row engine over compiled box tables (`logic::boxes::Engine`): box
    /// calls stay atoms, the residual is Tseitin-encoded, each atom is tied
    /// to its box by `atom ⇒ table` / `¬atom ⇒ ¬table` rows.
    Boxes,
    /// Single-DFS `BacktrackWhenCoveredController`.  Used by the
    /// `paths` view (it needs the full cover certificates).  Not
    /// exposed in the UI selector.
    Backtrack,
    /// Single-DFS `SmartController`.  Previous default for valid /
    /// satisfiable.
    Smart,
    /// Single-DFS `CdclController`.
    Cdcl,
    /// Single-DFS `EffectiveCountWrapper<CdclController>` — CDCL with
    /// the effective-path-count layer wrapped around it, no dual
    /// framework overhead.
    Eff,
    /// Dual `GreedyMaxCoverController × CdclDualPathController`.
    GreedyCdcl,
    /// Dual `GreedyMaxCoverController × EffectivePathController`.
    /// New default for valid / satisfiable; currently the strongest
    /// matrix-method configuration on most rows of the focused
    /// 27-bit bench.
    GreedyEff,
}

// (`Backend::is_dual` helper omitted — the match arm in
// `start_classify_job` directly handles the dual variants.)

fn parse_backend(s: &str) -> Backend {
    match s {
        "boxes"       => Backend::Boxes,
        "smart"       => Backend::Smart,
        "cdcl"        => Backend::Cdcl,
        "eff"         => Backend::Eff,
        "greedy_cdcl" => Backend::GreedyCdcl,
        "greedy_eff"  => Backend::GreedyEff,
        _             => Backend::GreedyEff,
    }
}

#[derive(Deserialize)]
struct SimplifyRequest {
    formula: String,
    #[serde(default)]
    cnf: bool,
}

#[derive(Deserialize)]
struct PathsRequest {
    formula: String,
    #[serde(default = "default_paths_class_limit")]
    paths_class_limit: usize,
    #[serde(default)]
    complement: bool,
    /// Keep box calls as units: paths of the collapsed matrix, each checked
    /// against the box tables.
    #[serde(default)]
    box_aware: bool,
}

fn default_paths_class_limit() -> usize { 100 }

#[derive(Serialize)]
struct SimplifyResponse {
    result: Option<String>,
    error:  Option<String>,
}

/// Shared status response for valid, satisfiable, and paths jobs.
#[derive(Serialize)]
struct ClassifyStatusResponse {
    uncovered_paths:            Vec<String>,
    uncovered_path_positions:   Vec<Vec<Vec<usize>>>,
    cover_groups:               Vec<CoverGroup>,
    total_prefix_count:         usize,
    classified_count:           f64,
    total_path_count:           f64,
    elapsed_secs:               f64,
    hit_limit:                  bool,
    running:                    bool,
    is_complement:              bool,
    error:                      Option<String>,
    preprocessed_to:            Option<String>,
}

fn classify_status(job: &ClassifyJob) -> ClassifyStatusResponse {
    // The drainer task keeps `snapshot.classified_count` updated for cover-
    // mode jobs (it adds the right-side cover count of every covered prefix).
    // For no_cover jobs the channel never sees Covered events so the snapshot
    // stays at zero until the run completes.  The worker meanwhile publishes
    // a live `path_count` (covered + uncovered detections) into the cancel
    // handle every few thousand traversal steps; surface that as a fallback
    // so the UI sees the count tick up in real time.
    let live = job.cancel.as_ref().map(|c| c.paths_so_far()).unwrap_or(0.0);
    let classified = job.snapshot.classified_count.max(live);
    ClassifyStatusResponse {
        uncovered_paths:          job.snapshot.uncovered_paths.clone(),
        uncovered_path_positions: job.snapshot.uncovered_path_positions.clone(),
        cover_groups:             job.snapshot.cover_groups.clone(),
        total_prefix_count:       job.snapshot.total_prefix_count,
        classified_count:         classified,
        total_path_count:         job.total_path_count,
        elapsed_secs:             job.start_time.map_or(0.0, |t| t.elapsed().as_secs_f64()),
        hit_limit:                job.snapshot.hit_limit,
        running:                  job.running,
        is_complement:            job.is_complement,
        error:                    job.error.clone(),
        preprocessed_to:          job.snapshot.preprocessed_to.clone(),
    }
}

async fn simplify_handler(State(state): State<AppState>, Json(req): Json<SimplifyRequest>) -> Json<SimplifyResponse> {
    let formula = match expand_formula(&state, &req.formula) {
        Ok(f) => f,
        Err(e) => return Json(SimplifyResponse { result: None, error: Some(e) }),
    };
    let result = if req.cnf {
        logic::simplify_cnf(&formula)
    } else {
        logic::simplify_dnf(&formula)
    };
    match result {
        Ok(r)  => Json(SimplifyResponse { result: Some(r), error: None }),
        Err(e) => Json(SimplifyResponse { result: None,    error: Some(e) }),
    }
}

/// Start a classify job: parse formula, launch `classify_paths`, spawn drainer.
///
/// `use_smart_controller` picks the controller flavour:
/// - `false` → `BacktrackWhenCoveredController`, the cover-aware DFS used
///   by the `paths` view (it needs the full cover certificates).
/// - `true` → `SmartController`, which preprocesses the target NNF for
///   cross-clause unit propagation.  Used by the `valid` and `satisfiable`
///   views, which only need a yes/no answer plus a witness — propagation
///   gets there much faster on structured formulas (adders, encoders).
///
/// `preprocess` enables Phase 1 NNF preprocessing (top-level unit
/// propagation) — runs `matrix.preprocess_for_search(complement)` and
/// hands the simplified NNF to the search.  Cover-pair and
/// path-position outputs are translated back to original-formula
/// positions so the UI renders them on the original formula's
/// diagram.  Lemma covers derived during preprocessing are appended
/// to `cover_groups` after the search completes.
fn start_classify_job(
    job_state: Arc<Mutex<ClassifyJob>>,
    formula: &str,
    complement: bool,
    params: Option<logic::matrix::PathParams>,
    backend: Backend,
    preprocess: bool,
    boxctx: Option<BoxContext>,
) -> Result<(), String> {
    use logic::matrix::{
        Matrix, DynOnClass, PathsClass, NNF, Lit,
        default_classify_controller, format_lits, format_path,
    };
    use logic::controller::{CdclController, SmartController};
    use logic::preprocess::{PositionMap, ReconstructionStack};

    // Start the wall-clock timer here, before parsing and preprocessing,
    // so the UI's `elapsed_secs` reflects raw-input → verdict time and
    // is directly comparable with the cadical-style all-in numbers from
    // `bench_focused_top_config_preprocessed`.  Without this, the timer
    // would only cover the search phase and silently undercount the
    // user's wait by `pp` (3–7 ms on the focused benchmark formulas).
    let job_start = std::time::Instant::now();

    /// Simulate the matrix-method search's DFS through `ast`, counting
    /// leaf positions visited up to (and including) the moment when
    /// both `p1` and `p2` have been visited — i.e. the moment when
    /// `BacktrackWhenCoveredController` would detect the cover and
    /// back out.  The returned count matches the `prefix_length` the
    /// search would have reported for a search-found cover of this
    /// pair (within the variability introduced by alt-pick choices at
    /// unconstrained pick-one nodes — this simulation picks alt 0 at
    /// such nodes).
    ///
    /// `pick_one_is_sum` is `true` for satisfiability (search on
    /// complement: `Sum` is pick-one under De Morgan) and `false` for
    /// validity (search on `NNF`: `Prod` is pick-one).
    fn dfs_prefix_length_to_cover(
        ast: &NNF,
        p1: &[usize],
        p2: &[usize],
        pick_one_is_sum: bool,
    ) -> usize {
        fn is_strict_prefix(prefix: &[usize], full: &[usize]) -> bool {
            if prefix.len() >= full.len() { return false; }
            prefix.iter().zip(full.iter()).all(|(a, b)| a == b)
        }
        struct Ctx<'a> {
            p1: &'a [usize],
            p2: &'a [usize],
            pick_one_is_sum: bool,
            visited_p1: bool,
            visited_p2: bool,
            count: usize,
            done: bool,
        }
        fn walk(node: &NNF, pos: &mut Vec<usize>, ctx: &mut Ctx) {
            if ctx.done { return; }
            match node {
                NNF::Lit(_) => {
                    ctx.count += 1;
                    if pos.as_slice() == ctx.p1 { ctx.visited_p1 = true; }
                    if pos.as_slice() == ctx.p2 { ctx.visited_p2 = true; }
                    if ctx.visited_p1 && ctx.visited_p2 { ctx.done = true; }
                }
                NNF::Sum(ch) | NNF::Prod(ch) => {
                    let is_pick_one = match node {
                        NNF::Sum(_)  => ctx.pick_one_is_sum,
                        NNF::Prod(_) => !ctx.pick_one_is_sum,
                        NNF::Lit(_)  => unreachable!(),
                    };
                    if is_pick_one {
                        // At pick-one nodes, follow the constraint from
                        // p1 or p2 if pos is a strict prefix of either;
                        // otherwise pick alt 0 (the search's natural
                        // first descent).
                        let chosen = if is_strict_prefix(pos, ctx.p1) {
                            ctx.p1[pos.len()]
                        } else if is_strict_prefix(pos, ctx.p2) {
                            ctx.p2[pos.len()]
                        } else {
                            0
                        };
                        if chosen < ch.len() {
                            pos.push(chosen);
                            walk(&ch[chosen], pos, ctx);
                            pos.pop();
                        }
                    } else {
                        for (i, child) in ch.iter().enumerate() {
                            if ctx.done { break; }
                            pos.push(i);
                            walk(child, pos, ctx);
                            pos.pop();
                        }
                    }
                }
            }
        }
        let mut ctx = Ctx {
            p1, p2, pick_one_is_sum,
            visited_p1: false, visited_p2: false,
            count: 0, done: false,
        };
        let mut pos: Vec<usize> = Vec::new();
        walk(ast, &mut pos, &mut ctx);
        ctx.count
    }

    let mut matrix = Matrix::try_from(formula)?;
    // Box-aware paths: candidate paths of the atomized matrix are checked
    // against the box tables before they are reported (see `box_path_filter`).
    let box_filter_for_drainer: Option<Arc<dyn Fn(&[Lit]) -> bool + Send + Sync>> = match &boxctx {
        Some(ctx) => Some(box_path_filter(ctx, &mut matrix)?),
        None => None,
    };
    // Snapshot of the original NNF needed for lemma-cover sizing
    // (we count leaves on covered paths through the *original*
    // matrix, not the preprocessed one).  Kept separately so the
    // `for_search` consumer doesn't move it.
    let original_nnf_for_lemma = matrix.nnf.clone();

    // If preprocessing is enabled, run Phase 1 UP and use the
    // simplified-and-re-complemented NNF as the search target.  Keep
    // the position map, reconstruction stack, and lemma covers
    // around so the drainer can translate outputs back to the
    // original-NNF positions / variables the UI expects.
    let (target_nnf, pos_map_opt, recon_opt, lemma_covers):
        (NNF, Option<PositionMap>, Option<ReconstructionStack>, logic::matrix::Cover) =
        if preprocess {
            let (search_target, pp) = matrix.preprocess_for_search(complement);
            (search_target, Some(pp.pos_map), Some(pp.recon), pp.lemma_covers)
        } else {
            let raw = if complement { matrix.nnf_complement.clone() } else { matrix.nnf.clone() };
            (raw, None, None, Vec::new())
        };
    // `total_path_count` is the count the UI shows in
    // "all N paths..." messages — it should reflect the *original*
    // formula's matrix (what the user is thinking about), not the
    // possibly-much-smaller preprocessed search target.  For
    // preprocessing-off this equals the search target as before; for
    // preprocessing-on we ignore the preprocessed target's path count
    // and report the original side's path count.
    //
    // Edge case: formulas containing the constant `0` (or whose
    // encoders emit one when a sub-constraint is structurally
    // impossible — e.g. BMC `c_n > n` with `n ≥ 2^w`) put a
    // `Sum([])` somewhere in `F` and a `Prod([])` in `comp(F)`.
    // `Prod([])` annihilates the surrounding `Sum`'s cross-product so
    // the *complement* side ends up with `path_count = 0` while `F`
    // still has many paths.  When the primary side is 0 fall back to
    // the other side so the UI doesn't read "all 0 paths".
    let primary_path_count = if complement {
        matrix.nnf_complement.path_count()
    } else {
        matrix.nnf.path_count()
    };
    let total_path_count = if primary_path_count > 0.0 {
        primary_path_count
    } else if complement {
        matrix.nnf.path_count()
    } else {
        matrix.nnf_complement.path_count()
    };
    let target = target_nnf.clone();
    let vars = matrix.ast.vars.clone();

    // Detect whether preprocessing already reduced the search target
    // to a constant — `Prod([])` (TRUE) means the search will find no
    // paths (so no covers, no uncovered), and `Sum([])` (FALSE) means
    // one empty path which the search will report as uncovered.
    // Surface this state in the snapshot so the UI can show
    // "Preprocessing covered every path in the original matrix" when
    // there are no concrete covers to render.
    let preprocessed_to: Option<String> = if preprocess {
        match &target {
            NNF::Prod(ch) if ch.is_empty() => Some("TRUE".to_string()),
            NNF::Sum(ch)  if ch.is_empty() => Some("FALSE".to_string()),
            _ => None,
        }
    } else {
        None
    };

    // Translation helpers — closures over the optional pos_map.  When
    // pos_map is None (preprocessing disabled) these are identity.
    let pos_map_for_drainer = pos_map_opt;
    let recon_for_drainer = recon_opt;
    let translate_pos = |p: &logic::matrix::Position, pm: &Option<PositionMap>| -> logic::matrix::Position {
        pm.as_ref().and_then(|m| m.translate(p)).unwrap_or_else(|| p.clone())
    };
    let translate_pair = |pair: &logic::matrix::Pair, pm: &Option<PositionMap>| -> logic::matrix::Pair {
        pm.as_ref().and_then(|m| m.translate_pair(pair)).unwrap_or_else(|| pair.clone())
    };

    let params_for_builder = params.clone();
    // `for_nnf_with_cover` enables cover-pair certificates so the UI
    // can display them; `for_nnf` is the cheaper uncovered-only
    // variant that suppresses `Covered` events.  Pick based on the
    // request's `no_cover` flag.
    let want_cover = params.as_ref().is_none_or(|p| !p.no_cover);
    let buffer_size = 64usize;

    // Dispatch by backend.  Single-DFS backends (smart, cdcl, eff,
    // backtrack) use `classify_paths*` directly.  Dual backends
    // (greedy_cdcl, greedy_eff) run `solve_dual_with_cancel` in a
    // spawn_blocking task and stream events through a
    // controller-side `Sender` set up via `with_stream`.
    let (handle, mut rx, cancel) = match backend {
        Backend::Backtrack => {
            let p = params_for_builder.clone();
            target_nnf.classify_paths(buffer_size, move |tx| default_classify_controller(p, tx))
        }
        Backend::Smart => {
            let nnf_for_builder = target.clone();
            let p = params_for_builder.clone();
            if want_cover {
                target_nnf.classify_paths(buffer_size, move |tx| {
                    let on_class: DynOnClass = Box::new(move |class, hit_limit|
                        tx.blocking_send((class, hit_limit)).is_ok());
                    SmartController::for_nnf_with_cover(&nnf_for_builder, p, on_class)
                })
            } else {
                target_nnf.classify_paths_uncovered_only(buffer_size, move |tx| {
                    let on_class: DynOnClass = Box::new(move |class, hit_limit|
                        tx.blocking_send((class, hit_limit)).is_ok());
                    SmartController::for_nnf(&nnf_for_builder, p, on_class)
                })
            }
        }
        Backend::Cdcl => {
            let nnf_for_builder = target.clone();
            let p = params_for_builder.clone();
            if want_cover {
                target_nnf.classify_paths(buffer_size, move |tx| {
                    let on_class: DynOnClass = Box::new(move |class, hit_limit|
                        tx.blocking_send((class, hit_limit)).is_ok());
                    CdclController::for_nnf_with_cover(&nnf_for_builder, p, on_class)
                })
            } else {
                target_nnf.classify_paths_uncovered_only(buffer_size, move |tx| {
                    let on_class: DynOnClass = Box::new(move |class, hit_limit|
                        tx.blocking_send((class, hit_limit)).is_ok());
                    CdclController::for_nnf(&nnf_for_builder, p, on_class)
                })
            }
        }
        Backend::Eff => {
            // matrix.eff: CDCL inner + EffectiveCountWrapper, no
            // dual framework.  Always use the positions-ON engine
            // (`classify_paths_with_nnf`) regardless of `want_cover`
            // because `EffectiveCountWrapper::sum_ord` re-orders Sum
            // children — without positions tracked by the engine, the
            // drainer's fallback (`positions_on_path` walking
            // declaration-order) would mis-align path entries to
            // subtrees and panic on non-trivial formulas.  The
            // inner CdclController still picks cover-mode vs
            // uncovered-only based on `want_cover`; only the engine
            // tracks positions in both cases.  `_with_nnf` passes the
            // engine's own NNF clone to the builder so the
            // `EffectiveCountIndex`'s pointer-keyed lookups line up
            // with the &NNF refs the engine passes via sum_ord /
            // prod_ord.
            use logic::dual::effective_count::{EffectiveCountIndex, EffectiveCounts};
            use logic::dual::path_effective::EffectiveCountWrapper;
            let p = params_for_builder.clone();
            target_nnf.classify_paths_with_nnf(buffer_size, move |nnf_ref, tx| {
                let on_class: DynOnClass = Box::new(move |class, hit_limit|
                    tx.blocking_send((class, hit_limit)).is_ok());
                let cdcl = if want_cover {
                    CdclController::for_nnf_with_cover(nnf_ref, p, on_class)
                } else {
                    CdclController::for_nnf(nnf_ref, p, on_class)
                };
                let idx = EffectiveCountIndex::build(nnf_ref);
                let counts = EffectiveCounts::new(&idx);
                EffectiveCountWrapper::new(cdcl, idx, counts)
            })
        }
        Backend::GreedyCdcl | Backend::GreedyEff | Backend::Boxes => {
            spawn_dual_classify_job(backend, target_nnf.clone(), buffer_size)
        }
    };
    {
        let mut job = job_state.lock().unwrap();
        job.cancel = Some(cancel);
        job.total_path_count = total_path_count;
        // Use the timer started at the very top of this function so
        // preprocessing + search-setup are included in `elapsed_secs`
        // (the UI's "at N paths/s in T ms" reading).
        job.start_time = Some(job_start);
        job.preprocessed = preprocess;
        job.snapshot.preprocessed_to = preprocessed_to;
    }

    let js = job_state.clone();
    tokio::spawn(async move {
        while let Some((class, hit_limit)) = rx.recv().await {
            // Drainer needs the lock to update the snapshot.  Recover
            // gracefully if a previous iteration poisoned the mutex
            // (e.g. by panicking inside `positions_on_path` /
            // `lits_on_path` on a re-ordered DFS path emission — see
            // `bug_note` below).  Using `into_inner()` here is safe
            // because we always re-acquire the lock and write
            // valid state below; any partial write from the
            // panicking iteration is overwritten.
            let mut job = match js.lock() {
                Ok(g)  => g,
                Err(p) => p.into_inner(),
            };
            // Catch panics inside the per-event processing so a
            // single bad event (e.g. an Uncovered ProdPath that
            // doesn't resolve under declaration-order
            // `positions_on_path`, which happens for re-ordered DFS
            // emissions from the Effective layer / dual configs)
            // doesn't take down the whole drainer and poison the
            // mutex for every future status poll.  On panic, we set
            // an error on the job, mark it not-running, and stop
            // draining.
            //
            // bug_note: The proper fix is to plumb positions through
            // `PathsClass::Uncovered` from the engines that have
            // them (positions-ON DFS), or to make
            // `positions_on_path` / `lits_on_path` re-order-aware.
            // For now this turns a hard crash into a soft error.
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            match class {
                PathsClass::Covered(cp) => {
                    let cover_count = target.prefix_cover_count(&cp.prefix);
                    // Translate pair and prefix back to original-NNF positions.
                    let pair = translate_pair(&cp.cover, &pos_map_for_drainer);
                    let prefix: Vec<logic::matrix::Position> = cp.prefix.iter()
                        .map(|p| translate_pos(p, &pos_map_for_drainer))
                        .collect();
                    let key = pair_key(&pair);
                    let len = prefix.len();
                    let snap = &mut job.snapshot;
                    snap.total_prefix_count += 1;
                    snap.classified_count += cover_count;
                    let gi = if let Some(&gi) = snap.group_map.get(&key) {
                        gi
                    } else {
                        let gi = snap.cover_groups.len();
                        snap.group_map.insert(key, gi);
                        snap.cover_groups.push(CoverGroup {
                            pair,
                            count: 0,
                            prefix_length_min: usize::MAX,
                            prefix_length_max: 0,
                            prefixes: Vec::new(),
                        });
                        gi
                    };
                    let g = &mut snap.cover_groups[gi];
                    g.count += 1;
                    g.prefix_length_min = g.prefix_length_min.min(len);
                    g.prefix_length_max = g.prefix_length_max.max(len);
                    if snap.total_prefix_count <= PREFIX_DETAIL_LIMIT {
                        g.prefixes.push(prefix);
                    } else if snap.total_prefix_count == PREFIX_DETAIL_LIMIT + 1 {
                        for grp in &mut snap.cover_groups {
                            grp.prefixes.clear();
                        }
                    }
                }
                PathsClass::Uncovered(up) => {
                    let keep = box_filter_for_drainer.as_ref().is_none_or(|f| {
                        let lits: Vec<Lit> = if !up.lits.is_empty() { up.lits.clone() }
                            else { target.lits_on_path(&up.prod_path).iter().map(|&l| l.clone()).collect() };
                        f(&lits)
                    });
                    // Use the engine-provided positions and lits when
                    // they're populated (positions-ON engines —
                    // matrix.eff / greedy×eff in particular).  Fall
                    // back to `positions_on_path` / `lits_on_path` when
                    // the engine didn't track them (positions-OFF —
                    // matrix.smart / matrix.cdcl); that fallback is
                    // sound because positions-OFF engines pair with
                    // declaration-order Sum traversal.
                    let raw_positions: logic::matrix::PathPrefix = if !up.positions.is_empty() {
                        up.positions.clone()
                    } else {
                        target.positions_on_path(&up.prod_path)
                    };
                    let translated: logic::matrix::PathPrefix = raw_positions.iter()
                        .map(|p| translate_pos(p, &pos_map_for_drainer))
                        .collect();
                    // Build the displayed witness.  When preprocessing
                    // is on, the search ran on a simplified NNF that
                    // doesn't mention any variable UP pinned — append
                    // the recon stack's literals so the user sees the
                    // full assignment, not just the post-pp residual.
                    //
                    // Recon stores each step as `Unit { var, value }`
                    // where `value` is what the var must equal in the
                    // witness direction (satisfying-F for satisfiability,
                    // falsifying-F for validity).  The matrix-method's
                    // display convention is "user mentally negates the
                    // displayed literals to read the witness", so we
                    // push each recon literal with `neg = value` (the
                    // OPPOSITE of the recon's witness-direction lit).
                    let path_str = if let Some(recon) = &recon_for_drainer {
                        // Build the F-direction witness assignment, then
                        // negate it for display (the UI follows the
                        // "user mentally negates path literals to read
                        // the witness" convention).  Use
                        // `pad_survivors_and_extend` (not raw
                        // `extend_assignment`) because Phase 3's
                        // `Defined` recon steps evaluate their defns
                        // against surviving variables — those must
                        // already be in the assignment before recon
                        // replay.
                        let path_lits: Vec<Lit> = if !up.lits.is_empty() {
                            up.lits.clone()
                        } else {
                            target.lits_on_path(&up.prod_path)
                                .iter().map(|&l| l.clone()).collect()
                        };
                        let mut witness_f: Vec<Lit> = path_lits.iter()
                            .map(|l| l.complement()).collect();
                        recon.pad_survivors_and_extend(&mut witness_f, vars.len() as u32);
                        // Display in target polarity (user negates).
                        let display_lits: Vec<Lit> = witness_f.iter()
                            .map(|l| l.complement())
                            .collect();
                        format_lits(&display_lits, &vars)
                    } else if !up.lits.is_empty() {
                        format_lits(&up.lits, &vars)
                    } else {
                        format_path(&up.prod_path, &target, &vars)
                    };
                    if keep {
                        job.snapshot.classified_count += 1.0;
                        job.snapshot.uncovered_paths.push(path_str);
                        job.snapshot.uncovered_path_positions.push(translated);
                    }
                }
            }
            if hit_limit { job.snapshot.hit_limit = true; }
            }));
            if let Err(panic_info) = result {
                let msg = if let Some(s) = panic_info.downcast_ref::<&str>() {
                    s.to_string()
                } else if let Some(s) = panic_info.downcast_ref::<String>() {
                    s.clone()
                } else {
                    "drainer event processing panicked (unknown payload type)".to_string()
                };
                job.error = Some(format!(
                    "Internal: backend emitted a path the drainer couldn't \
                     translate — likely a re-ordered Sum traversal from the \
                     Effective layer.  Detail: {}",
                    msg,
                ));
                eprintln!("[web_app drainer] caught panic: {}", msg);
                drop(job);
                // Stop draining — we can't trust further events from
                // this run.  Also break the receiver so the producer
                // notices the drop.
                rx.close();
                break;
            }
            // (job lock dropped at end of arm.)
        }
        let _ = handle.await;
        let mut job = match js.lock() {
            Ok(g)  => g,
            Err(p) => p.into_inner(),
        };
        // Append preprocessing-derived lemma covers to the cover-group
        // list.  Their positions are already in the original NNF; for
        // each lemma cover we simulate the matrix-method search's DFS
        // through the original NNF and report the leaf-count at the
        // moment when both endpoints have been visited — i.e. when
        // the search would have detected this cover and backed out.
        // That gives a prefix length in the same ballpark as
        // search-found covers, matching what the paths-view shows
        // for similar covers found by full DFS.  `prefixes` stays
        // empty (no concrete search-derived path-trace to render).
        for pair in lemma_covers {
            let key = pair_key(&pair);
            // SAT direction (complement=true): search ran on comp(F), so
            // Sum acts as pick-one when walking F's NNF.  Validity
            // direction: Prod is pick-one.  Matches the frontend's
            // `coverProdType` rule ('OR' for SAT, 'AND' for validity).
            let leaf_count = dfs_prefix_length_to_cover(
                &original_nnf_for_lemma, &pair.0, &pair.1, complement);
            let snap = &mut job.snapshot;
            let gi = if let Some(&gi) = snap.group_map.get(&key) {
                gi
            } else {
                let gi = snap.cover_groups.len();
                snap.group_map.insert(key, gi);
                snap.cover_groups.push(CoverGroup {
                    pair,
                    count: 0,
                    prefix_length_min: usize::MAX,
                    prefix_length_max: 0,
                    prefixes: Vec::new(),
                });
                gi
            };
            let g = &mut snap.cover_groups[gi];
            g.count += 1;
            g.prefix_length_min = g.prefix_length_min.min(leaf_count);
            g.prefix_length_max = g.prefix_length_max.max(leaf_count);
        }
        job.running = false;
        let cancelled = job.cancel.as_ref().is_some_and(|c| c.is_cancelled());
        job.cancel = None;
        // On clean completion every path has been classified — even in
        // `no_cover` mode, where `Covered` events are suppressed and the
        // running counter therefore never tracked them.  Backfill to the
        // total so the reported rate reflects reality.
        if !cancelled && !job.snapshot.hit_limit && job.error.is_none() {
            job.snapshot.classified_count = job.total_path_count;
        }
    });
    Ok(())
}

/// Dual-framework backend dispatch: run `solve_dual_with_cancel` on a
/// blocking task, with B's path controller (`CdclDualPathController`
/// or `EffectivePathController`) configured to stream every
/// `PathsClass` event into the returned `Receiver`.  The drainer
/// task in `start_classify_job` then processes those events the
/// same way it does single-DFS events — populating cover groups,
/// uncovered paths, classified counts, etc.
///
/// The returned `PathClassificationHandle`'s cancel signal is wired
/// to `solve_dual_with_cancel`'s `external_cancel` parameter via a
/// short-lived watcher thread, so the UI's Cancel button still
/// works.
fn spawn_dual_classify_job(
    backend: Backend,
    target_nnf: logic::matrix::NNF,
    buffer_size: usize,
) -> (
    tokio::task::JoinHandle<Result<(), Box<dyn std::error::Error + Send>>>,
    tokio::sync::mpsc::Receiver<(logic::matrix::PathsClass, bool)>,
    logic::matrix::PathClassificationHandle,
) {
    use logic::dual::{
        solve_dual_with_cancel, BasicCoverState, CdclDualPathController,
        EffectivePathController, GreedyMaxCoverController, SearchMode,
    };

    let (tx, rx) = tokio::sync::mpsc::channel::<(logic::matrix::PathsClass, bool)>(buffer_size);
    let cancel = logic::matrix::PathClassificationHandle::new();
    // Share the cancel atomic directly — no watcher thread, so the
    // UI's `cancel()` reaches `solve_dual_with_cancel`'s termination
    // loop as fast as `solve_dual_with_cancel` polls it (every few
    // ms; see that function for the timeout).  Previously a 50 ms
    // polling watcher added a tail to cancel propagation, which
    // compounded across rapid re-runs (e.g. backend-selector
    // toggles) and made subsequent dual runs visibly slower until
    // the old run cleaned up.
    let external_cancel = cancel.cancel_flag();

    let handle = tokio::task::spawn_blocking(move || {
        let _ = match backend {
            Backend::GreedyCdcl => {
                let cover = GreedyMaxCoverController::default();
                let path  = CdclDualPathController::<BasicCoverState>::with_stream(tx);
                solve_dual_with_cancel(
                    &target_nnf, cover, path, SearchMode::Satisfiable,
                    external_cancel,
                )
            }
            Backend::GreedyEff | Backend::Boxes => {
                let cover = GreedyMaxCoverController::default();
                let path  = EffectivePathController::<BasicCoverState>::with_stream(tx);
                solve_dual_with_cancel(
                    &target_nnf, cover, path, SearchMode::Satisfiable,
                    external_cancel,
                )
            }
            _ => unreachable!("spawn_dual_classify_job called with non-dual backend"),
        };
        Ok::<(), Box<dyn std::error::Error + Send>>(())
    });
    (handle, rx, cancel)
}

fn reset_and_start(
    job_state: &Arc<Mutex<ClassifyJob>>,
    formula: &str,
    complement: bool,
    params: Option<logic::matrix::PathParams>,
    backend: Backend,
    preprocess: bool,
    boxctx: Option<BoxContext>,
) -> Json<serde_json::Value> {
    {
        let mut job = match job_state.lock() {
            Ok(g)  => g,
            Err(p) => p.into_inner(),
        };
        if let Some(c) = job.cancel.take() { c.cancel(); }
        *job = ClassifyJob::default();
        job.running = true;
        job.is_complement = complement;
    }
    if let Err(e) = start_classify_job(
        job_state.clone(), formula, complement, params, backend, preprocess, boxctx,
    ) {
        let mut job = match job_state.lock() {
            Ok(g)  => g,
            Err(p) => p.into_inner(),
        };
        job.running = false;
        job.error = Some(e);
    }
    Json(serde_json::json!({ "ok": true }))
}

fn status_handler(job_state: &Arc<Mutex<ClassifyJob>>) -> Json<ClassifyStatusResponse> {
    // Recover from a poisoned mutex — see drainer notes.  A poisoned
    // job-state is still readable: we just risk inconsistent
    // intermediate values, which is fine for a status response.
    let job = match job_state.lock() {
        Ok(g)  => g,
        Err(p) => p.into_inner(),
    };
    Json(classify_status(&job))
}

fn cancel_handler(job_state: &Arc<Mutex<ClassifyJob>>) -> Json<serde_json::Value> {
    let mut job = match job_state.lock() {
        Ok(g)  => g,
        Err(p) => p.into_inner(),
    };
    if let Some(c) = job.cancel.take() { c.cancel(); }
    job.running = false;
    Json(serde_json::json!({ "ok": true }))
}

async fn valid_handler(
    State(state): State<AppState>,
    Json(req): Json<FormulaRequest>,
) -> Json<serde_json::Value> {
    use logic::matrix::PathParams;
    let params = Some(PathParams {
        uncovered_path_limit: 1,
        paths_class_limit: usize::MAX,
        covered_prefix_limit: usize::MAX,
        no_cover: req.no_cover,
    });
    let backend = parse_backend(&req.backend);
    if matches!(backend, Backend::Boxes) {
        return reset_and_start_boxes(&state.valid_job, &state, &req.formula, false);
    }
    let formula = match expand_formula(&state, &req.formula) {
        Ok(f) => f,
        Err(e) => return Json(serde_json::json!({ "error": e })),
    };
    reset_and_start(&state.valid_job, &formula, false, params,
                    backend, /*preprocess=*/ true, None)
}

async fn valid_status_handler(State(state): State<AppState>) -> Json<ClassifyStatusResponse> {
    status_handler(&state.valid_job)
}

async fn valid_cancel_handler(State(state): State<AppState>) -> Json<serde_json::Value> {
    cancel_handler(&state.valid_job)
}

async fn paths_handler(
    State(state): State<AppState>,
    Json(req): Json<PathsRequest>,
) -> Json<serde_json::Value> {
    use logic::matrix::PathParams;
    let params = Some(PathParams { paths_class_limit: req.paths_class_limit, ..Default::default() });
    if req.box_aware {
        return match build_box_context(&state, &req.formula) {
            Ok((text, ctx)) => reset_and_start(&state.paths_job, &text, req.complement, params,
                                               Backend::Backtrack, /*preprocess=*/ false, Some(ctx)),
            Err(e) => Json(serde_json::json!({ "error": e })),
        };
    }
    let formula = match expand_formula(&state, &req.formula) {
        Ok(f) => f,
        Err(e) => return Json(serde_json::json!({ "error": e })),
    };
    reset_and_start(&state.paths_job, &formula, req.complement, params,
                    Backend::Backtrack, /*preprocess=*/ false, None)
}

async fn paths_status_handler(State(state): State<AppState>) -> Json<ClassifyStatusResponse> {
    status_handler(&state.paths_job)
}

async fn paths_cancel_handler(State(state): State<AppState>) -> Json<serde_json::Value> {
    cancel_handler(&state.paths_job)
}

async fn satisfiable_handler(
    State(state): State<AppState>,
    Json(req): Json<FormulaRequest>,
) -> Json<serde_json::Value> {
    use logic::matrix::PathParams;
    let params = Some(PathParams {
        uncovered_path_limit: 1,
        paths_class_limit: usize::MAX,
        covered_prefix_limit: usize::MAX,
        no_cover: req.no_cover,
    });
    let backend = parse_backend(&req.backend);
    if matches!(backend, Backend::Boxes) {
        return reset_and_start_boxes(&state.sat_job, &state, &req.formula, true);
    }
    let formula = match expand_formula(&state, &req.formula) {
        Ok(f) => f,
        Err(e) => return Json(serde_json::json!({ "error": e })),
    };
    reset_and_start(&state.sat_job, &formula, true, params,
                    backend, /*preprocess=*/ true, None)
}

async fn satisfiable_status_handler(State(state): State<AppState>) -> Json<ClassifyStatusResponse> {
    status_handler(&state.sat_job)
}

async fn satisfiable_cancel_handler(State(state): State<AppState>) -> Json<serde_json::Value> {
    cancel_handler(&state.sat_job)
}

// ── CaDiCaL handlers ─────────────────────────────────────────────────────────

fn start_cadical_job(
    job_state: &Arc<Mutex<CaDiCaLJob>>,
    formula: &str,
    is_valid: bool,
) -> Json<serde_json::Value> {
    use logic::matrix::Matrix;

    {
        let mut job = job_state.lock().unwrap();
        if let Some(c) = job.cancel.take() { c.cancel(); }
        *job = CaDiCaLJob::default();
        job.running = true;
    }

    let matrix = match Matrix::try_from(formula) {
        Ok(m) => m,
        Err(e) => {
            let mut job = job_state.lock().unwrap();
            job.running = false;
            job.error = Some(e);
            return Json(serde_json::json!({ "ok": true }));
        }
    };

    let js = job_state.clone();
    let start = std::time::Instant::now();

    if is_valid {
        let (handle, cancel) = matrix.cadical_valid();
        { job_state.lock().unwrap().cancel = Some(cancel); }
        tokio::spawn(async move {
            let elapsed = match handle.await {
                Ok(Ok(r)) => {
                    let elapsed = start.elapsed().as_secs_f64();
                    let mut job = js.lock().unwrap();
                    let asgn = match &r.result {
                        Ok(()) => None,
                        Err(a) => Some(a.iter().map(|l| (l.var, l.neg)).collect()),
                    };
                    job.result = Some(CaDiCaLJobResult {
                        assignment: asgn,
                        learned_clauses: r.learned_clauses,
                        elapsed_secs: elapsed,
                    });
                    elapsed
                }
                Ok(Err(e)) => {
                    let elapsed = start.elapsed().as_secs_f64();
                    js.lock().unwrap().error = Some(e.to_string());
                    elapsed
                }
                Err(e) => {
                    let elapsed = start.elapsed().as_secs_f64();
                    js.lock().unwrap().error = Some(format!("task panicked: {}", e));
                    elapsed
                }
            };
            let mut job = js.lock().unwrap();
            job.running = false;
            job.cancel = None;
            // Store elapsed if not already set
            if let Some(ref mut r) = job.result
                && r.elapsed_secs == 0.0 { r.elapsed_secs = elapsed; }
        });
    } else {
        let (handle, cancel) = matrix.cadical_satisfiable();
        { job_state.lock().unwrap().cancel = Some(cancel); }
        tokio::spawn(async move {
            let elapsed = match handle.await {
                Ok(Ok(r)) => {
                    let elapsed = start.elapsed().as_secs_f64();
                    let mut job = js.lock().unwrap();
                    let asgn = match &r.result {
                        Ok(a) => Some(a.iter().map(|l| (l.var, l.neg)).collect()),
                        Err(()) => None,
                    };
                    job.result = Some(CaDiCaLJobResult {
                        assignment: asgn,
                        learned_clauses: r.learned_clauses,
                        elapsed_secs: elapsed,
                    });
                    elapsed
                }
                Ok(Err(e)) => {
                    let elapsed = start.elapsed().as_secs_f64();
                    js.lock().unwrap().error = Some(e.to_string());
                    elapsed
                }
                Err(e) => {
                    let elapsed = start.elapsed().as_secs_f64();
                    js.lock().unwrap().error = Some(format!("task panicked: {}", e));
                    elapsed
                }
            };
            let mut job = js.lock().unwrap();
            job.running = false;
            job.cancel = None;
            if let Some(ref mut r) = job.result
                && r.elapsed_secs == 0.0 { r.elapsed_secs = elapsed; }
        });
    }

    Json(serde_json::json!({ "ok": true }))
}

async fn cadical_valid_handler(
    State(state): State<AppState>,
    Json(req): Json<FormulaRequest>,
) -> Json<serde_json::Value> {
    let formula = match expand_formula(&state, &req.formula) {
        Ok(f) => f,
        Err(e) => return Json(serde_json::json!({ "error": e })),
    };
    start_cadical_job(&state.cadical_valid_job, &formula, true)
}

async fn cadical_valid_status_handler(State(state): State<AppState>) -> Json<CaDiCaLStatusResponse> {
    let job = state.cadical_valid_job.lock().unwrap();
    Json(CaDiCaLStatusResponse { result: job.result.clone(), running: job.running, error: job.error.clone() })
}

async fn cadical_valid_cancel_handler(State(state): State<AppState>) -> Json<serde_json::Value> {
    let mut job = state.cadical_valid_job.lock().unwrap();
    if let Some(c) = job.cancel.take() { c.cancel(); }
    job.running = false;
    Json(serde_json::json!({ "ok": true }))
}

async fn cadical_sat_handler(
    State(state): State<AppState>,
    Json(req): Json<FormulaRequest>,
) -> Json<serde_json::Value> {
    let formula = match expand_formula(&state, &req.formula) {
        Ok(f) => f,
        Err(e) => return Json(serde_json::json!({ "error": e })),
    };
    start_cadical_job(&state.cadical_sat_job, &formula, false)
}

async fn cadical_sat_status_handler(State(state): State<AppState>) -> Json<CaDiCaLStatusResponse> {
    let job = state.cadical_sat_job.lock().unwrap();
    Json(CaDiCaLStatusResponse { result: job.result.clone(), running: job.running, error: job.error.clone() })
}

async fn cadical_sat_cancel_handler(State(state): State<AppState>) -> Json<serde_json::Value> {
    let mut job = state.cadical_sat_job.lock().unwrap();
    if let Some(c) = job.cancel.take() { c.cancel(); }
    job.running = false;
    Json(serde_json::json!({ "ok": true }))
}

// ── Main ──────────────────────────────────────────────────────────────────────

#[tokio::main]
async fn main() {
    let server_root = std::env::var("SERVER_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|_| std::env::current_dir().expect("cannot determine working directory"));

    println!("Library root: {}", server_root.join("lib").display());

    let mut default_libs = Vec::new();
    let expr_path = server_root.join("lib").join("expr.jq");
    if let Ok(raw) = std::fs::read_to_string(&expr_path) {
        println!("Auto-loaded: {}", expr_path.display());
        match lib_entry_from_raw("expr.jq", &raw) {
            Ok(entry) => default_libs.push(entry),
            Err(e) => eprintln!("expr.jq: {e}"),
        }
    }

    let state = AppState {
        jq_libs: Arc::new(Mutex::new(default_libs)),
        compiled_boxes: Arc::new(Mutex::new(Vec::new())),
        server_root,
        valid_job: Arc::new(Mutex::new(ClassifyJob::default())),
        sat_job:   Arc::new(Mutex::new(ClassifyJob::default())),
        paths_job: Arc::new(Mutex::new(ClassifyJob::default())),
        cadical_valid_job: Arc::new(Mutex::new(CaDiCaLJob::default())),
        cadical_sat_job:   Arc::new(Mutex::new(CaDiCaLJob::default())),
    };
    for path in ["expr.jq"] {
        for st in compile_lib_boxes(&state, path, BoxesCompileRequest::default_max(), BoxesCompileRequest::default_timeout()).await {
            if let Some(e) = st.get("error").and_then(|e| e.as_str()) { eprintln!("{path}: box: {e}"); }
        }
    }

    let cors = CorsLayer::new()
        .allow_origin(Any)
        .allow_methods([Method::GET, Method::POST, Method::PUT, Method::DELETE])
        .allow_headers(Any);

    // Optional static-file serving for the pre-built frontend.  When the env
    // var `STATIC_DIR` is set and the directory exists, serve it as a
    // fallback — API routes above still take precedence.  This is how the
    // Docker image bundles the vite output alongside the Rust binary and
    // runs everything on a single port.
    let static_dir = std::env::var("STATIC_DIR").ok()
        .map(std::path::PathBuf::from)
        .filter(|p| p.is_dir());

    let mut app = Router::new()
        .route("/simplify",          post(simplify_handler))
        .route("/valid",             get(valid_status_handler).post(valid_handler))
        .route("/valid/cancel",      post(valid_cancel_handler))
        .route("/satisfiable",       get(satisfiable_status_handler).post(satisfiable_handler))
        .route("/satisfiable/cancel",post(satisfiable_cancel_handler))
        .route("/paths",             get(paths_status_handler).post(paths_handler))
        .route("/paths/cancel",      post(paths_cancel_handler))
        .route("/cadical/valid",        get(cadical_valid_status_handler).post(cadical_valid_handler))
        .route("/cadical/valid/cancel", post(cadical_valid_cancel_handler))
        .route("/cadical/sat",          get(cadical_sat_status_handler).post(cadical_sat_handler))
        .route("/cadical/sat/cancel",   post(cadical_sat_cancel_handler))
        .route("/jq",          post(jq_handler))
        .route("/jq-lib",      get(jq_lib_list_handler)
                                   .post(jq_lib_load_handler)
                                   .put(jq_lib_save_handler)
                                   .delete(jq_lib_unload_handler))
        .route("/jq-lib/file",  delete(jq_lib_delete_handler))
        .route("/jq-lib/files", get(jq_lib_files_handler))
        .route("/expand",        post(expand_handler))
        .route("/boxes",         get(boxes_list_handler))
        .route("/boxes/compile", post(boxes_compile_handler))
        .route("/boxes/table",   get(boxes_table_handler).delete(boxes_delete_handler))
        .route("/examples",    get(load_examples_handler).post(save_examples_handler))
        .with_state(state);

    if let Some(dir) = &static_dir {
        println!("Serving static files from {}", dir.display());
        app = app.fallback_service(
            tower_http::services::ServeDir::new(dir)
                .append_index_html_on_directories(true)
                .fallback(tower_http::services::ServeFile::new(dir.join("index.html"))),
        );
    }

    let app = app.layer(cors);

    let port: u16 = std::env::var("PORT").ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(3001);
    let bind = format!("0.0.0.0:{}", port);
    let listener = tokio::net::TcpListener::bind(&bind).await.unwrap();
    println!("Rust service listening on http://localhost:{}", port);
    axum::serve(listener, app).await.unwrap();
}
