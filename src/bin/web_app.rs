use axum::{
    extract::{Json, State},
    http::Method,
    routing::{get, post},
    Router,
};
use logic::matrix::CancelHandle;
use serde::{Deserialize, Serialize};
use std::{collections::HashMap, path::PathBuf, sync::{Arc, Mutex}};
use tower_http::cors::{Any, CorsLayer};
use xq::{module_loader::PreludeLoader, run_query, Value as XqValue};

// ── App state ─────────────────────────────────────────────────────────────────

#[derive(Clone, Serialize)]
struct JqLibEntry {
    path:    String,
    name:    String,
    content: String,
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
}

struct ClassifyJob {
    snapshot: ClassifySnapshot,
    total_path_count:         f64,
    start_time:               Option<std::time::Instant>,
    cancel:   Option<CancelHandle>,
    running:  bool,
    error:    Option<String>,
    is_complement: bool,
}

impl Default for ClassifyJob {
    fn default() -> Self {
        Self {
            snapshot: ClassifySnapshot::default(),
            cancel: None,
            running: false,
            error: None,
            is_complement: false,
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

struct CaDiCaLJob {
    result:   Option<CaDiCaLJobResult>,
    cancel:   Option<CancelHandle>,
    running:  bool,
    error:    Option<String>,
}

impl Default for CaDiCaLJob {
    fn default() -> Self {
        Self { result: None, cancel: None, running: false, error: None }
    }
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
    server_root: PathBuf,
    valid_job:   Arc<Mutex<ClassifyJob>>,
    sat_job:     Arc<Mutex<ClassifyJob>>,
    paths_job:   Arc<Mutex<ClassifyJob>>,
    cadical_valid_job: Arc<Mutex<CaDiCaLJob>>,
    cadical_sat_job:   Arc<Mutex<CaDiCaLJob>>,
}

// ── jq handlers ───────────────────────────────────────────────────────────────

#[derive(Deserialize)]
struct JqRequest {
    filter: String,
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
    let libs = state.jq_libs.lock().unwrap().clone();

    let mut preamble = String::new();
    for lib in &libs {
        preamble.push_str(&lib.content);
        preamble.push('\n');
    }

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

async fn jq_lib_load_handler(
    State(state): State<AppState>,
    Json(req): Json<JqLibRequest>,
) -> Json<serde_json::Value> {
    let full_path = state.server_root.join("lib").join(&req.path);

    let content = match std::fs::read_to_string(&full_path) {
        Ok(c)   => c,
        Err(e)  => return Json(serde_json::json!({ "error": e.to_string() })),
    };

    let name = match full_path.file_stem().and_then(|s| s.to_str()) {
        Some(n) => n.to_string(),
        None    => return Json(serde_json::json!({ "error": "invalid file path" })),
    };

    let mut libs = state.jq_libs.lock().unwrap();
    if let Some(pos) = libs.iter().position(|e| e.path == req.path) {
        libs[pos] = JqLibEntry { path: req.path, name, content };
    } else {
        libs.push(JqLibEntry { path: req.path, name, content });
    }

    Json(serde_json::json!({ "ok": true }))
}

async fn jq_lib_unload_handler(
    State(state): State<AppState>,
    Json(req): Json<JqLibRequest>,
) -> Json<serde_json::Value> {
    state.jq_libs.lock().unwrap().retain(|e| e.path != req.path);
    Json(serde_json::json!({ "ok": true }))
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
}

fn classify_status(job: &ClassifyJob) -> ClassifyStatusResponse {
    ClassifyStatusResponse {
        uncovered_paths:          job.snapshot.uncovered_paths.clone(),
        uncovered_path_positions: job.snapshot.uncovered_path_positions.clone(),
        cover_groups:             job.snapshot.cover_groups.clone(),
        total_prefix_count:       job.snapshot.total_prefix_count,
        classified_count:         job.snapshot.classified_count,
        total_path_count:         job.total_path_count,
        elapsed_secs:             job.start_time.map_or(0.0, |t| t.elapsed().as_secs_f64()),
        hit_limit:                job.snapshot.hit_limit,
        running:                  job.running,
        is_complement:            job.is_complement,
        error:                    job.error.clone(),
    }
}

async fn simplify_handler(Json(req): Json<SimplifyRequest>) -> Json<SimplifyResponse> {
    let result = if req.cnf {
        logic::simplify_cnf(&req.formula)
    } else {
        logic::simplify_dnf(&req.formula)
    };
    match result {
        Ok(r)  => Json(SimplifyResponse { result: Some(r), error: None }),
        Err(e) => Json(SimplifyResponse { result: None,    error: Some(e) }),
    }
}

/// Start a classify job: parse formula, launch `classify_paths`, spawn drainer.
fn start_classify_job(
    job_state: Arc<Mutex<ClassifyJob>>,
    formula: &str,
    complement: bool,
    params: Option<logic::matrix::PathParams>,
) -> Result<(), String> {
    use logic::matrix::{Matrix, format_path, PathsClass, NNF};

    let matrix = Matrix::try_from(formula).map_err(|e| e)?;
    let target_nnf: &NNF = if complement { &matrix.nnf_complement } else { &matrix.nnf };
    let total_path_count = target_nnf.path_count();
    let target = target_nnf.clone();
    let vars = matrix.ast.vars.clone();

    let (handle, mut rx, cancel) = matrix.classify_paths(complement, 64, params);
    {
        let mut job = job_state.lock().unwrap();
        job.cancel = Some(cancel);
        job.total_path_count = total_path_count;
        job.start_time = Some(std::time::Instant::now());
    }

    let js = job_state.clone();
    tokio::spawn(async move {
        while let Some((class, hit_limit)) = rx.recv().await {
            let mut job = js.lock().unwrap();
            match class {
                PathsClass::Covered(cp) => {
                    let cover_count = target.prefix_cover_count(&cp.prefix);
                    let key = pair_key(&cp.cover);
                    let len = cp.prefix.len();
                    let snap = &mut job.snapshot;
                    snap.total_prefix_count += 1;
                    snap.classified_count += cover_count;
                    let gi = if let Some(&gi) = snap.group_map.get(&key) {
                        gi
                    } else {
                        let gi = snap.cover_groups.len();
                        snap.group_map.insert(key, gi);
                        snap.cover_groups.push(CoverGroup {
                            pair: cp.cover,
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
                        g.prefixes.push(cp.prefix);
                    } else if snap.total_prefix_count == PREFIX_DETAIL_LIMIT + 1 {
                        for grp in &mut snap.cover_groups {
                            grp.prefixes.clear();
                        }
                    }
                }
                PathsClass::Uncovered(p) => {
                    job.snapshot.classified_count += 1.0;
                    job.snapshot.uncovered_paths.push(format_path(&p, &target, &vars));
                    job.snapshot.uncovered_path_positions.push(target.positions_on_path(&p));
                }
            }
            if hit_limit { job.snapshot.hit_limit = true; }
        }
        let _ = handle.await;
        let mut job = js.lock().unwrap();
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

fn reset_and_start(
    job_state: &Arc<Mutex<ClassifyJob>>,
    formula: &str,
    complement: bool,
    params: Option<logic::matrix::PathParams>,
) -> Json<serde_json::Value> {
    {
        let mut job = job_state.lock().unwrap();
        if let Some(c) = job.cancel.take() { c.cancel(); }
        *job = ClassifyJob::default();
        job.running = true;
        job.is_complement = complement;
    }
    if let Err(e) = start_classify_job(job_state.clone(), formula, complement, params) {
        let mut job = job_state.lock().unwrap();
        job.running = false;
        job.error = Some(e);
    }
    Json(serde_json::json!({ "ok": true }))
}

fn status_handler(job_state: &Arc<Mutex<ClassifyJob>>) -> Json<ClassifyStatusResponse> {
    let job = job_state.lock().unwrap();
    Json(classify_status(&job))
}

fn cancel_handler(job_state: &Arc<Mutex<ClassifyJob>>) -> Json<serde_json::Value> {
    let mut job = job_state.lock().unwrap();
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
    reset_and_start(&state.valid_job, &req.formula, false, params)
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
    reset_and_start(&state.paths_job, &req.formula, req.complement, params)
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
    reset_and_start(&state.sat_job, &req.formula, true, params)
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
            if let Some(ref mut r) = job.result {
                if r.elapsed_secs == 0.0 { r.elapsed_secs = elapsed; }
            }
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
            if let Some(ref mut r) = job.result {
                if r.elapsed_secs == 0.0 { r.elapsed_secs = elapsed; }
            }
        });
    }

    Json(serde_json::json!({ "ok": true }))
}

async fn cadical_valid_handler(
    State(state): State<AppState>,
    Json(req): Json<FormulaRequest>,
) -> Json<serde_json::Value> {
    start_cadical_job(&state.cadical_valid_job, &req.formula, true)
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
    start_cadical_job(&state.cadical_sat_job, &req.formula, false)
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
    if let Ok(content) = std::fs::read_to_string(&expr_path) {
        println!("Auto-loaded: {}", expr_path.display());
        default_libs.push(JqLibEntry {
            path:    "expr.jq".to_string(),
            name:    "expr".to_string(),
            content,
        });
    }

    let state = AppState {
        jq_libs: Arc::new(Mutex::new(default_libs)),
        server_root,
        valid_job: Arc::new(Mutex::new(ClassifyJob::default())),
        sat_job:   Arc::new(Mutex::new(ClassifyJob::default())),
        paths_job: Arc::new(Mutex::new(ClassifyJob::default())),
        cadical_valid_job: Arc::new(Mutex::new(CaDiCaLJob::default())),
        cadical_sat_job:   Arc::new(Mutex::new(CaDiCaLJob::default())),
    };

    let cors = CorsLayer::new()
        .allow_origin(Any)
        .allow_methods([Method::GET, Method::POST, Method::DELETE])
        .allow_headers(Any);

    let app = Router::new()
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
                                   .delete(jq_lib_unload_handler))
        .route("/jq-lib/files", get(jq_lib_files_handler))
        .route("/examples",    get(load_examples_handler).post(save_examples_handler))
        .with_state(state)
        .layer(cors);

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3001").await.unwrap();
    println!("Rust service listening on http://localhost:3001");
    axum::serve(listener, app).await.unwrap();
}
