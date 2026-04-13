use axum::{
    extract::{Json, State},
    http::Method,
    routing::{get, post},
    Router,
};
use logic::matrix::{CancelHandle, Cover, PathPrefix};
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

fn build_cover_groups(pairs: &Cover, prefixes: &[PathPrefix]) -> (Vec<CoverGroup>, usize) {
    let total = pairs.len();
    let include_prefixes = total <= PREFIX_DETAIL_LIMIT;
    let mut groups: Vec<CoverGroup> = Vec::new();
    let mut map: HashMap<String, usize> = HashMap::new();
    for (pair, prefix) in pairs.iter().zip(prefixes.iter()) {
        let key = pair_key(pair);
        let len = prefix.len();
        let gi = if let Some(&gi) = map.get(&key) {
            gi
        } else {
            let gi = groups.len();
            map.insert(key, gi);
            groups.push(CoverGroup {
                pair: pair.clone(),
                count: 0,
                prefix_length_min: usize::MAX,
                prefix_length_max: 0,
                prefixes: Vec::new(),
            });
            gi
        };
        let g = &mut groups[gi];
        g.count += 1;
        g.prefix_length_min = g.prefix_length_min.min(len);
        g.prefix_length_max = g.prefix_length_max.max(len);
        if include_prefixes {
            g.prefixes.push(prefix.clone());
        }
    }
    (groups, total)
}

/// Snapshot of an in-progress paths job.
#[derive(Default, Clone)]
struct PathsSnapshot {
    uncovered_paths:          Vec<String>,
    uncovered_path_positions: Vec<Vec<Vec<usize>>>,
    cover_groups:             Vec<CoverGroup>,
    group_map:                HashMap<String, usize>,
    total_prefix_count:       usize,
    classified_count:         usize,
    hit_limit:                bool,
}

struct PathsJob {
    snapshot: PathsSnapshot,
    total_path_count:         usize,
    cancel:   Option<CancelHandle>,
    running:  bool,
    error:    Option<String>,
    is_complement: bool,
}

impl Default for PathsJob {
    fn default() -> Self {
        Self {
            snapshot: PathsSnapshot::default(),
            cancel: None,
            running: false,
            error: None,
            is_complement: false,
            total_path_count: 0,
        }
    }
}

#[derive(Clone)]
struct AppState {
    jq_libs:     Arc<Mutex<Vec<JqLibEntry>>>,
    server_root: PathBuf,
    paths_job:   Arc<Mutex<PathsJob>>,
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

#[derive(Serialize)]
struct ValidResponse {
    valid:                      Option<bool>,
    path:                       Option<String>,
    uncovered_path_positions:   Option<Vec<Vec<usize>>>,
    cover_groups:               Option<Vec<CoverGroup>>,
    total_prefix_count:         Option<usize>,
    error:                      Option<String>,
}

#[derive(Serialize)]
struct PathsStatusResponse {
    uncovered_paths:            Vec<String>,
    uncovered_path_positions:   Vec<Vec<Vec<usize>>>,
    cover_groups:               Vec<CoverGroup>,
    total_prefix_count:         usize,
    classified_count:           usize,
    total_path_count:           usize,
    hit_limit:                  bool,
    running:                    bool,
    is_complement:              bool,
    error:                      Option<String>,
}

#[derive(Serialize)]
struct SatisfiableResponse {
    satisfiable:                Option<bool>,
    path:                       Option<String>,
    uncovered_path_positions:   Option<Vec<Vec<usize>>>,
    cover_groups:               Option<Vec<CoverGroup>>,
    total_prefix_count:         Option<usize>,
    error:                      Option<String>,
}

async fn simplify_handler(Json(req): Json<FormulaRequest>) -> Json<SimplifyResponse> {
    match logic::simplify(&req.formula) {
        Ok(r)  => Json(SimplifyResponse { result: Some(r), error: None }),
        Err(e) => Json(SimplifyResponse { result: None,    error: Some(e) }),
    }
}

async fn valid_handler(Json(req): Json<FormulaRequest>) -> Json<ValidResponse> {
    match logic::check_valid(&req.formula) {
        Ok((v, path, positions, pairs, prefixes)) => {
            let (groups, total) = build_cover_groups(&pairs, &prefixes);
            Json(ValidResponse {
                valid: Some(v), path,
                uncovered_path_positions: positions,
                cover_groups: Some(groups),
                total_prefix_count: Some(total),
                error: None,
            })
        }
        Err(e) => Json(ValidResponse { valid: None, path: None, uncovered_path_positions: None, cover_groups: None, total_prefix_count: None, error: Some(e) }),
    }
}

/// Start a streaming paths job. Cancels any in-progress job, parses the
/// formula, and spawns a drainer task that incrementally fills the shared
/// `PathsJob` snapshot from the `classify_paths` channel. Returns immediately.
async fn paths_handler(
    State(state): State<AppState>,
    Json(req): Json<PathsRequest>,
) -> Json<serde_json::Value> {
    use logic::matrix::{Matrix, format_path, PathParams, PathsClass};

    // Cancel + reset existing job.
    {
        let mut job = state.paths_job.lock().unwrap();
        if let Some(c) = job.cancel.take() { c.cancel(); }
        *job = PathsJob::default();
        job.running = true;
        job.is_complement = req.complement;
    }

    let matrix = match Matrix::try_from(req.formula.as_str()) {
        Ok(m) => m,
        Err(e) => {
            let mut job = state.paths_job.lock().unwrap();
            job.running = false;
            job.error = Some(e);
            return Json(serde_json::json!({ "ok": true }));
        }
    };

    let target_nnf = if req.complement { &matrix.nnf_complement } else { &matrix.nnf };
    let total_path_count = target_nnf.path_count();
    let target = target_nnf.clone();
    let vars = matrix.ast.vars.clone();

    let params = Some(PathParams { paths_class_limit: req.paths_class_limit, ..Default::default() });
    let (handle, mut rx, cancel) = matrix.classify_paths(req.complement, 64, params);
    {
        let mut job = state.paths_job.lock().unwrap();
        job.cancel = Some(cancel);
        job.total_path_count = total_path_count;
    }

    let job_state = state.paths_job.clone();
    tokio::spawn(async move {
        while let Some((class, hit_limit)) = rx.recv().await {
            let mut job = job_state.lock().unwrap();
            match class {
                PathsClass::Covered(cp) => {
                    let key = pair_key(&cp.cover);
                    let len = cp.prefix.len();
                    let snap = &mut job.snapshot;
                    snap.total_prefix_count += 1;
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
                    job.snapshot.uncovered_paths.push(format_path(&p, &target, &vars));
                    job.snapshot.uncovered_path_positions.push(target.positions_on_path(&p));
                }
            }
            job.snapshot.classified_count += 1;
            if hit_limit { job.snapshot.hit_limit = true; }
        }
        let _ = handle.await;
        let mut job = job_state.lock().unwrap();
        job.running = false;
        job.cancel = None;
    });

    Json(serde_json::json!({ "ok": true }))
}

async fn paths_status_handler(State(state): State<AppState>) -> Json<PathsStatusResponse> {
    let job = state.paths_job.lock().unwrap();
    Json(PathsStatusResponse {
        uncovered_paths:          job.snapshot.uncovered_paths.clone(),
        uncovered_path_positions: job.snapshot.uncovered_path_positions.clone(),
        cover_groups:             job.snapshot.cover_groups.clone(),
        total_prefix_count:       job.snapshot.total_prefix_count,
        classified_count:         job.snapshot.classified_count,
        total_path_count:         job.total_path_count,
        hit_limit:                job.snapshot.hit_limit,
        running:                  job.running,
        is_complement:            job.is_complement,
        error:                    job.error.clone(),
    })
}

async fn paths_cancel_handler(State(state): State<AppState>) -> Json<serde_json::Value> {
    let mut job = state.paths_job.lock().unwrap();
    if let Some(c) = job.cancel.take() { c.cancel(); }
    job.running = false;
    Json(serde_json::json!({ "ok": true }))
}

async fn satisfiable_handler(Json(req): Json<FormulaRequest>) -> Json<SatisfiableResponse> {
    match logic::check_satisfiable(&req.formula) {
        Ok((s, path, positions, pairs, prefixes)) => {
            let (groups, total) = build_cover_groups(&pairs, &prefixes);
            Json(SatisfiableResponse {
                satisfiable: Some(s), path,
                uncovered_path_positions: positions,
                cover_groups: Some(groups),
                total_prefix_count: Some(total),
                error: None,
            })
        }
        Err(e) => Json(SatisfiableResponse { satisfiable: None, path: None, uncovered_path_positions: None, cover_groups: None, total_prefix_count: None, error: Some(e) }),
    }
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
        paths_job: Arc::new(Mutex::new(PathsJob::default())),
    };

    let cors = CorsLayer::new()
        .allow_origin(Any)
        .allow_methods([Method::GET, Method::POST, Method::DELETE])
        .allow_headers(Any);

    let app = Router::new()
        .route("/simplify",    post(simplify_handler))
        .route("/valid",       post(valid_handler))
        .route("/satisfiable", post(satisfiable_handler))
        .route("/paths",        get(paths_status_handler).post(paths_handler))
        .route("/paths/cancel", post(paths_cancel_handler))
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
