use axum::{
    extract::{Json, State},
    http::Method,
    routing::{get, post},
    Router,
};
use serde::{Deserialize, Serialize};
use std::{path::PathBuf, sync::{Arc, Mutex}};
use tower_http::cors::{Any, CorsLayer};
use xq::{module_loader::PreludeLoader, run_query, Value as XqValue};

// ── App state ─────────────────────────────────────────────────────────────────

#[derive(Clone, Serialize)]
struct JqLibEntry {
    path:    String,
    name:    String,
    content: String,
}

#[derive(Clone)]
struct AppState {
    jq_libs:     Arc<Mutex<Vec<JqLibEntry>>>,
    server_root: PathBuf,
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

#[derive(Serialize)]
struct SimplifyResponse {
    result: Option<String>,
    error:  Option<String>,
}

#[derive(Serialize)]
struct ValidResponse {
    valid:          Option<bool>,
    path:           Option<String>,
    covering_pairs: Option<Vec<String>>,
    error:          Option<String>,
}

#[derive(Serialize)]
struct PathsResponse {
    paths:         Option<Vec<String>>,
    complementary: Option<Vec<bool>>,
    error:         Option<String>,
}

#[derive(Serialize)]
struct SatisfiableResponse {
    satisfiable:    Option<bool>,
    path:           Option<String>,
    covering_pairs: Option<Vec<String>>,
    error:          Option<String>,
}

async fn simplify_handler(Json(req): Json<FormulaRequest>) -> Json<SimplifyResponse> {
    match logic::simplify(&req.formula) {
        Ok(r)  => Json(SimplifyResponse { result: Some(r), error: None }),
        Err(e) => Json(SimplifyResponse { result: None,    error: Some(e) }),
    }
}

async fn valid_handler(Json(req): Json<FormulaRequest>) -> Json<ValidResponse> {
    match logic::check_valid(&req.formula) {
        Ok((v, path, pairs)) => Json(ValidResponse {
            valid: Some(v), path,
            covering_pairs: if v { Some(pairs) } else { None },
            error: None,
        }),
        Err(e) => Json(ValidResponse { valid: None, path: None, covering_pairs: None, error: Some(e) }),
    }
}

async fn paths_handler(Json(req): Json<FormulaRequest>) -> Json<PathsResponse> {
    match logic::get_paths(&req.formula) {
        Ok((paths, comp)) => Json(PathsResponse { paths: Some(paths), complementary: Some(comp), error: None }),
        Err(e)            => Json(PathsResponse { paths: None, complementary: None, error: Some(e) }),
    }
}

async fn satisfiable_handler(Json(req): Json<FormulaRequest>) -> Json<SatisfiableResponse> {
    match logic::check_satisfiable(&req.formula) {
        Ok((s, path, pairs)) => Json(SatisfiableResponse {
            satisfiable: Some(s), path,
            covering_pairs: if !s { Some(pairs) } else { None },
            error: None,
        }),
        Err(e) => Json(SatisfiableResponse { satisfiable: None, path: None, covering_pairs: None, error: Some(e) }),
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
    };

    let cors = CorsLayer::new()
        .allow_origin(Any)
        .allow_methods([Method::GET, Method::POST, Method::DELETE])
        .allow_headers(Any);

    let app = Router::new()
        .route("/simplify",    post(simplify_handler))
        .route("/valid",       post(valid_handler))
        .route("/satisfiable", post(satisfiable_handler))
        .route("/paths",       post(paths_handler))
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
