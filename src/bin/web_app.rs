use axum::{extract::Json, http::Method, routing::{get, post}, Router};
use serde::{Deserialize, Serialize};
use tower_http::cors::{Any, CorsLayer};
use xq::{run_query, Value as XqValue, module_loader::PreludeLoader};

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

#[derive(Deserialize)]
struct JqRequest {
    filter: String,
}

#[derive(Serialize)]
struct JqResponse {
    results: Option<Vec<serde_json::Value>>,
    error:   Option<String>,
}

async fn jq_handler(Json(req): Json<JqRequest>) -> Json<JqResponse> {
    let loader = PreludeLoader();
    let context = std::iter::once(Ok::<XqValue, xq::InputError>(XqValue::Null));
    let input   = std::iter::empty::<Result<XqValue, xq::InputError>>();
    match run_query(&req.filter, context, input, &loader) {
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

const EXAMPLES_FILE: &str = "examples.json";

#[derive(Serialize, Deserialize, Clone)]
struct Example {
    label: String,
    f:     String,
}

async fn load_examples_handler() -> Json<serde_json::Value> {
    match std::fs::read_to_string(EXAMPLES_FILE) {
        Err(_)        => Json(serde_json::json!({ "examples": null })),
        Ok(content)   => match serde_json::from_str::<Vec<Example>>(&content) {
            Err(e)    => Json(serde_json::json!({ "error": e.to_string() })),
            Ok(list)  => Json(serde_json::json!({ "examples": list })),
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

#[tokio::main]
async fn main() {
    let cors = CorsLayer::new()
        .allow_origin(Any)
        .allow_methods([Method::GET, Method::POST])
        .allow_headers(Any);

    let app = Router::new()
        .route("/simplify",    post(simplify_handler))
        .route("/valid",       post(valid_handler))
        .route("/satisfiable", post(satisfiable_handler))
        .route("/paths",       post(paths_handler))
        .route("/jq",          post(jq_handler))
        .route("/examples",    get(load_examples_handler).post(save_examples_handler))
        .layer(cors);

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3001").await.unwrap();
    println!("Rust service listening on http://localhost:3001");
    axum::serve(listener, app).await.unwrap();
}
