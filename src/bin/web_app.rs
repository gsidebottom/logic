use axum::{extract::Json, http::Method, routing::post, Router};
use serde::{Deserialize, Serialize};
use tower_http::cors::{Any, CorsLayer};

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
        .allow_methods([Method::POST])
        .allow_headers(Any);

    let app = Router::new()
        .route("/simplify",    post(simplify_handler))
        .route("/valid",       post(valid_handler))
        .route("/satisfiable", post(satisfiable_handler))
        .layer(cors);

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3001").await.unwrap();
    println!("Rust service listening on http://localhost:3001");
    axum::serve(listener, app).await.unwrap();
}
