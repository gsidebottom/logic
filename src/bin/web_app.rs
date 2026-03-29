use axum::{extract::Json, http::Method, routing::post, Router};
use serde::{Deserialize, Serialize};
use tower_http::cors::{Any, CorsLayer};

#[derive(Deserialize)]
struct SimplifyRequest {
    formula: String,
}

#[derive(Serialize)]
struct SimplifyResponse {
    result: Option<String>,
    error: Option<String>,
}

async fn simplify_handler(Json(req): Json<SimplifyRequest>) -> Json<SimplifyResponse> {
    match logic::simplify(&req.formula) {
        Ok(result) => Json(SimplifyResponse { result: Some(result), error: None }),
        Err(e) => Json(SimplifyResponse { result: None, error: Some(e) }),
    }
}

#[tokio::main]
async fn main() {
    let cors = CorsLayer::new()
        .allow_origin(Any)
        .allow_methods([Method::POST])
        .allow_headers(Any);

    let app = Router::new()
        .route("/simplify", post(simplify_handler))
        .layer(cors);

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3001").await.unwrap();
    println!("Rust simplify service listening on http://localhost:3001");
    axum::serve(listener, app).await.unwrap();
}
