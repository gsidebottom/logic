# Docker

This repository packages as a single container that serves both the Rust
backend and the built React frontend on one port.

## Quick start

```sh
# Build the image (~3–5 minutes first time; CaDiCaL's C++ compile dominates).
docker build -t logic .

# Run it — open http://localhost:3001
docker run --rm -p 3001:3001 logic
```

Or with compose (adds host bind-mounts so library edits persist):

```sh
docker compose up --build
```

The image is self-contained: the Rust binary serves every API route **and**
the static Vite bundle at `/`, so there's just one origin, one port, no CORS
configuration needed for end users.

## What's in the image

Three Docker stages, final runtime ~120 MB:

1. **`rust:1.88-bookworm`** — builds `target/release/web_app`.
   - Installs `clang`, `libc++-dev`, `libc++abi-dev` so the `cadical` crate
     can compile its vendored C++ sources.
   - `cargo build --release --bin web_app --locked`.
2. **`oven/bun:1-debian`** — builds the frontend.
   - `bun install` using the committed `bun.lock`.
   - `bunx vite build` → `dist/`.
3. **`debian:bookworm-slim`** — runtime layer.
   - Installs only `libc++1`, `libc++abi1`, `ca-certificates`.
   - Copies in `web_app` → `/usr/local/bin/`.
   - Copies `dist/` → `/app/static` (frontend bundle).
   - Copies `lib/` → `/app/lib` (jq libraries).
   - Copies `examples.json` → `/app/examples.json`.
   - `EXPOSE 3001`, `CMD ["/usr/local/bin/web_app"]`.

## Environment variables

| Variable     | Default              | Effect                                                                        |
|--------------|----------------------|-------------------------------------------------------------------------------|
| `PORT`       | `3001`               | HTTP port the backend binds (`0.0.0.0:$PORT`).                                 |
| `STATIC_DIR` | `/app/static` (set by Dockerfile) | When set and pointing at an existing directory, the backend serves that directory at `/` as a fallback after the API routes. `index.html` is also returned for unknown paths so SPA deep-links work. Unset it if you want API-only. |

You can override either on the command line:

```sh
docker run --rm -p 8080:8080 -e PORT=8080 logic
```

## Persistence (volumes)

By default, changes to jq libraries or the examples file live only inside the
container and vanish on `docker rm`.  To keep them across restarts, bind-mount
the two writable paths from the host:

```sh
docker run --rm -p 3001:3001 \
    -v "$PWD/lib:/app/lib" \
    -v "$PWD/examples.json:/app/examples.json" \
    logic
```

The provided `docker-compose.yml` does this for you:

```yaml
services:
  logic:
    build: .
    image: logic:latest
    ports: ["3001:3001"]
    volumes:
      - ./lib:/app/lib
      - ./examples.json:/app/examples.json
    restart: unless-stopped
```

Comment the `volumes:` block out for a fully ephemeral container.

## How the single-port trick works

- The frontend defines one module-level constant:

  ```js
  const API_BASE = import.meta.env.PROD ? '' : 'http://localhost:3001';
  ```

  In `vite dev` it still points at the standalone Rust service on port 3001
  (so the `./app.sh start` workflow keeps working unchanged).  In the
  production build Vite substitutes `''`, so every `fetch` becomes a
  relative URL — same-origin as whichever host the user reaches the
  container on.

- The backend's router registers a `tower_http::services::ServeDir` fallback
  **after** all API routes, plus a `ServeFile` for `index.html`.  API paths
  take priority; anything else falls through to the static bundle.

Because the browser only ever talks to one origin, there's no CORS issue
and no hard-coded hostname — it works whether you hit the container on
`localhost`, a LAN IP, or a domain behind a reverse proxy.

## Rebuilding

Code changes need a rebuild of the affected stage:

```sh
# After editing Rust or JSX.  Docker layer caching reuses the apt and
# toolchain layers; only the cargo and vite steps re-run.
docker build -t logic .
```

Force a completely fresh build (ignore all layer caches):

```sh
docker build --no-cache -t logic .
```

## Running behind a reverse proxy

The backend binds `0.0.0.0:$PORT`, so standard forwarding works:

```nginx
location / {
    proxy_pass       http://127.0.0.1:3001;
    proxy_set_header Host              $host;
    proxy_set_header X-Real-IP         $remote_addr;
    proxy_set_header X-Forwarded-For   $proxy_add_x_forwarded_for;
    proxy_set_header X-Forwarded-Proto $scheme;
}
```

No extra configuration is needed because API calls are relative URLs.

## Troubleshooting

**Stage 1 (Rust) fails with "feature `edition2024` is required".**  The
`Cargo.toml` uses edition 2024.  The Dockerfile pins `rust:1.88-bookworm`
which supports it.  If you forked to a different Rust version, bump the base
image.

**Stage 1 fails with "rustc X.Y is not supported by … time@…".**  Same cause
— a too-old Rust toolchain.  Bump the `rust:` tag.

**"Could not reach Rust service" from the frontend.**  In the Docker image
this shouldn't happen because API_BASE is `''`.  If you see it, you're
probably running the **dev** build pointed at `localhost:3001` but the
backend isn't reachable there.  For the container, make sure you are using
the production build that lives in `dist/` (the image is, unconditionally).

**CORS preflight errors.**  Only happens on the dev (`vite dev`) workflow
against an external backend.  The Dockerized build is same-origin so CORS
doesn't apply.  If you're mixing the two (e.g. dev frontend against
Dockerized backend) ensure the backend's `CorsLayer` allows the methods
you use; the current layer allows `GET`, `POST`, `PUT`, `DELETE`.

**Container starts but `/lib/*.jq` edits don't persist.**  You forgot the
volume mounts.  Either run with `-v ./lib:/app/lib -v ./examples.json:/app/examples.json`
or use `docker compose up`.

## Useful commands

```sh
# Smoke-test a running container.
curl -s http://localhost:3001/ | head -c 100                   # should be HTML
curl -s http://localhost:3001/jq-lib | head -c 200             # loaded libs
curl -s -X POST -H 'content-type: application/json' \
    -d '{"formula":"a+b"}' http://localhost:3001/simplify      # API works

# Shell into the running container.
docker exec -it <container-id> /bin/bash

# Check the actual binary mtime inside the image (sanity for "am I running
# the build I think I'm running?").
docker run --rm logic stat /usr/local/bin/web_app
```
