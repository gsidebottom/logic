# Nested Boxes — Boolean Formula Visualizer

Renders boolean formulas as nested box diagrams. AND = vertical stack, OR = side by side.

## Run

This is a two-process app: a **Rust backend** (`web_app`, port 3001) that runs the
solvers, and this **Vite/React frontend** (port 8080) that talks to it. The manager
script at the repo root starts, stops, and monitors both:

```bash
./app.sh start          # build backend if needed, then launch backend + UI
```

Then open **http://localhost:8080**. The script installs any missing prerequisites
(Rust, bun, node), rebuilds `web_app` only when the Rust source changed, and writes
logs to `.logs/`.

Other commands:

```bash
./app.sh status         # ✓/✗ for each process and its URL
./app.sh restart        # stop + start (use this if start says "already running")
./app.sh stop           # stop both
./app.sh logs           # tail -f both logs
./app.sh monitor        # live status + log dashboard
./app.sh start -p 9000  # pick a different UI port (backend stays on 3001)
```

### Frontend only

You can run just the UI (e.g. to iterate on the diagram code), but the **Simplify**,
satisfiability, and validity buttons call the backend at `http://localhost:3001`, so
they won't work unless `web_app` is running too:

```bash
cd nested-boxes
bunx vite                # serves on http://localhost:8080 (see vite.config.js)
```

## Usage

- Type a formula in the input box — the diagram updates live
- Use `·` or `*` for AND, `+` for OR, `'` after a variable for complement
- Click **Simplify** to reduce to minimal sum-of-products form

## Example formulas

```
(A·B) + (A'+B')
A · (B + C)
(A·B') + (A'·B)
```
