# Nested Boxes — Boolean Formula Visualizer

Renders boolean formulas as nested box diagrams. AND = vertical stack, OR = side by side.

## Run

```bash
cd nested-boxes
bunx vite
```

Then open http://localhost:5173 in your browser.

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
