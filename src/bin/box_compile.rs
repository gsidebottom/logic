//! `box-compile`: compile a box definition into its table — the canonical
//! uncovered paths of the definition's complement (= its models), projected
//! onto the interface — as JSON for `sat -b boxes --boxes`.
//! Design: `doc/box_backend_design.md` §5.
//!
//! ```text
//! # from a jq library's `# === boxes ===` declarations (interface = the params)
//! box-compile --lib adder.jq --box full_adder --out full_adder.json
//! box-compile --lib adder.jq --all --out-dir boxes/
//! # or from a bare formula
//! box-compile --name full_adder --interface X,Y,C1,Z,C \
//!     --formula "(C = X Y + (X ⊕ Y) C1) (Z = X ⊕ Y ⊕ C1)" --out full_adder.json
//! ```
//!
//! Internals (variables not in the interface) are projected out — dropped
//! from every row, duplicate rows merged — unless exposed.  Rows are in model
//! polarity: `1` = true, `0` = false, `null` = don't care.

use std::collections::HashMap;

use logic::boxes::compile::{compile_box_blocking, MinimizeBudget};
use logic::jqlib::{box_formula, parse_boxes, resolve_preamble, split_file};

fn split_list(s: &str) -> Vec<String> {
    s.split(',').map(|x| x.trim().to_string()).filter(|x| !x.is_empty()).collect()
}

fn die(msg: String) -> ! { eprintln!("box-compile: {msg}"); std::process::exit(2) }

fn write_json(v: &serde_json::Value, out: Option<&str>) {
    let text = serde_json::to_string_pretty(v).unwrap();
    match out {
        Some(p) => std::fs::write(p, text).unwrap_or_else(|e| die(format!("write {p}: {e}"))),
        None => println!("{text}"),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (mut formula, mut formula_file, mut interface, mut out, mut lib, mut box_name, mut out_dir) =
        (None, None, None, None, None, None, None);
    let (mut expose, mut all) = (Vec::new(), false);
    let mut name = "box".to_string();
    let mut lib_dir = "lib".to_string();
    let mut max_paths: usize = 1_000_000;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--formula"      => formula = it.next().cloned(),
            "--formula-file" => formula_file = it.next().cloned(),
            "--interface"    => interface = it.next().map(|s| split_list(s)),
            "--expose"       => expose = it.next().map(|s| split_list(s)).unwrap_or_default(),
            "--name"         => name = it.next().cloned().unwrap_or(name),
            "--out"          => out = it.next().cloned(),
            "--out-dir"      => out_dir = it.next().cloned(),
            "--lib"          => lib = it.next().cloned(),
            "--lib-dir"      => lib_dir = it.next().cloned().unwrap_or(lib_dir),
            "--box"          => box_name = it.next().cloned(),
            "--all"          => all = true,
            "--max-paths"    => max_paths = it.next().and_then(|v| v.parse().ok()).unwrap_or(max_paths),
            other => die(format!("unknown argument {other}")),
        }
    }

    if let Some(lib) = lib {
        // Boxes declared in a jq library: interface = the declaration's parameters.
        let lib_path = std::path::Path::new(&lib_dir);
        let raw = std::fs::read_to_string(lib_path.join(&lib)).unwrap_or_else(|e| die(format!("read {lib}: {e}")));
        let (_deps, content, _tests) = split_file(&raw);
        let decls = parse_boxes(&content).unwrap_or_else(|e| die(format!("{lib}: {e}")));
        if decls.is_empty() { die(format!("{lib}: no `# === boxes ===` declarations")); }
        let preamble = resolve_preamble(std::slice::from_ref(&lib), &HashMap::new(), lib_path).unwrap_or_else(|e| die(e));
        let selected: Vec<_> = match (&box_name, all) {
            (Some(b), _) => decls.iter().filter(|d| &d.name == b).cloned().collect(),
            (None, true) => decls.clone(),
            (None, false) => die("--lib needs --box <name> or --all".into()),
        };
        if selected.is_empty() { die(format!("{lib}: no box named {}", box_name.unwrap_or_default())); }
        for d in selected {
            let formula = box_formula(&preamble, &d, None).unwrap_or_else(|e| die(e));
            let budget = MinimizeBudget::new(d.budget.cubes, d.budget.ms);
            let table = compile_box_blocking(&d.name, &formula, &d.params, &d.expose, max_paths, &budget).unwrap_or_else(|e| die(e));
            eprintln!("box-compile: {}: {} uncovered paths -> {} canonical rows over {:?} ({} internal variables projected)", d.name, table.uncovered_paths, table.rows.len(), table.vars, table.internals_projected.len());
            let table = table.to_json();
            let target = match (&out_dir, &out) {
                (Some(dir), _) => Some(format!("{dir}/{}.json", d.name)),
                (None, Some(o)) => Some(o.clone()),
                (None, None) => None,
            };
            if let Some(dir) = &out_dir { std::fs::create_dir_all(dir).unwrap_or_else(|e| die(format!("{dir}: {e}"))); }
            write_json(&table, target.as_deref());
        }
        return;
    }

    let formula = match (formula, formula_file) {
        (Some(f), _) => f,
        (None, Some(p)) => std::fs::read_to_string(&p).unwrap_or_else(|e| die(format!("read {p}: {e}"))),
        _ => die("--formula, --formula-file, or --lib required".into()),
    };
    let interface = interface.unwrap_or_default();
    if interface.is_empty() { die("--interface required".into()); }
    let table = compile_box_blocking(&name, &formula, &interface, &expose, max_paths, &MinimizeBudget::default()).unwrap_or_else(|e| die(e));
    eprintln!("box-compile: {}: {} uncovered paths -> {} canonical rows over {:?} ({} internal variables projected)", name, table.uncovered_paths, table.rows.len(), table.vars, table.internals_projected.len());
    write_json(&table.to_json(), out.as_deref());
}
