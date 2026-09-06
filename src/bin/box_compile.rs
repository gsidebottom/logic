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

use std::collections::{HashMap, HashSet};

use logic::controller::SmartController;
use logic::jqlib::{box_formula, parse_boxes, resolve_preamble, split_file};
use logic::matrix::{DynOnClass, Matrix, PathParams, PathsClass};

fn split_list(s: &str) -> Vec<String> {
    s.split(',').map(|x| x.trim().to_string()).filter(|x| !x.is_empty()).collect()
}

fn die(msg: String) -> ! { eprintln!("box-compile: {msg}"); std::process::exit(2) }

/// Enumerate the definition's models (uncovered paths of its complement) and
/// project them onto `cols`.  Returns the table as JSON.
fn compile_box(name: &str, formula: &str, cols: &[String]) -> serde_json::Value {
    let m = Matrix::try_from(formula.trim()).unwrap_or_else(|e| die(format!("{name}: parse error: {e}")));
    let names = m.ast.vars.clone();
    for c in cols {
        if !names.contains(c) { eprintln!("box-compile: warning: {name}: column {c} does not occur in the formula"); }
    }
    let internals: Vec<String> = names.iter().filter(|n| !cols.contains(n)).cloned().collect();
    let col_of: HashMap<&str, usize> = cols.iter().enumerate().map(|(i, c)| (c.as_str(), i)).collect();
    let nnf = m.nnf_complement.clone();
    let params = Some(PathParams {
        paths_class_limit: usize::MAX / 2, uncovered_path_limit: usize::MAX / 2, ..Default::default()
    });
    let rt = tokio::runtime::Builder::new_multi_thread().enable_all().build().expect("tokio runtime");
    let (set, n_uncovered) = rt.block_on(async {
        let nnf_for_builder = nnf.clone();
        let (handle, mut rx, _cancel) = nnf.classify_paths_uncovered_only(
            64,
            move |tx: tokio::sync::mpsc::Sender<(PathsClass, bool)>| {
                let on_class: DynOnClass =
                    Box::new(move |class, hit_limit| tx.blocking_send((class, hit_limit)).is_ok());
                SmartController::for_nnf(&nnf_for_builder, params, on_class)
            },
        );
        let mut set: HashSet<Vec<Option<bool>>> = HashSet::new();
        let mut n = 0usize;
        while let Some((class, _hit_limit)) = rx.recv().await {
            if let PathsClass::Uncovered(up) = class {
                n += 1;
                // A path literal is made FALSE by the model (§2.2): model value = l.neg.
                let mut row = vec![None; cols.len()];
                for l in &up.lits {
                    if let Some(&ci) = col_of.get(names[l.var as usize].as_str()) { row[ci] = Some(l.neg); }
                }
                set.insert(row);
            }
        }
        let _ = handle.await;
        (set, n)
    });
    let mut rows: Vec<Vec<Option<bool>>> = set.into_iter().collect();
    rows.sort();
    eprintln!("box-compile: {name}: {n_uncovered} uncovered paths -> {} canonical rows over {:?} ({} internal variables projected)",
              rows.len(), cols, internals.len());
    serde_json::json!({
        "name": name,
        "vars": cols,
        "rows": rows.iter().map(|r| r.iter().map(|c| match c {
            Some(true) => serde_json::Value::from(1), Some(false) => serde_json::Value::from(0), None => serde_json::Value::Null,
        }).collect::<Vec<_>>()).collect::<Vec<_>>(),
        "formula": formula.trim(),
        "internals_projected": internals,
        "uncovered_paths": n_uncovered,
    })
}

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
        let preamble = resolve_preamble(&[lib.clone()], &HashMap::new(), lib_path).unwrap_or_else(|e| die(e));
        let selected: Vec<_> = match (&box_name, all) {
            (Some(b), _) => decls.iter().filter(|d| &d.name == b).cloned().collect(),
            (None, true) => decls.clone(),
            (None, false) => die("--lib needs --box <name> or --all".into()),
        };
        if selected.is_empty() { die(format!("{lib}: no box named {}", box_name.unwrap_or_default())); }
        for d in selected {
            let formula = box_formula(&preamble, &d, None).unwrap_or_else(|e| die(e));
            let mut cols = d.params.clone();
            for e in &d.expose { if !cols.contains(e) { cols.push(e.clone()); } }
            let table = compile_box(&d.name, &formula, &cols);
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
    let mut cols = interface;
    for e in &expose { if !cols.contains(e) { cols.push(e.clone()); } }
    write_json(&compile_box(&name, &formula, &cols), out.as_deref());
}
