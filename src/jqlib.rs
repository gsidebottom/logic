//! The jq library machinery shared by the web app and `box-compile`:
//! `.jq` file sections (`# === deps ===`, `# === tests ===`, and the box
//! declarations `# === boxes ===`), transitive preamble resolution, running a
//! filter through the `xq` engine, and turning a declared box definition into
//! its formula text.  Design: `doc/box_backend_design.md` §5.

use std::collections::HashMap;

/// Markers inside a `.jq` file that bracket structured sections.  They are
/// jq comment lines so a file that contains them is still a legal preamble
/// if something ever reads the whole file raw without splitting.
pub const DEPS_MARKER:     &str = "# === deps ===";
pub const DEPS_END_MARKER: &str = "# === end deps ===";
pub const TESTS_MARKER:    &str = "# === tests ===";

/// Parse a `.jq` file's raw contents into `(deps, library_code, tests)`.
///
/// Layout:
///   # === deps ===
///   # expr.jq         ← one per line, `# name` form (jq comment)
///   # adder.jq
///   # === end deps ===
///   ...library code...
///   # === tests ===
///   ...test filter...
///
/// Any section may be absent.  The deps block, if present, must be at the
/// start; the tests block, if present, must be after the library code.
pub fn split_file(raw: &str) -> (Vec<String>, String, String) {
    // Split tests off first (reuse the old logic).
    let (body, tests) = {
        let mut lib_end: Option<usize> = None;
        let mut tests_start: Option<usize> = None;
        let mut offset = 0usize;
        for line in raw.split_inclusive('\n') {
            let trimmed = line.trim_end_matches('\n').trim_end_matches('\r').trim_end();
            if trimmed == TESTS_MARKER {
                lib_end = Some(offset);
                tests_start = Some(offset + line.len());
                break;
            }
            offset += line.len();
        }
        match (lib_end, tests_start) {
            (Some(le), Some(ts)) => (raw[..le].to_string(), raw[ts..].to_string()),
            _ => (raw.to_string(), String::new()),
        }
    };

    // Look for a leading deps block, skipping any purely-blank lines before
    // it.  We iterate with `split_inclusive('\n')` so `line.len()` is the
    // real on-disk byte count including any `\r` — which matters on CRLF
    // files, where plain `lines()` would leave our byte offsets short and
    // slice `content` mid-way through the end marker.
    let mut deps: Vec<String> = Vec::new();
    let mut content = body.clone();
    let pieces: Vec<&str> = body.split_inclusive('\n').collect();
    let mut header_end: Option<usize> = None; // byte just past `# === end deps ===\n`
    let mut offset = 0usize;
    let mut i = 0;
    while i < pieces.len() {
        let line = pieces[i];
        let trimmed = line.trim_end_matches('\n').trim_end_matches('\r').trim_end();
        if trimmed.is_empty() {
            offset += line.len();
            i += 1;
            continue;
        }
        if trimmed == DEPS_MARKER {
            offset += line.len();
            i += 1;
            let mut closed = false;
            while i < pieces.len() {
                let inner = pieces[i];
                let t = inner.trim_end_matches('\n').trim_end_matches('\r').trim_end();
                offset += inner.len();
                i += 1;
                if t == DEPS_END_MARKER {
                    closed = true;
                    break;
                }
                // Expect "# name.jq" (jq comment with name).
                let cleaned = t.trim_start();
                let cleaned = cleaned.strip_prefix('#').unwrap_or(cleaned).trim();
                if !cleaned.is_empty() {
                    deps.push(cleaned.to_string());
                }
            }
            if closed {
                header_end = Some(offset);
            } else {
                // No closing marker — treat the file as all-content.
                deps.clear();
            }
        }
        break;
    }
    if let Some(end) = header_end {
        let end = end.min(body.len());
        content = body[end..].to_string();
    }
    (deps, content, tests)
}

/// Serialize a library to its on-disk form, writing only the sections that
/// have content.  Deps block goes at the top, tests block at the bottom.
pub fn join_file(deps: &[String], content: &str, tests: &str) -> String {
    let mut out = String::new();
    if !deps.is_empty() {
        out.push_str(DEPS_MARKER);
        out.push('\n');
        for d in deps {
            out.push_str("# ");
            out.push_str(d);
            out.push('\n');
        }
        out.push_str(DEPS_END_MARKER);
        out.push('\n');
    }
    out.push_str(content);
    if !tests.trim().is_empty() {
        if !out.ends_with('\n') { out.push('\n'); }
        out.push_str(TESTS_MARKER);
        out.push('\n');
        out.push_str(tests);
    }
    out
}

/// The transitive dependency closure of `roots` in dependency order: every
/// library after everything it depends on (and otherwise in the roots'
/// order), each once.  `deps_of(path)` yields a library's declared deps or an
/// error (unreadable, invalid path).  Cycles are reported.
pub fn resolve_lib_order(
    roots: &[String],
    deps_of: &dyn Fn(&str) -> Result<Vec<String>, String>,
) -> Result<Vec<String>, String> {
    enum State { InProgress, Done }
    fn visit(
        path: &str,
        deps_of: &dyn Fn(&str) -> Result<Vec<String>, String>,
        state: &mut HashMap<String, State>,
        stack: &mut Vec<String>,
        out: &mut Vec<String>,
    ) -> Result<(), String> {
        match state.get(path) {
            Some(State::Done) => return Ok(()),
            Some(State::InProgress) => {
                // Format a readable cycle report.
                let start = stack.iter().position(|p| p == path).unwrap_or(0);
                let cycle: Vec<String> = stack[start..].iter().cloned()
                    .chain(std::iter::once(path.to_string()))
                    .collect();
                return Err(format!("dependency cycle: {}", cycle.join(" → ")));
            }
            None => {}
        }
        if path.contains('/') || path.contains('\\') || path.contains("..") {
            return Err(format!("invalid dependency path: {}", path));
        }
        let deps = deps_of(path)?;
        state.insert(path.to_string(), State::InProgress);
        stack.push(path.to_string());
        for d in &deps {
            visit(d, deps_of, state, stack, out)?;
        }
        stack.pop();
        out.push(path.to_string());
        state.insert(path.to_string(), State::Done);
        Ok(())
    }
    let (mut state, mut stack, mut out) = (HashMap::new(), Vec::new(), Vec::new());
    for r in roots {
        visit(r, deps_of, &mut state, &mut stack, &mut out)?;
    }
    Ok(out)
}

/// Build a concatenated jq preamble from a set of root libraries, pulling in
/// their transitive dependencies in dependency order ([`resolve_lib_order`]).
/// Each library contributes its `content` (not its tests).
///
/// `roots` are the libraries the caller starts from, in order.  `overrides`
/// maps `path` → `(deps, content)` — typically the currently-loaded
/// in-memory libs plus any editor preamble override.  Unknown paths fall
/// through to a disk read from `lib_dir`.
pub fn resolve_preamble(
    roots: &[String],
    overrides: &HashMap<String, (Vec<String>, String)>,
    lib_dir: &std::path::Path,
) -> Result<String, String> {
    let disk: std::cell::RefCell<HashMap<String, (Vec<String>, String)>> = std::cell::RefCell::new(HashMap::new());
    let read = |path: &str| -> Result<(Vec<String>, String), String> {
        if let Some(v) = overrides.get(path) { return Ok(v.clone()); }
        if let Some(v) = disk.borrow().get(path) { return Ok(v.clone()); }
        let raw = std::fs::read_to_string(lib_dir.join(path))
            .map_err(|e| format!("reading dependency {}: {}", path, e))?;
        let (d, c, _t) = split_file(&raw);
        disk.borrow_mut().insert(path.to_string(), (d.clone(), c.clone()));
        Ok((d, c))
    };
    let order = resolve_lib_order(roots, &|path| read(path).map(|(d, _c)| d))?;
    let mut out = String::new();
    for path in &order {
        let (_d, content) = read(path)?;
        out.push_str(&content);
        if !content.ends_with('\n') { out.push('\n'); }
    }
    Ok(out)
}

/// Run `filter` after `preamble` through the `xq` jq engine (null input) and
/// return the emitted values as JSON.
pub fn run_filter(preamble: &str, filter: &str) -> Result<Vec<serde_json::Value>, String> {
    use xq::{module_loader::PreludeLoader, run_query, Value as XqValue};
    let combined = format!("{}{}", preamble, filter);
    let loader  = PreludeLoader();
    let context = std::iter::once(Ok::<XqValue, xq::InputError>(XqValue::Null));
    let input   = std::iter::empty::<Result<XqValue, xq::InputError>>();
    let iter = run_query(&combined, context, input, &loader).map_err(|e| e.to_string())?;
    let mut results = Vec::new();
    for item in iter {
        let v = item.map_err(|e| e.to_string())?;
        results.push(serde_json::from_str::<serde_json::Value>(&v.to_string()).map_err(|e| e.to_string())?);
    }
    Ok(results)
}

pub const BOXES_MARKER:     &str = "# === boxes ===";
pub const BOXES_END_MARKER: &str = "# === end boxes ===";

/// A box declared in a `.jq` library's `# === boxes ===` section:
/// `# name(p1;p2;…) [expose v1,v2]`.  The parameters are the box's
/// interface; any other variable the definition introduces is internal and
/// projected out unless listed in `expose`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoxDecl {
    pub name: String,
    /// Interface parameters.  Each is a *family* prefix: it binds the variable
    /// named like it and every `p_<subscript>` the definition generates.
    pub params: Vec<String>,
    /// Hidden families to add to the interface (after `params`, in this order).
    pub expose: Vec<String>,
    /// Optional jq expression defining the box (`:= …`); each parameter is
    /// bound to its name as a zero-arity definition while it is evaluated.
    /// `None` means the definition is the jq function `name(p1;…;pn)`.
    pub rhs: Option<String>,
    /// Optional jq expression defining the box's *negation* (`negation …`),
    /// evaluated like `rhs`: its formula compiles to the negative table
    /// directly — for a definition whose falsifying branches are too many to
    /// enumerate (a 9-bit ≤: over 10⁷ paths for 511 rows) but whose negation
    /// has a definition of its own (`lt(b; a; 9)`).
    pub negation: Option<String>,
    /// Per-box minimization budget: `budget cubes=N ms=M` (either key optional).
    pub budget: BoxBudget,
}

/// Minimization budget overrides of a declaration (`None` = the default).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct BoxBudget {
    pub cubes: Option<usize>,
    pub ms: Option<u64>,
}

fn parse_budget(s: &str) -> Result<BoxBudget, String> {
    let mut b = BoxBudget::default();
    for tok in s.split(|c: char| c.is_whitespace() || c == ',').filter(|t| !t.is_empty()) {
        let (k, v) = tok.split_once('=').ok_or_else(|| format!("budget: expected key=value, got {tok:?}"))?;
        match k.trim() {
            "cubes" => b.cubes = Some(v.trim().parse().map_err(|_| format!("budget cubes: not a number: {v:?}"))?),
            "ms" => b.ms = Some(v.trim().parse().map_err(|_| format!("budget ms: not a number: {v:?}"))?),
            other => return Err(format!("budget: unknown key {other:?} (cubes, ms)")),
        }
    }
    Ok(b)
}

/// Split the `# === boxes ===` … `# === end boxes ===` block out of a library's
/// content: `(content without the block, declaration lines)`.  Declarations
/// are returned without their leading `#`; the block may sit anywhere.
pub fn split_boxes(content: &str) -> (String, Vec<String>) {
    let (mut out, mut decls, mut inside) = (String::new(), Vec::new(), false);
    for line in content.split_inclusive('\n') {
        let t = line.trim_end_matches('\n').trim_end_matches('\r').trim();
        if t == BOXES_MARKER { inside = true; continue; }
        if t == BOXES_END_MARKER { inside = false; continue; }
        if inside {
            let body = t.strip_prefix('#').map(str::trim).unwrap_or(t);
            if !body.is_empty() { decls.push(body.to_string()); }
            continue;
        }
        out.push_str(line);
    }
    (out, decls)
}

/// Re-attach declarations to `content` as a `# === boxes ===` block at its end
/// (the inverse of [`split_boxes`] up to block position).
pub fn join_boxes(content: &str, decls: &[String]) -> String {
    let decls: Vec<&str> = decls.iter().map(|d| d.trim()).filter(|d| !d.is_empty()).collect();
    let mut out = content.to_string();
    if decls.is_empty() { return out; }
    if !out.is_empty() && !out.ends_with('\n') { out.push('\n'); }
    if !out.is_empty() && !out.ends_with("\n\n") { out.push('\n'); }
    out.push_str(BOXES_MARKER); out.push('\n');
    for d in decls { out.push_str("# "); out.push_str(d); out.push('\n'); }
    out.push_str(BOXES_END_MARKER); out.push('\n');
    out
}

/// Is `s` a jq-style identifier (usable as a zero-arity `def`)?
fn is_ident(s: &str) -> bool {
    let mut cs = s.chars();
    matches!(cs.next(), Some(c) if c.is_ascii_alphabetic() || c == '_') && cs.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// Parse one declaration,
/// `name(p1;p2;…) [:= <jq expression>] [expose f1,f2] [budget cubes=N ms=M]`.
pub fn parse_box_decl(body: &str) -> Result<BoxDecl, String> {
    let body = body.trim().strip_prefix('#').map(str::trim).unwrap_or(body.trim());
    let open = body.find('(').ok_or("expected name(params…)")?;
    let close = body[open..].find(')').ok_or("unclosed parameter list")? + open;
    let name = body[..open].trim().to_string();
    let params: Vec<String> = body[open + 1..close].split(';').map(|p| p.trim().to_string()).filter(|p| !p.is_empty()).collect();
    let rest = body[close + 1..].trim();
    // `budget …` is the last clause, `expose …` the one before; what precedes
    // them may be `:= <jq expression>`.
    let (rest, budget): (&str, BoxBudget) = match rest.rfind(" budget ") {
        Some(i) => (rest[..i].trim_end(), parse_budget(&rest[i + 8..])?),
        None => match rest.strip_prefix("budget ") { Some(r) => ("", parse_budget(r)?), None => (rest, BoxBudget::default()) },
    };
    let (rhs_part, expose_part): (&str, Option<&str>) = match rest.rfind(" expose ") {
        Some(i) => (&rest[..i], Some(&rest[i + 8..])),
        None => match rest.strip_prefix("expose ") { Some(r) => ("", Some(r)), None => (rest, None) },
    };
    // `negation <jq expression>` sits between the definition and `expose`
    let (rhs_part, negation): (&str, Option<String>) = match rhs_part.rfind(" negation ") {
        Some(i) => (&rhs_part[..i], Some(rhs_part[i + 10..].trim().to_string())),
        None => match rhs_part.trim().strip_prefix("negation ") { Some(r) => ("", Some(r.trim().to_string())), None => (rhs_part, None) },
    };
    if negation.as_deref().is_some_and(str::is_empty) { return Err(format!("{name}: empty expression after `negation`")); }
    let rhs_part = rhs_part.trim();
    let rhs = match rhs_part.strip_prefix(":=") {
        Some(r) if r.trim().is_empty() => return Err(format!("{name}: empty definition after `:=`")),
        Some(r) => Some(r.trim().to_string()),
        None if rhs_part.is_empty() => None,
        None => return Err(format!("unexpected text after the parameter list: {rhs_part}")),
    };
    let expose: Vec<String> = expose_part.map(|r| r.split(',').map(|p| p.trim().to_string()).filter(|p| !p.is_empty()).collect()).unwrap_or_default();
    if name.is_empty() || name.contains(char::is_whitespace) { return Err(format!("bad box name in {body:?}")); }
    if params.is_empty() { return Err(format!("{name}: a box needs at least one parameter")); }
    for p in params.iter().chain(&expose) {
        if !is_ident(p) { return Err(format!("{name}: parameter {p:?} must be an identifier (letters, digits, `_`)")); }
    }
    Ok(BoxDecl { name, params, expose, rhs, negation, budget })
}

/// All declarations in a library's content (its `# === boxes ===` block).
pub fn parse_boxes(content: &str) -> Result<Vec<BoxDecl>, String> {
    split_boxes(content).1.iter().enumerate()
        .map(|(i, d)| parse_box_decl(d).map_err(|e| format!("box declaration {}: {e}", i + 1)))
        .collect()
}

/// The formula text of a declared box.  Each parameter becomes a zero-arity
/// jq definition bound to its own name (or the given argument), so the
/// right-hand side — or the default call `name(p1;…;pn)` — can pass it to
/// any generator next to literals: `eq4(a;b) := eq(a;b;4)` evaluates
/// `def a: "a"; def b: "b"; eq(a;b;4)`.
pub fn box_formula(preamble: &str, decl: &BoxDecl, args: Option<&[String]>) -> Result<String, String> {
    let names: Vec<String> = match args {
        Some(a) if a.len() == decl.params.len() => a.to_vec(),
        Some(a) => return Err(format!("{}: expects {} arguments, got {}", decl.name, decl.params.len(), a.len())),
        None => decl.params.clone(),
    };
    let mut program = String::new();
    for (p, n) in decl.params.iter().zip(&names) { program.push_str(&format!("def {p}: \"{n}\"; ")); }
    match &decl.rhs {
        Some(r) => program.push_str(r),
        None => program.push_str(&format!("{}({})", decl.name, decl.params.join(";"))),
    }
    formula_of(preamble, decl, &program)
}

/// The formula of a declaration's `negation` clause over its parameters
/// (`None` without the clause).
pub fn box_negation_formula(preamble: &str, decl: &BoxDecl) -> Result<Option<String>, String> {
    let Some(neg) = &decl.negation else { return Ok(None) };
    let mut program = String::new();
    for p in &decl.params { program.push_str(&format!("def {p}: \"{p}\"; ")); }
    program.push_str(neg);
    formula_of(preamble, decl, &program).map(Some)
}

/// Run a definition's jq program and take its single string output.
fn formula_of(preamble: &str, decl: &BoxDecl, program: &str) -> Result<String, String> {
    let vals = run_filter(preamble, program)?;
    match vals.as_slice() {
        [serde_json::Value::String(s)] => Ok(s.clone()),
        [] => Err(format!("{}: the definition produced no output", decl.name)),
        [other] => Err(format!("{}: expected a formula string, got {other}", decl.name)),
        _ => Err(format!("{}: the definition produced {} outputs, expected one", decl.name, vals.len())),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn boxes_section() {
        let c = "def x: 1;\n# === boxes ===\n# full_adder(x;y;c_in;s;c_out)\n# adder(a;b;c_in;s;c_out;u1;u2;u3) expose u1, u2,u3\n# === end boxes ===\ndef y: 2;\n";
        let d = parse_boxes(c).unwrap();
        assert_eq!(d.len(), 2);
        assert_eq!(d[0], BoxDecl { name: "full_adder".into(), params: ["x","y","c_in","s","c_out"].map(String::from).to_vec(), expose: vec![], rhs: None, negation: None, budget: BoxBudget::default() });
        let g = parse_box_decl("le_9(a;b) := le(a; b; 9) negation lt(b; a; 9) expose c budget ms=10").unwrap();
        assert_eq!((g.rhs.as_deref(), g.negation.as_deref(), g.expose.len(), g.budget.ms), (Some("le(a; b; 9)"), Some("lt(b; a; 9)"), 1, Some(10)));
        let g = parse_box_decl("le_9(a;b) negation lt(b; a; 9)").unwrap();
        assert_eq!((g.rhs, g.negation.as_deref()), (None, Some("lt(b; a; 9)")));
        assert!(parse_box_decl("f(a;b) negation ").is_err());
        let g = parse_box_decl("plus_4(a;b;c) := plus(a; b; c; 4) budget cubes=5000000 ms=30000").unwrap();
        assert_eq!((g.rhs.as_deref(), g.budget), (Some("plus(a; b; c; 4)"), BoxBudget { cubes: Some(5_000_000), ms: Some(30_000) }));
        let g = parse_box_decl("f(a;b) expose c budget ms=10").unwrap();
        assert_eq!((g.expose.clone(), g.budget), (vec!["c".to_string()], BoxBudget { cubes: None, ms: Some(10) }));
        assert!(parse_box_decl("f(a;b) budget nodes=3").is_err());
        assert_eq!(d[1].expose, ["u1","u2","u3"].map(String::from).to_vec());
        let g = parse_box_decl("eq4(a;b) := eq(a;b;4)").unwrap();
        assert_eq!((g.params.len(), g.rhs.as_deref(), g.expose.len()), (2, Some("eq(a;b;4)"), 0));
        let g = parse_box_decl("add4(a;b;s) := add(a; b; s; 4) expose c").unwrap();
        assert_eq!((g.rhs.as_deref(), g.expose.clone()), (Some("add(a; b; s; 4)"), vec!["c".to_string()]));
        assert!(parse_box_decl("f(a;b) := ").is_err());
        assert!(parse_box_decl("f(a,b;c)").is_err());   // `a,b` is not an identifier
        assert!(parse_boxes("# === boxes ===\nnot a declaration\n# === end boxes ===").is_err());
    }

    #[test]
    fn split_join_boxes_round_trip() {
        let c = "def x: 1;\n\n# === boxes ===\n# fa(x;y)\n# === end boxes ===\ndef y: 2;\n";
        let (content, decls) = split_boxes(c);
        assert_eq!(decls, vec!["fa(x;y)".to_string()]);
        assert_eq!(content, "def x: 1;\n\ndef y: 2;\n");
        let joined = join_boxes(&content, &decls);
        assert_eq!(joined, "def x: 1;\n\ndef y: 2;\n\n# === boxes ===\n# fa(x;y)\n# === end boxes ===\n");
        let (c2, d2) = split_boxes(&joined);
        assert_eq!((c2.as_str(), d2), ("def x: 1;\n\ndef y: 2;\n\n", decls));
        assert_eq!(join_boxes("def z: 3;", &[]), "def z: 3;");
        assert!(parse_box_decl("fa x").is_err());
        assert!(parse_box_decl("fa()").is_err());
    }

    #[test]
    fn run_filter_and_box_formula() {
        let pre = "def sum(s): [s] | join(\" + \");\ndef full_adder(x;y): sum(x, y);\n";
        assert_eq!(run_filter(pre, "full_adder(\"a\";\"b\")").unwrap(), vec![serde_json::json!("a + b")]);
        let d = BoxDecl { name: "full_adder".into(), params: vec!["x".into(), "y".into()], expose: vec![], rhs: None, negation: None, budget: BoxBudget::default() };
        assert_eq!(box_formula(pre, &d, None).unwrap(), "x + y");
        assert_eq!(box_formula(pre, &d, Some(&["P".to_string(), "Q".to_string()])).unwrap(), "P + Q");
        // a right-hand side with a literal argument, parameters bound as definitions
        let pre2 = "def sum(s): [s] | join(\" + \");\ndef rep(a; n): sum(range(n) | \"\\(a)_\\(.)\");\n";
        let g = BoxDecl { name: "rep2".into(), params: vec!["a".into()], expose: vec![], rhs: Some("rep(a; 2)".into()), negation: None, budget: BoxBudget::default() };
        assert_eq!(box_formula(pre2, &g, None).unwrap(), "a_0 + a_1");
        assert_eq!(box_formula(pre2, &g, Some(&["x".to_string()])).unwrap(), "x_0 + x_1");
    }

    #[test]
    fn lib_order_is_dependency_order() {
        // diamond: app → {ui, db}, ui → core, db → core
        let deps = |p: &str| -> Result<Vec<String>, String> {
            Ok(match p {
                "app.jq" => vec!["ui.jq".into(), "db.jq".into()],
                "ui.jq" | "db.jq" => vec!["core.jq".into()],
                "core.jq" => vec![],
                "a.jq" => vec!["b.jq".into()],
                "b.jq" => vec!["a.jq".into()],
                other => return Err(format!("no such library {other}")),
            })
        };
        assert_eq!(resolve_lib_order(&["app.jq".to_string()], &deps).unwrap(), ["core.jq", "ui.jq", "db.jq", "app.jq"]);
        // roots keep their order; a root that is also a dep appears once, first
        assert_eq!(resolve_lib_order(&["db.jq".to_string(), "app.jq".to_string()], &deps).unwrap(), ["core.jq", "db.jq", "ui.jq", "app.jq"]);
        assert!(resolve_lib_order(&["a.jq".to_string()], &deps).unwrap_err().contains("dependency cycle: a.jq → b.jq → a.jq"));
        assert!(resolve_lib_order(&["zz.jq".to_string()], &deps).unwrap_err().contains("no such library"));
        assert!(resolve_lib_order(&["../x.jq".to_string()], &deps).unwrap_err().contains("invalid dependency path"));
    }

    /// Every library under `lib/` has its `# === tests ===` block evaluated
    /// with the library and its deps as the preamble — the same check the
    /// web UI runs — and every result must be `true`.  Failures are reported
    /// by test name (`cargo test library_test_blocks_pass -- --nocapture`
    /// also prints a per-library summary).
    #[test]
    fn library_test_blocks_pass() {
        let lib_dir = std::path::Path::new("lib");
        let mut libs: Vec<String> = std::fs::read_dir(lib_dir).expect("lib/ next to Cargo.toml")
            .filter_map(|e| e.ok()).map(|e| e.file_name().to_string_lossy().to_string())
            .filter(|n| n.ends_with(".jq")).collect();
        libs.sort();
        assert!(!libs.is_empty(), "no .jq libraries found in lib/");
        let (mut failures, mut summary) = (Vec::new(), Vec::new());
        for name in &libs {
            let raw = std::fs::read_to_string(lib_dir.join(name)).unwrap();
            let (_deps, _content, tests) = split_file(&raw);
            if tests.trim().is_empty() { summary.push(format!("{name}: no tests block")); continue; }
            let preamble = resolve_preamble(&[name.clone()], &std::collections::HashMap::new(), lib_dir)
                .unwrap_or_else(|e| panic!("{name}: cannot resolve the library and its deps: {e}"));
            let results = run_filter(&preamble, &tests)
                .unwrap_or_else(|e| panic!("{name}: the tests block failed to evaluate: {e}"));
            // one name per top-level comma-separated entry; only trusted when
            // the count matches (a test expression may itself contain commas)
            let names: Vec<&str> = tests.split(',').map(str::trim).filter(|s| !s.is_empty()).collect();
            let label = |i: usize| if names.len() == results.len() { names[i].to_string() } else { format!("#{}", i + 1) };
            let mut failed = 0;
            for (i, r) in results.iter().enumerate() {
                if *r != serde_json::Value::Bool(true) { failed += 1; failures.push(format!("{name}: {} → {r}", label(i))); }
            }
            summary.push(format!("{name}: {} tests, {failed} failed", results.len()));
        }
        eprintln!("{}", summary.join("\n"));
        assert!(failures.is_empty(), "jq library test failures:\n{}", failures.join("\n"));
    }
}
