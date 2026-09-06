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

/// Build a concatenated jq preamble from a set of root libraries, pulling in
/// their transitive dependencies in topological order.  Each library
/// contributes its `content` (not its tests).  Cycles are reported.
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
    enum State { InProgress, Done }
    let mut state: HashMap<String, State> = HashMap::new();
    let mut out = String::new();

    fn visit(
        path: &str,
        overrides: &HashMap<String, (Vec<String>, String)>,
        lib_dir: &std::path::Path,
        state: &mut HashMap<String, State>,
        stack: &mut Vec<String>,
        out: &mut String,
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
        let (deps, content) = match overrides.get(path) {
            Some(v) => v.clone(),
            None => {
                let raw = std::fs::read_to_string(lib_dir.join(path))
                    .map_err(|e| format!("reading dependency {}: {}", path, e))?;
                let (d, c, _t) = split_file(&raw);
                (d, c)
            }
        };
        state.insert(path.to_string(), State::InProgress);
        stack.push(path.to_string());
        for d in &deps {
            visit(d, overrides, lib_dir, state, stack, out)?;
        }
        stack.pop();
        out.push_str(&content);
        if !content.ends_with('\n') { out.push('\n'); }
        state.insert(path.to_string(), State::Done);
        Ok(())
    }

    let mut stack = Vec::new();
    for r in roots {
        visit(r, overrides, lib_dir, &mut state, &mut stack, &mut out)?;
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
    pub params: Vec<String>,
    pub expose: Vec<String>,
}

/// Parse the `# === boxes ===` … `# === end boxes ===` block of a library's
/// content.  Lines are jq comments, so the block is inert for jq itself.
pub fn parse_boxes(content: &str) -> Result<Vec<BoxDecl>, String> {
    let mut out = Vec::new();
    let mut inside = false;
    for (i, line) in content.lines().enumerate() {
        let t = line.trim();
        if t == BOXES_MARKER { inside = true; continue; }
        if t == BOXES_END_MARKER { inside = false; continue; }
        if !inside || t.is_empty() { continue; }
        let body = t.strip_prefix('#').ok_or_else(|| format!("line {}: box declarations must be comment lines", i + 1))?.trim();
        if body.is_empty() { continue; }
        let open = body.find('(').ok_or_else(|| format!("line {}: expected name(params…)", i + 1))?;
        let close = body[open..].find(')').ok_or_else(|| format!("line {}: unclosed parameter list", i + 1))? + open;
        let name = body[..open].trim().to_string();
        let params: Vec<String> = body[open + 1..close].split(';').map(|p| p.trim().to_string()).filter(|p| !p.is_empty()).collect();
        let rest = body[close + 1..].trim();
        let expose: Vec<String> = match rest.strip_prefix("expose") {
            Some(r) => r.split(',').map(|p| p.trim().to_string()).filter(|p| !p.is_empty()).collect(),
            None if rest.is_empty() => Vec::new(),
            None => return Err(format!("line {}: unexpected text after the parameter list: {rest}", i + 1)),
        };
        if name.is_empty() || params.is_empty() { return Err(format!("line {}: bad box declaration", i + 1)); }
        out.push(BoxDecl { name, params, expose });
    }
    Ok(out)
}

/// The formula text of a declared box: call its jq definition with the formal
/// parameter names (or `args`) as the variable names.
pub fn box_formula(preamble: &str, decl: &BoxDecl, args: Option<&[String]>) -> Result<String, String> {
    let names: Vec<String> = match args {
        Some(a) if a.len() == decl.params.len() => a.to_vec(),
        Some(a) => return Err(format!("{}: expects {} arguments, got {}", decl.name, decl.params.len(), a.len())),
        None => decl.params.clone(),
    };
    let call = format!("{}({})", decl.name, names.iter().map(|n| format!("\"{n}\"")).collect::<Vec<_>>().join(";"));
    let vals = run_filter(preamble, &call)?;
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
        assert_eq!(d[0], BoxDecl { name: "full_adder".into(), params: ["x","y","c_in","s","c_out"].map(String::from).to_vec(), expose: vec![] });
        assert_eq!(d[1].expose, ["u1","u2","u3"].map(String::from).to_vec());
        assert!(parse_boxes("# === boxes ===\nnot a comment\n# === end boxes ===").is_err());
    }

    #[test]
    fn run_filter_and_box_formula() {
        let pre = "def sum(s): [s] | join(\" + \");\ndef full_adder(x;y): sum(x, y);\n";
        assert_eq!(run_filter(pre, "full_adder(\"a\";\"b\")").unwrap(), vec![serde_json::json!("a + b")]);
        let d = BoxDecl { name: "full_adder".into(), params: vec!["x".into(), "y".into()], expose: vec![] };
        assert_eq!(box_formula(pre, &d, None).unwrap(), "x + y");
        assert_eq!(box_formula(pre, &d, Some(&["P".to_string(), "Q".to_string()])).unwrap(), "P + Q");
    }
}
