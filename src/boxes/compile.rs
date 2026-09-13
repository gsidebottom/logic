//! Box compilation: a definition's models — the canonical uncovered paths of
//! its complement — projected onto the interface, as a [`Table`] that can be
//! instantiated into a [`TableBox`] over concrete variables.  Shared by the
//! `box-compile` CLI and the web app's `/boxes/compile` endpoint.
//! Design: `doc/box_backend_design.md` §5.

use std::collections::{HashMap, HashSet};
use super::expand::family_of;

use super::TableBox;
use crate::controller::SmartController;
use crate::matrix::{DynOnClass, Lit, Matrix, PathParams, PathsClass};

/// A compiled box: rows in model polarity over `vars` (`None` = don't care).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Table {
    pub name: String,
    /// Interface families in call order (parameters, then exposed families).
    /// Every column belongs to exactly one (`expand::family_of`).
    pub params: Vec<String>,
    /// Columns: the members of each family in turn, in subscript order.
    pub vars: Vec<String>,
    pub rows: Vec<Vec<Option<bool>>>,
    pub formula: String,
    pub internals_projected: Vec<String>,
    pub uncovered_paths: usize,
}

impl Table {
    /// JSON form: rows as `1` / `0` / `null`.
    pub fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "name": self.name,
            "params": self.params,
            "vars": self.vars,
            "rows": self.rows.iter().map(|r| r.iter().map(|c| match c {
                Some(true) => serde_json::Value::from(1),
                Some(false) => serde_json::Value::from(0),
                None => serde_json::Value::Null,
            }).collect::<Vec<_>>()).collect::<Vec<_>>(),
            "formula": self.formula,
            "internals_projected": self.internals_projected,
            "uncovered_paths": self.uncovered_paths,
        })
    }

    /// Parse the JSON form (cells may be `1`/`0`/`null` or `true`/`false`/`null`).
    pub fn from_json(v: &serde_json::Value) -> Result<Table, String> {
        let strs = |key: &str| -> Vec<String> {
            v[key].as_array().map(|a| a.iter().filter_map(|x| x.as_str().map(String::from)).collect()).unwrap_or_default()
        };
        let vars = strs("vars");
        if vars.is_empty() { return Err("table: missing \"vars\"".into()); }
        let params = { let p = strs("params"); if p.is_empty() { vars.clone() } else { p } };
        let rows_v = v["rows"].as_array().ok_or("table: missing \"rows\"")?;
        let mut rows = Vec::with_capacity(rows_v.len());
        for r in rows_v {
            let cells = r.as_array().ok_or("table: row is not an array")?;
            if cells.len() != vars.len() { return Err(format!("table: row has {} cells, expected {}", cells.len(), vars.len())); }
            rows.push(cells.iter().map(|c| match c {
                serde_json::Value::Null => Ok(None),
                serde_json::Value::Bool(b) => Ok(Some(*b)),
                serde_json::Value::Number(n) => match n.as_i64() { Some(1) => Ok(Some(true)), Some(0) => Ok(Some(false)), _ => Err(format!("table: bad cell {c}")) },
                other => Err(format!("table: bad cell {other}")),
            }).collect::<Result<Vec<_>, String>>()?);
        }
        Ok(Table {
            params,
            name: v["name"].as_str().unwrap_or("box").to_string(),
            vars, rows,
            formula: v["formula"].as_str().unwrap_or("").to_string(),
            internals_projected: strs("internals_projected"),
            uncovered_paths: v["uncovered_paths"].as_u64().unwrap_or(0) as usize,
        })
    }

    /// Bind the columns to 0-based variables and build the engine's box.
    pub fn instantiate(&self, args: &[u32]) -> Result<TableBox, String> {
        if args.len() != self.vars.len() {
            return Err(format!("{}: expects {} arguments, instance has {}", self.name, self.vars.len(), args.len()));
        }
        let rows = self.rows.iter().map(|r| {
            r.iter().enumerate().filter_map(|(ci, c)| c.map(|b| Lit { var: args[ci], neg: !b })).collect()
        }).collect();
        Ok(TableBox::new(rows))
    }
}


/// How a call binds one table column: to a (possibly complemented) variable
/// of the enclosing problem, or to a constant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArgBinding {
    Var { id: u32, neg: bool },
    Const(bool),
}

impl Table {
    /// Rows of this table over the problem's variables, for one call.
    /// A complemented argument flips the column; a constant filters the rows
    /// (and drops the column).
    pub fn instantiate_args(&self, args: &[ArgBinding]) -> Result<Vec<Vec<Lit>>, String> {
        if args.len() != self.vars.len() {
            return Err(format!("{}: expects {} arguments, call has {}", self.name, self.vars.len(), args.len()));
        }
        let mut out = Vec::with_capacity(self.rows.len());
        'rows: for r in &self.rows {
            let mut lits = Vec::new();
            for (ci, c) in r.iter().enumerate() {
                let Some(b) = *c else { continue };
                match args[ci] {
                    ArgBinding::Var { id, neg } => lits.push(Lit { var: id, neg: !(b ^ neg) }),
                    ArgBinding::Const(k) => if k != b { continue 'rows; },
                }
            }
            out.push(lits);
        }
        Ok(out)
    }

    /// The table of the box's negation over the same columns: every full
    /// assignment of the columns matched by no row.  Exact for projected boxes
    /// (¬∃U.B = ∀U.¬B); rows are full assignments (no don't-cares).  Errors when
    /// the column count exceeds `max_cols` (2^k enumeration).
    pub fn complement(&self, max_cols: usize) -> Result<Table, String> {
        let k = self.vars.len();
        if k > max_cols {
            return Err(format!("{}: negative table needs 2^{k} assignments over {k} columns (limit {max_cols})", self.name));
        }
        let mut rows = Vec::new();
        for a in 0u64..(1u64 << k) {
            let asg: Vec<bool> = (0..k).map(|i| (a >> i) & 1 == 1).collect();
            let covered = self.rows.iter().any(|r| r.iter().zip(&asg).all(|(c, &v)| c.is_none_or(|b| b == v)));
            if !covered { rows.push(asg.iter().map(|&v| Some(v)).collect()); }
        }
        let rows = minimize_rows(rows, k);
        Ok(Table { name: format!("{}'", self.name), params: self.params.clone(), vars: self.vars.clone(), rows, formula: format!("({})'", self.formula),
                   internals_projected: self.internals_projected.clone(), uncovered_paths: 0 })
    }
}

/// The table `sel = sel_value ⇒ (one of `rows`)`: every row gets the selector
/// literal, plus one escape row that only fixes the selector to the other
/// value.  With `sel_value = true` this is `atom ⇒ box`; with `false`,
/// `¬atom ⇒ ¬box` when `rows` is the negative table — together they make the
/// atom equivalent to the box (§2.2: two tables per box).
pub fn implication_box(rows: Vec<Vec<Lit>>, sel: u32, sel_value: bool) -> TableBox {
    let mut all: Vec<Vec<Lit>> = Vec::with_capacity(rows.len() + 1);
    all.push(vec![Lit { var: sel, neg: sel_value }]);          // escape: sel ≠ sel_value
    for mut r in rows {
        r.push(Lit { var: sel, neg: !sel_value });               // sel = sel_value
        all.push(r);
    }
    TableBox::new(all)
}


/// Columns up to which tables are minimized (the function is enumerated over
/// 2^k assignments — the same cap as the negative-table complement).
pub const MINIMIZE_MAX_COLS: usize = 20;

/// The assignment indices (bit i = column i) a row with don't-cares covers.
fn cube_minterms(row: &[Option<bool>]) -> Vec<usize> {
    let mut base = 0usize;
    let mut dcs = Vec::new();
    for (i, c) in row.iter().enumerate() {
        match c { Some(true) => base |= 1 << i, Some(false) => {}, None => dcs.push(i) }
    }
    (0..1usize << dcs.len()).map(|m| {
        let mut idx = base;
        for (j, &i) in dcs.iter().enumerate() { if (m >> j) & 1 == 1 { idx |= 1 << i; } }
        idx
    }).collect()
}

/// Minimize a table's rows — a DNF cover with don't-cares — to an irredundant
/// cover by prime implicants, without changing the set of assignments covered:
/// EXPAND grows every row to a maximal cube (a fixed column becomes a
/// don't-care when the flipped half-cube also lies inside the function), then
/// IRREDUNDANT drops rows covered by the others (smallest first).  Row counts
/// then no longer depend on how the definition was written — `lt + eq` and
/// `¬lt(b;a)` compile to covers of the same size — and fewer, wider rows
/// propagate faster.  Rows are returned sorted.  Left unchanged when the box
/// has more than [`MINIMIZE_MAX_COLS`] columns.
pub fn minimize_rows(rows: Vec<Vec<Option<bool>>>, k: usize) -> Vec<Vec<Option<bool>>> {
    if k > MINIMIZE_MAX_COLS || rows.is_empty() { return rows; }
    let mut f = vec![false; 1usize << k];
    for r in &rows { for m in cube_minterms(r) { f[m] = true; } }
    // EXPAND
    let mut cubes: HashSet<Vec<Option<bool>>> = HashSet::new();
    for r in &rows {
        let mut cube = r.clone();
        for c in 0..k {
            if let Some(v) = cube[c] {
                let mut flipped = cube.clone();
                flipped[c] = Some(!v);
                if cube_minterms(&flipped).into_iter().all(|m| f[m]) { cube[c] = None; }
            }
        }
        cubes.insert(cube);
    }
    // IRREDUNDANT: smallest cubes first
    let mut cubes: Vec<Vec<Option<bool>>> = cubes.into_iter().collect();
    cubes.sort_by_key(|c| (c.iter().filter(|x| x.is_none()).count(), c.clone()));
    let mut count = vec![0u32; 1usize << k];
    for c in &cubes { for m in cube_minterms(c) { count[m] += 1; } }
    let mut kept = Vec::with_capacity(cubes.len());
    for c in cubes {
        let ms = cube_minterms(&c);
        if ms.iter().all(|&m| count[m] >= 2) { for m in ms { count[m] -= 1; } } else { kept.push(c); }
    }
    kept.sort();
    kept
}

/// Sort key for the members of a family: the bare name first, then integer
/// subscripts numerically (`a_2` before `a_10`, lists lexicographic), then
/// other subscripts alphabetically.
fn subscript_key(name: &str, prefix: &str) -> (u8, Vec<i64>, String) {
    let suffix = name[prefix.len()..].trim_start_matches('_');
    if suffix.is_empty() { return (0, Vec::new(), String::new()); }
    match suffix.split(',').map(|p| p.parse::<i64>()).collect::<Result<Vec<_>, _>>() {
        Ok(nums) => (1, nums, String::new()),
        Err(_) => (2, Vec::new(), suffix.to_string()),
    }
}

/// The interface of a definition over its variables `names`: the families
/// `params ++ expose` (a family is a name prefix, see `expand::family_of`),
/// their member columns in subscript order, and the hidden variables.
pub fn interface_columns(names: &[String], params: &[String], expose: &[String]) -> (Vec<String>, Vec<String>, Vec<String>) {
    let mut families: Vec<String> = params.to_vec();
    for e in expose { if !families.contains(e) { families.push(e.clone()); } }
    let mut cols = Vec::new();
    for (fi, f) in families.iter().enumerate() {
        let mut members: Vec<&String> = names.iter().filter(|n| family_of(n, &families) == Some(fi)).collect();
        members.sort_by_key(|n| subscript_key(n, f));
        cols.extend(members.into_iter().cloned());
    }
    let hidden = names.iter().filter(|n| family_of(n, &families).is_none()).cloned().collect();
    (families, cols, hidden)
}

/// Compile a definition into its table over the interface `params ++ expose`
/// (families of variables — see [`interface_columns`]): enumerate the
/// uncovered paths of the complement, decode each to model polarity, project
/// onto the interface columns (every other variable is hidden — ∃), dedup,
/// and minimize ([`minimize_rows`]).  Must run inside a tokio runtime; errors
/// if more than `max_uncovered_paths` paths are found.
pub async fn compile_box(name: &str, formula: &str, params: &[String], expose: &[String], max_uncovered_paths: usize) -> Result<Table, String> {
    compile_box_polarity(name, formula, params, expose, max_uncovered_paths, false).await
}

/// Like [`compile_box`]; with `negate` the table of the *complement* of the
/// definition is compiled (its uncovered paths are those of the definition's
/// own NNF).  Only exact when nothing is projected: ¬(∃U.B) ≠ ∃U.¬B — use
/// [`Table::complement`] for a box with projected internals.
pub async fn compile_box_polarity(name: &str, formula: &str, params: &[String], expose: &[String], max_uncovered_paths: usize, negate: bool) -> Result<Table, String> {
    let (names, nnf) = {
        let m = Matrix::try_from(formula.trim()).map_err(|e| format!("{name}: parse error: {e}"))?;
        (m.ast.vars.clone(), if negate { m.nnf.clone() } else { m.nnf_complement.clone() })
    };
    let (families, cols, internals) = interface_columns(&names, params, expose);
    let col_of: HashMap<String, usize> = cols.iter().enumerate().map(|(i, c)| (c.clone(), i)).collect();
    let params = Some(PathParams {
        paths_class_limit: usize::MAX / 2, uncovered_path_limit: max_uncovered_paths, ..Default::default()
    });
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
    let (mut n, mut hit) = (0usize, false);
    while let Some((class, hit_limit)) = rx.recv().await {
        if hit_limit { hit = true; }
        if let PathsClass::Uncovered(up) = class {
            n += 1;
            // A path literal is made FALSE by the model (§2.2): model value = l.neg.
            let mut row = vec![None; cols.len()];
            for l in &up.lits {
                if let Some(&ci) = col_of.get(&names[l.var as usize]) { row[ci] = Some(l.neg); }
            }
            set.insert(row);
        }
    }
    let _ = handle.await;
    if hit {
        return Err(format!("{name}: more than {max_uncovered_paths} uncovered paths — raise the limit or split the box"));
    }
    let rows = minimize_rows(set.into_iter().collect(), cols.len());
    Ok(Table {
        name: name.to_string(), params: families, vars: cols, rows,
        formula: formula.trim().to_string(), internals_projected: internals, uncovered_paths: n,
    })
}

/// [`compile_box`] on a private runtime, for command-line use.
pub fn compile_box_blocking(name: &str, formula: &str, params: &[String], expose: &[String], max_uncovered_paths: usize) -> Result<Table, String> {
    let rt = tokio::runtime::Builder::new_multi_thread().enable_all().build().map_err(|e| e.to_string())?;
    rt.block_on(compile_box(name, formula, params, expose, max_uncovered_paths))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn adder_compiles_to_its_truth_table() {
        let cols: Vec<String> = ["X", "Y", "C1", "Z", "C"].map(String::from).to_vec();
        let t = compile_box_blocking("full_adder", "(C = X Y + (X ⊕ Y) C1) (Z = X ⊕ Y ⊕ C1)", &cols, &[], 100_000).unwrap();
        assert_eq!(t.rows.len(), 8);
        for r in &t.rows {
            let v = |i: usize| r[i].unwrap() as u32;
            assert_eq!(v(3), (v(0) + v(1) + v(2)) & 1);          // Z = sum bit
            assert_eq!(v(4), ((v(0) + v(1) + v(2)) >> 1) & 1);   // C = carry
        }
        let back = Table::from_json(&t.to_json()).unwrap();
        assert_eq!(back, t);
        let b = t.instantiate(&[0, 1, 2, 3, 4]).unwrap();
        assert_eq!(b.rows.len(), 8);
        assert!(t.instantiate(&[0, 1]).is_err());
    }

    #[test]
    fn projection_drops_internals() {
        let cols: Vec<String> = ["X", "Y", "C1", "Z", "C"].map(String::from).to_vec();
        let five = "(U1 = X Y) (U2 = U3 C1) (C = U1+U2) (U3 = X ⊕ Y) (Z = U3 ⊕ C1)";
        let t = compile_box_blocking("adder", five, &cols, &[], 100_000).unwrap();
        assert_eq!(t.internals_projected, ["U1", "U2", "U3"].map(String::from).to_vec());
        let two = compile_box_blocking("full_adder", "(C = X Y + (X ⊕ Y) C1) (Z = X ⊕ Y ⊕ C1)", &cols, &[], 100_000).unwrap();
        assert_eq!(t.rows, two.rows, "∃U.adder == full_adder as tables");
    }

    #[test]
    fn arg_bindings_constants_and_complement() {
        let t = Table { name: "and".into(), params: vec!["a".into(), "b".into(), "z".into()], vars: vec!["a".into(), "b".into(), "z".into()],
            rows: vec![vec![Some(true), Some(true), Some(true)], vec![Some(false), None, Some(false)], vec![None, Some(false), Some(false)]],
            formula: "z = a b".into(), internals_projected: vec![], uncovered_paths: 3 };
        // z = a b with a := x', b := 1, z := y  →  y = x'
        let rows = t.instantiate_args(&[ArgBinding::Var { id: 0, neg: true }, ArgBinding::Const(true), ArgBinding::Var { id: 1, neg: false }]).unwrap();
        assert_eq!(rows, vec![
            vec![Lit { var: 0, neg: true }, Lit { var: 1, neg: false }],   // a=1 ⇒ x=0, z=1
            vec![Lit { var: 0, neg: false }, Lit { var: 1, neg: true }],   // a=0 ⇒ x=1, z=0
        ]);                                                                 // row 3 (b=0) filtered by b := 1
        let c = t.complement(8).unwrap();
        // z = a b has 4 non-models of (a,b,z); minimized to the 3 primes (0,-,1), (-,0,1), (1,1,0)
        assert_eq!(c.rows.len(), 3);
        assert!(c.rows.iter().all(|r| cube_minterms(r).into_iter().all(|m| { let (a, b, z) = (m & 1 == 1, m & 2 == 2, m & 4 == 4); z != (a && b) })));
        // atom ⇒ box: the escape row plus each row tagged with the atom
        let ib = implication_box(rows.clone(), 5, true);
        assert_eq!(ib.rows.len(), 3);
        let mut e = crate::boxes::Engine::new(6, vec![ib, TableBox::clause(&[6]), TableBox::clause(&[1])]);   // atom=true, x=true ⇒ y=false
        match e.solve() { crate::boxes::Verdict::Sat(m) => assert!(!m[1]), v => panic!("{v:?}") }
    }

    #[test]
    fn families_group_subscripted_variables_and_hide_the_rest() {
        let (fam, cols, hidden) = interface_columns(
            &["b_10", "a_2", "a_0", "c_1", "a", "b_1"].map(String::from), &["a".into(), "b".into()], &[]);
        assert_eq!(fam, ["a", "b"].map(String::from).to_vec());
        assert_eq!(cols, ["a", "a_0", "a_2", "b_1", "b_10"].map(String::from).to_vec());   // numeric subscript order
        assert_eq!(hidden, vec!["c_1".to_string()]);
        // a 2-bit equality box: 4 columns, 4 rows
        let t = compile_box_blocking("eq2", "(a_0 = b_0) (a_1 = b_1)", &["a".into(), "b".into()], &[], 100_000).unwrap();
        assert_eq!(t.params, ["a", "b"].map(String::from).to_vec());
        assert_eq!(t.vars, ["a_0", "a_1", "b_0", "b_1"].map(String::from).to_vec());
        assert_eq!(t.rows.len(), 4);
        // a carry family c_* is hidden unless exposed
        let f = "(c_1 = a_0 b_0) (s_0 = a_0 ⊕ b_0) (s_1 = c_1 ⊕ a_1 ⊕ b_1)";
        let h = compile_box_blocking("half2", f, &["a".into(), "b".into(), "s".into()], &[], 100_000).unwrap();
        assert_eq!(h.internals_projected, vec!["c_1".to_string()]);
        assert_eq!(h.vars, ["a_0", "a_1", "b_0", "b_1", "s_0", "s_1"].map(String::from).to_vec());
        assert_eq!(h.rows.len(), 16);
        let e = compile_box_blocking("half2", f, &["a".into(), "b".into(), "s".into()], &["c".into()], 100_000).unwrap();
        assert_eq!(e.params, ["a", "b", "s", "c"].map(String::from).to_vec());
        assert_eq!(e.vars.last().map(String::as_str), Some("c_1"));
        assert!(e.internals_projected.is_empty());
        let j = e.to_json(); let back = Table::from_json(&j).unwrap();
        assert_eq!(back.params, e.params);
    }

    #[test]
    fn minimization_is_exact_and_formula_independent() {
        // Coverage is preserved and every kept row is a prime implicant.
        let rows = vec![vec![Some(false), Some(false)], vec![Some(false), Some(true)], vec![Some(true), Some(true)]];
        let m = minimize_rows(rows.clone(), 2);
        let cover = |rs: &Vec<Vec<Option<bool>>>| { let mut v: Vec<usize> = rs.iter().flat_map(|r| cube_minterms(r)).collect(); v.sort(); v.dedup(); v };
        assert_eq!(cover(&m), cover(&rows));
        assert_eq!(m, vec![vec![None, Some(true)], vec![Some(false), None]]);   // b + a' (sorted)
        // a ≤ b over 4-bit vectors has 23 prime implicants, all essential: the
        // minimum cover is 23 rows however the relation is written — as
        // lt + eq, or as the negation of lt(b; a).
        let lt = |a: &str, b: &str| -> String {
            (0..4).rev().map(|i| {
                let mut t: Vec<String> = ((i + 1)..4).map(|j| format!("({a}_{j} = {b}_{j})")).collect();
                t.push(format!("{a}_{i}' {b}_{i}"));
                t.join(" ")
            }).collect::<Vec<_>>().join(" + ")
        };
        let eq: String = (0..4).map(|i| format!("(a_{i} = b_{i})")).collect::<Vec<_>>().join(" ");
        let le = format!("{} + {}", lt("a", "b"), eq);
        let ab = ["a".to_string(), "b".to_string()];
        let le_t = compile_box_blocking("le4", &le, &ab, &[], 100_000).unwrap();
        assert_eq!(le_t.rows.len(), 23);
        let rt = tokio::runtime::Builder::new_multi_thread().enable_all().build().unwrap();
        let lt_ba_neg = rt.block_on(compile_box_polarity("lt4", &lt("b", "a"), &ab, &[], 100_000, true)).unwrap();
        assert_eq!(lt_ba_neg.rows.len(), 23);
        assert_eq!(cover(&le_t.rows), cover(&lt_ba_neg.rows));   // the same 136 assignments
        assert_eq!(cover(&le_t.rows).len(), 136);
    }
}
