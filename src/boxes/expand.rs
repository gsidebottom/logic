//! Box calls in the formula language (`doc/box_backend_design.md` §5.2):
//! `name(a1, a2, …)` (or `name(a1; a2; …)`) refers to a compiled box.
//!
//! Two consumers share one scanner:
//! * [`expand_box_calls`] — substitute the arguments for the box's parameters
//!   in its definition, rename its projected internals freshly per call site
//!   (they are local — the ∃ of §2.4), and recurse, so every formula-level
//!   backend and the diagram see an ordinary formula.
//! * [`atomize_box_calls`] — replace each call by a fresh atom `BOXCALL_k` and
//!   record the call, so the `boxes` backend and the box-aware paths view can
//!   treat the call as a unit (a table constraint on the atom's polarity).
//!
//! An unknown box or a wrong argument count is an error.
//!
//! Call vs. juxtaposition: `name(` starts a call when the parenthesised text is
//! an argument list and either `name` is a known box, or there are two or more
//! arguments (or none, or `;` separators).  `A(B+C)` and `A(B)` keep their old
//! meaning (AND by juxtaposition).  Inside an argument list a comma continues a
//! name only within a numeric subscript (`d_0,1`); elsewhere it separates
//! arguments, so `x,y` is two arguments even though `x,y` is one variable
//! name in the rest of the language.

use std::collections::HashSet;

/// The interface family a variable belongs to: the longest parameter `p` with
/// `name == p` or `name` starting with `p_` (a parameter is a name prefix — a
/// bit vector `a` owns `a_0, a_1, …`; a plain variable is a family of one).
pub fn family_of(name: &str, params: &[String]) -> Option<usize> {
    let mut best: Option<usize> = None;
    for (i, p) in params.iter().enumerate() {
        let member = name == p || (name.len() > p.len() && name.starts_with(p.as_str()) && name.as_bytes()[p.len()] == b'_');
        if member && best.is_none_or(|b| p.len() > params[b].len()) { best = Some(i); }
    }
    best
}

/// What expansion needs to know about a compiled box.
#[derive(Clone, Debug)]
pub struct BoxSig {
    /// The call's arguments bind to these families, in order (parameters, then
    /// exposed families).
    pub params: Vec<String>,
    /// Projected internals of the definition: renamed `<name>__<k>` per call site.
    pub internals: Vec<String>,
    /// The definition, over `params` and `internals`.
    pub formula: String,
}

/// One argument of a box call, as written.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Arg {
    /// A variable, possibly complemented (`x'` binds the parameter to ¬x).
    Var { name: String, neg: bool },
    /// The constant `0` or `1`.
    Const(bool),
}

impl Arg {
    fn parse(s: &str) -> Arg {
        match s {
            "0" => Arg::Const(false),
            "1" => Arg::Const(true),
            _ => match s.strip_suffix('\'') {
                Some(base) => Arg::Var { name: base.to_string(), neg: true },
                None => Arg::Var { name: s.to_string(), neg: false },
            },
        }
    }
    fn text(&self) -> String {
        match self {
            Arg::Const(b) => if *b { "1".into() } else { "0".into() },
            Arg::Var { name, neg } => if *neg { format!("{name}'") } else { name.clone() },
        }
    }
}

/// A box call replaced by an atom (see [`atomize_box_calls`]).
#[derive(Clone, Debug)]
pub struct BoxCall {
    /// The variable standing for the call in the atomized text (`BOXCALL_k`).
    pub atom: String,
    pub name: String,
    pub args: Vec<Arg>,
    /// Display label: `name(a1;a2;…)` — `;` never continues a name, so the label
    /// re-parses unambiguously and splits cleanly inside path strings.
    pub label: String,
}

/// Result of [`atomize_box_calls`].
#[derive(Clone, Debug, Default)]
pub struct Atomized {
    pub text: String,
    pub calls: Vec<BoxCall>,
}

/// Prefix of the atoms standing for box calls in atomized text.
pub const ATOM_PREFIX: &str = "BOXCALL_";

fn is_name_char(c: char) -> bool { c.is_alphanumeric() || c == '_' || c == ',' }

/// Read a name at `i` (`chars[i]` is ASCII-alphabetic).  `in_args` applies the
/// subscript-comma rule; otherwise commas are part of the name, as in the
/// tokenizer.
fn read_name(chars: &[char], mut i: usize, in_args: bool) -> (String, usize) {
    let mut name = String::new();
    let mut in_subscript = false;
    while i < chars.len() {
        let c = chars[i];
        if c == '_' { in_subscript = true; }
        else if c == ',' {
            if in_args && !(in_subscript && i + 1 < chars.len() && chars[i + 1].is_ascii_digit()) { break; }
        } else if !c.is_alphanumeric() { break; }
        name.push(c);
        i += 1;
    }
    (name, i)
}

/// Parse an argument list starting at `chars[i] == '('`.  `None` if the text is
/// not an argument list (an operator inside, an unclosed paren, …).
/// Returns `(args, index after ')', used a ';')`.
fn parse_args(chars: &[char], mut i: usize) -> Option<(Vec<String>, usize, bool)> {
    i += 1;
    let (mut args, mut semi) = (Vec::new(), false);
    loop {
        while i < chars.len() && chars[i].is_whitespace() { i += 1; }
        if i >= chars.len() { return None; }
        if chars[i] == ')' {
            return if args.is_empty() { Some((args, i + 1, semi)) } else { None };  // trailing separator
        }
        let mut name = if chars[i].is_ascii_alphabetic() {
            let (n, j) = read_name(chars, i, true); i = j; n
        } else if chars[i] == '0' || chars[i] == '1' {
            let n = chars[i].to_string(); i += 1; n
        } else { return None; };
        let mut k = i;
        while k < chars.len() && chars[k].is_whitespace() { k += 1; }
        let mut primes = 0;
        while k < chars.len() && chars[k] == '\'' { primes += 1; k += 1; }
        if primes > 0 { i = k; if primes % 2 == 1 { name.push('\''); } }
        args.push(name);
        while i < chars.len() && chars[i].is_whitespace() { i += 1; }
        if i >= chars.len() { return None; }
        match chars[i] {
            ')' => return Some((args, i + 1, semi)),
            ',' => i += 1,
            ';' => { semi = true; i += 1; }
            _ => return None,
        }
    }
}

/// Substitute a call's arguments for the parameter families in the definition
/// (`a_3` with `a := x` becomes `x_3`; a primed argument primes each member; a
/// constant replaces every member), and give the hidden internals
/// call-site-unique names.
fn substitute(sig: &BoxSig, args: &[String], k: usize) -> String {
    let internals: HashSet<&str> = sig.internals.iter().map(String::as_str).collect();
    let chars: Vec<char> = sig.formula.chars().collect();
    let (mut out, mut i) = (String::new(), 0);
    while i < chars.len() {
        let c = chars[i];
        let prev_is_name = i > 0 && (is_name_char(chars[i - 1]) || chars[i - 1] == '\'');
        if c.is_ascii_alphabetic() && !prev_is_name {
            let (name, j) = read_name(&chars, i, false);
            let rep = if let Some(fi) = family_of(&name, &sig.params) {
                let suffix = &name[sig.params[fi].len()..];
                let a = &args[fi];
                if a == "0" || a == "1" { a.clone() }
                else if let Some(base) = a.strip_suffix('\'') { format!("{base}{suffix}'") }
                else { format!("{a}{suffix}") }
            } else if internals.contains(name.as_str()) { format!("{name}__{k}") } else { name.clone() };
            out.push_str(&rep);
            i = j;
        } else { out.push(c); i += 1; }
    }
    out
}

/// Scan `text` for box calls; `on_call(name, args, sig)` returns the text that
/// replaces a recognised call.  Everything else is copied through.
fn walk_calls(
    text: &str,
    lookup: &dyn Fn(&str) -> Option<BoxSig>,
    on_call: &mut dyn FnMut(&str, &[String], BoxSig) -> Result<String, String>,
) -> Result<String, String> {
    let chars: Vec<char> = text.chars().collect();
    let (mut out, mut i) = (String::new(), 0);
    while i < chars.len() {
        let c = chars[i];
        let prev_is_name = i > 0 && (is_name_char(chars[i - 1]) || chars[i - 1] == '\'');
        if c.is_ascii_alphabetic() && !prev_is_name {
            let (name, j) = read_name(&chars, i, false);
            if j < chars.len() && chars[j] == '(' && let Some((args, after, semi)) = parse_args(&chars, j) {
                    let sig = lookup(&name);
                    if sig.is_some() || args.len() != 1 || semi {
                        let sig = sig.ok_or_else(|| format!(
                            "unknown box `{name}` — load and compile its library (jq panel), or check the spelling"))?;
                        if args.len() != sig.params.len() {
                            let hint = if args.iter().any(|a| a.contains(',')) {
                                " — a comma directly followed by a digit continues a subscript (`b_0,0` is one two-index name); write `b_0, 0` or separate arguments with `;`"
                            } else { "" };
                            return Err(format!("box `{name}` expects {} argument{} ({}), got {}{hint}",
                                sig.params.len(), if sig.params.len() == 1 { "" } else { "s" },
                                sig.params.join("; "), args.len()));
                        }
                        out.push_str(&on_call(&name, &args, sig)?);
                        i = after;
                        continue;
                    }
            }
            out.push_str(&name);
            i = j;
        } else { out.push(c); i += 1; }
    }
    Ok(out)
}

fn expand_rec(text: &str, lookup: &dyn Fn(&str) -> Option<BoxSig>, counter: &mut usize, depth: usize) -> Result<String, String> {
    if depth > 16 {
        return Err("box expansion nested more than 16 levels — is a box defined in terms of itself?".into());
    }
    walk_calls(text, lookup, &mut |_name, args, sig| {
        *counter += 1;
        let body = substitute(&sig, args, *counter);
        let expanded = expand_rec(&body, lookup, counter, depth + 1)?;
        Ok(format!("({expanded})"))
    })
}

/// Expand every box call in `formula`.  `lookup` resolves a box name.
pub fn expand_box_calls(formula: &str, lookup: &dyn Fn(&str) -> Option<BoxSig>) -> Result<String, String> {
    let mut counter = 0;
    expand_rec(formula, lookup, &mut counter, 0)
}

/// Replace every box call in `formula` by a fresh atom `BOXCALL_k` (a plain
/// variable of the formula language) and record the calls.  A following `'`
/// attaches to the atom, so the call's polarity in the NNF is the atom's.
pub fn atomize_box_calls(formula: &str, lookup: &dyn Fn(&str) -> Option<BoxSig>) -> Result<Atomized, String> {
    if formula.contains(ATOM_PREFIX) {
        return Err(format!("variable names starting with `{ATOM_PREFIX}` are reserved for box calls"));
    }
    let mut calls: Vec<BoxCall> = Vec::new();
    let text = walk_calls(formula, lookup, &mut |name, args, _sig| {
        let k = calls.len() + 1;
        let atom = format!("{ATOM_PREFIX}{k}");
        let args: Vec<Arg> = args.iter().map(|a| Arg::parse(a)).collect();
        let label = format!("{name}({})", args.iter().map(Arg::text).collect::<Vec<_>>().join(";"));
        calls.push(BoxCall { atom: atom.clone(), name: name.to_string(), args, label });
        Ok(atom)
    })?;
    Ok(Atomized { text, calls })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::matrix::Matrix;

    fn lib(name: &str) -> Option<BoxSig> {
        match name {
            "fa" => Some(BoxSig {
                params: ["x", "y", "c_in", "s", "c_out"].map(String::from).to_vec(), internals: vec![],
                formula: "(x y + (x ⊕ y) c_in = c_out) (x ⊕ y ⊕ c_in = s)".into() }),
            "defd" => Some(BoxSig {
                params: ["x", "y", "z"].map(String::from).to_vec(), internals: vec!["u".into()],
                formula: "(u = x y) (z = u + x')".into() }),
            "two" => Some(BoxSig {   // hierarchical: defined in terms of fa
                params: ["a", "b", "s"].map(String::from).to_vec(), internals: vec!["c".into()],
                formula: "fa(a, b, 0, s, c)".into() }),
            "loop" => Some(BoxSig { params: vec!["x".into()], internals: vec![], formula: "loop(x)".into() }),
            "eq2" => Some(BoxSig {   // a bit-vector box: parameters are prefixes
                params: ["a", "b"].map(String::from).to_vec(), internals: vec![],
                formula: "(a_0 = b_0) (a_1 = b_1)".into() }),
            "half2" => Some(BoxSig {   // hidden carry family c_*
                params: ["a", "b", "s"].map(String::from).to_vec(), internals: vec!["c_1".into()],
                formula: "(c_1 = a_0 b_0) (s_0 = a_0 ⊕ b_0) (s_1 = c_1 ⊕ a_1 ⊕ b_1)".into() }),
            _ => None,
        }
    }

    #[test]
    fn expands_and_parses() {
        let e = expand_box_calls("fa(a_0, b_0, c_0, s_0, c_1) (s_0 = c_1)", &lib).unwrap();
        assert_eq!(e, "((a_0 b_0 + (a_0 ⊕ b_0) c_0 = c_1) (a_0 ⊕ b_0 ⊕ c_0 = s_0)) (s_0 = c_1)");
        assert!(Matrix::try_from(e.as_str()).is_ok());
        assert_eq!(expand_box_calls("fa(a;b;0;s;c)", &lib).unwrap(), "((a b + (a ⊕ b) 0 = c) (a ⊕ b ⊕ 0 = s))");
    }

    #[test]
    fn primes_compose_and_internals_are_fresh() {
        assert_eq!(expand_box_calls("defd(p', q, r)", &lib).unwrap(), "((u__1 = p' q) (r = u__1 + p''))");
        let e = expand_box_calls("defd(a, b, c) defd(d, e, f)", &lib).unwrap();
        assert!(e.contains("u__1") && e.contains("u__2"), "{e}");
    }

    #[test]
    fn errors() {
        assert!(expand_box_calls("full_adder(x,y,c_in,s,c_out)", &lib).unwrap_err().contains("unknown box `full_adder`"));
        assert!(expand_box_calls("fa(x, y)", &lib).unwrap_err().contains("expects 5 arguments"));
        assert!(expand_box_calls("nope()", &lib).unwrap_err().contains("unknown box"));
        assert!(expand_box_calls("loop(x)", &lib).unwrap_err().contains("16 levels"));
    }

    #[test]
    fn juxtaposition_is_preserved() {
        for f in ["A(B+C)", "A(B)", "A (B, C)", "x'(y)", "A(B C)"] {
            assert_eq!(expand_box_calls(f, &lib).unwrap(), f);
        }
    }

    #[test]
    fn subscript_commas_and_nesting() {
        assert_eq!(expand_box_calls("fa(d_0,1, e_0,2, c, s, t)", &lib).unwrap(),
                   "((d_0,1 e_0,2 + (d_0,1 ⊕ e_0,2) c = t) (d_0,1 ⊕ e_0,2 ⊕ c = s))");
        assert_eq!(expand_box_calls("two(a, b, s)", &lib).unwrap(),
                   "(((a b + (a ⊕ b) 0 = c__1) (a ⊕ b ⊕ 0 = s)))");
    }

    #[test]
    fn families_bind_by_prefix() {
        assert_eq!(expand_box_calls("eq2(x, y)", &lib).unwrap(), "((x_0 = y_0) (x_1 = y_1))");
        assert_eq!(expand_box_calls("eq2(x', 0)", &lib).unwrap(), "((x_0' = 0) (x_1' = 0))");
        assert_eq!(expand_box_calls("half2(p, q, r)", &lib).unwrap(),
                   "((c_1__1 = p_0 q_0) (r_0 = p_0 ⊕ q_0) (r_1 = c_1__1 ⊕ p_1 ⊕ q_1))");
        let fams = ["c", "c_in", "s"].map(String::from).to_vec();
        assert_eq!(family_of("c_in", &fams), Some(1));      // longest match wins
        assert_eq!(family_of("c_in_2", &fams), Some(1));
        assert_eq!(family_of("c_3", &fams), Some(0));
        assert_eq!(family_of("cs", &fams), None);
    }

    #[test]
    fn atomizes_calls() {
        let at = atomize_box_calls("fa(a, b', 0, s, c)' (s = c) fa(p,q,r,t,u)", &lib).unwrap();
        assert_eq!(at.text, "BOXCALL_1' (s = c) BOXCALL_2");
        assert_eq!(at.calls.len(), 2);
        assert_eq!(at.calls[0].label, "fa(a;b';0;s;c)");
        assert_eq!(at.calls[0].args[1], Arg::Var { name: "b".into(), neg: true });
        assert_eq!(at.calls[0].args[2], Arg::Const(false));
        let m = Matrix::try_from(at.text.as_str()).unwrap();
        assert!(m.ast.vars.iter().any(|v| v == "BOXCALL_1"));
        assert!(atomize_box_calls("fa(x, y)", &lib).is_err());
        assert!(expand_box_calls("fa(a_0,b_0,0,s_0,c_1)", &lib).unwrap_err().contains("continues a subscript"));
        assert!(expand_box_calls("fa(a_0, b_0, 0, s_0, c_1)", &lib).is_ok());
        assert!(expand_box_calls("fa(a_0;b_0;0;s_0;c_1)", &lib).is_ok());
        assert!(atomize_box_calls("BOXCALL_1 x", &lib).unwrap_err().contains("reserved"));
        assert_eq!(atomize_box_calls("A(B+C)", &lib).unwrap().text, "A(B+C)");
    }
}
