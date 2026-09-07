//! Box calls in the formula language (`doc/box_backend_design.md` §5.2):
//! `name(a1, a2, …)` (or `name(a1; a2; …)`) refers to a compiled box.  Expansion
//! substitutes the arguments for the box's parameters in its definition,
//! renames the box's projected internals freshly per call site (they are local
//! — the ∃ of §2.4), and recurses, so every formula-level backend and the
//! diagram see an ordinary formula.  An unknown box or a wrong argument count
//! is an error.
//!
//! Call vs. juxtaposition: `name(` starts a call when the parenthesised text is
//! an argument list and either `name` is a known box, or there are two or more
//! arguments (or none, or `;` separators).  `A(B+C)` and `A(B)` keep their old
//! meaning (AND by juxtaposition).  Inside an argument list a comma continues a
//! name only within a numeric subscript (`d_0,1`); elsewhere it separates
//! arguments, so `x,y` is two arguments even though `x,y` is one variable
//! name in the rest of the language.

use std::collections::HashMap;

/// What expansion needs to know about a compiled box.
#[derive(Clone, Debug)]
pub struct BoxSig {
    /// The call's arguments bind to these, in order (interface + exposed internals).
    pub params: Vec<String>,
    /// Projected internals of the definition: renamed `<name>__<k>` per call site.
    pub internals: Vec<String>,
    /// The definition, over `params` and `internals`.
    pub formula: String,
}

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

/// Substitute a call's arguments for the parameters in the definition, and
/// give the internals call-site-unique names.
fn substitute(sig: &BoxSig, args: &[String], k: usize) -> String {
    let mut map: HashMap<&str, String> = sig.params.iter().zip(args).map(|(p, a)| (p.as_str(), a.clone())).collect();
    for v in &sig.internals { map.entry(v.as_str()).or_insert_with(|| format!("{v}__{k}")); }
    let chars: Vec<char> = sig.formula.chars().collect();
    let (mut out, mut i) = (String::new(), 0);
    while i < chars.len() {
        let c = chars[i];
        let prev_is_name = i > 0 && (is_name_char(chars[i - 1]) || chars[i - 1] == '\'');
        if c.is_ascii_alphabetic() && !prev_is_name {
            let (name, j) = read_name(&chars, i, false);
            out.push_str(map.get(name.as_str()).map(String::as_str).unwrap_or(&name));
            i = j;
        } else { out.push(c); i += 1; }
    }
    out
}

fn expand_rec(text: &str, lookup: &dyn Fn(&str) -> Option<BoxSig>, counter: &mut usize, depth: usize) -> Result<String, String> {
    if depth > 16 {
        return Err("box expansion nested more than 16 levels — is a box defined in terms of itself?".into());
    }
    let chars: Vec<char> = text.chars().collect();
    let (mut out, mut i) = (String::new(), 0);
    while i < chars.len() {
        let c = chars[i];
        let prev_is_name = i > 0 && (is_name_char(chars[i - 1]) || chars[i - 1] == '\'');
        if c.is_ascii_alphabetic() && !prev_is_name {
            let (name, j) = read_name(&chars, i, false);
            if j < chars.len() && chars[j] == '(' {
                if let Some((args, after, semi)) = parse_args(&chars, j) {
                    let sig = lookup(&name);
                    if sig.is_some() || args.len() != 1 || semi {
                        let sig = sig.ok_or_else(|| format!(
                            "unknown box `{name}` — load and compile its library (jq panel), or check the spelling"))?;
                        if args.len() != sig.params.len() {
                            return Err(format!("box `{name}` expects {} argument{} ({}), got {}",
                                sig.params.len(), if sig.params.len() == 1 { "" } else { "s" },
                                sig.params.join("; "), args.len()));
                        }
                        *counter += 1;
                        let body = substitute(&sig, &args, *counter);
                        let expanded = expand_rec(&body, lookup, counter, depth + 1)?;
                        out.push('('); out.push_str(&expanded); out.push(')');
                        i = after;
                        continue;
                    }
                }
            }
            out.push_str(&name);
            i = j;
        } else { out.push(c); i += 1; }
    }
    Ok(out)
}

/// Expand every box call in `formula`.  `lookup` resolves a box name.
pub fn expand_box_calls(formula: &str, lookup: &dyn Fn(&str) -> Option<BoxSig>) -> Result<String, String> {
    let mut counter = 0;
    expand_rec(formula, lookup, &mut counter, 0)
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
}
