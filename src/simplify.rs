use std::collections::{BTreeSet, HashMap, HashSet};
use crate::formula::{evaluate, extract_vars, parse};

// term values: 0=false, 1=true, 2=don't-care
#[derive(Clone)]
pub struct Implicant {
    pub term: Vec<u8>,
    pub covered: BTreeSet<usize>,
}

pub fn combine(a: &[u8], b: &[u8]) -> Option<Vec<u8>> {
    let mut diffs = 0;
    let mut diff_pos = 0;
    for i in 0..a.len() {
        if a[i] != b[i] {
            if a[i] == 2 || b[i] == 2 { return None; }
            diffs += 1;
            if diffs > 1 { return None; }
            diff_pos = i;
        }
    }
    if diffs == 1 {
        let mut result = a.to_vec();
        result[diff_pos] = 2;
        Some(result)
    } else {
        None
    }
}

pub fn qmc(minterms: &[usize], n: usize) -> Vec<Implicant> {
    let mut current: Vec<Implicant> = {
        let mut seen = HashSet::new();
        minterms.iter().filter_map(|&m| {
            let term: Vec<u8> = (0..n).map(|j| ((m >> (n - 1 - j)) & 1) as u8).collect();
            if seen.insert(term.clone()) {
                Some(Implicant { term, covered: BTreeSet::from([m]) })
            } else {
                None
            }
        }).collect()
    };

    let mut primes = Vec::new();

    while !current.is_empty() {
        let mut used = HashSet::new();
        let mut next_map: HashMap<Vec<u8>, Implicant> = HashMap::new();

        for i in 0..current.len() {
            for j in (i + 1)..current.len() {
                if let Some(c) = combine(&current[i].term, &current[j].term) {
                    used.insert(i);
                    used.insert(j);
                    let entry = next_map.entry(c.clone()).or_insert(Implicant {
                        term: c,
                        covered: BTreeSet::new(),
                    });
                    entry.covered.extend(&current[i].covered);
                    entry.covered.extend(&current[j].covered);
                }
            }
        }

        for (i, imp) in current.iter().enumerate() {
            if !used.contains(&i) {
                primes.push(imp.clone());
            }
        }
        current = next_map.into_values().collect();
    }

    primes
}

pub fn simplify(formula: &str) -> Result<String, String> {
    let ast = parse(formula)?;
    let vars: Vec<String> = extract_vars(&ast).into_iter().collect();
    let n = vars.len();

    if n == 0 { return Ok(evaluate(&ast, &HashMap::new()).to_string()); }
    if n > 10 { return Err("Too many variables to simplify (max 10)".to_string()); }

    let mut minterms = Vec::new();
    for i in 0..(1usize << n) {
        let mut asgn = HashMap::new();
        for (j, v) in vars.iter().enumerate() {
            asgn.insert(v.clone(), ((i >> (n - 1 - j)) & 1) as u8);
        }
        if evaluate(&ast, &asgn) == 1 {
            minterms.push(i);
        }
    }

    if minterms.is_empty() { return Ok("0".to_string()); }
    if minterms.len() == 1 << n { return Ok("1".to_string()); }

    let primes = qmc(&minterms, n);
    let cover = minimal_cover(&primes, &minterms);

    let result = cover.iter().map(|imp| {
        let lits: Vec<String> = vars.iter().enumerate().filter_map(|(i, v)| {
            match imp.term[i] {
                1 => Some(v.clone()),
                0 => Some(format!("{}'", v)),
                _ => None,
            }
        }).collect();
        if lits.is_empty() { "1".to_string() } else { lits.join("·") }
    }).collect::<Vec<_>>().join(" + ");

    Ok(result)
}

pub fn minimal_cover(primes: &[Implicant], minterms: &[usize]) -> Vec<Implicant> {
    let mut result: Vec<Implicant> = Vec::new();
    let mut covered: BTreeSet<usize> = BTreeSet::new();

    // Essential prime implicants
    for &m in minterms {
        let covering: Vec<_> = primes.iter().filter(|p| p.covered.contains(&m)).collect();
        if covering.len() == 1 && !result.iter().any(|r| r.term == covering[0].term) {
            covered.extend(&covering[0].covered);
            result.push(covering[0].clone());
        }
    }

    // Greedy cover of remaining minterms
    let mut uncovered: BTreeSet<usize> = minterms.iter()
        .filter(|m| !covered.contains(m))
        .cloned()
        .collect();

    while !uncovered.is_empty() {
        let best = primes.iter()
            .filter(|p| !result.iter().any(|r| r.term == p.term))
            .max_by_key(|p| p.covered.iter().filter(|m| uncovered.contains(m)).count());

        match best {
            Some(b) => {
                let b = b.clone();
                b.covered.iter().for_each(|m| { uncovered.remove(m); });
                result.push(b);
            }
            None => break,
        }
    }

    result
}
