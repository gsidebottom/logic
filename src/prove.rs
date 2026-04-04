use std::collections::BTreeSet;
use crate::matrix::{self, format_path, parse_to_matrix};

pub fn get_paths(formula: &str) -> Result<(Vec<String>, Vec<bool>), String> {
    let (m, vars) = parse_to_matrix(formula)?;
    let all_paths = matrix::paths(&m);
    let formatted  = all_paths.iter().map(|p| format_path(p, &vars)).collect();
    let comp_flags = all_paths.iter().map(matrix::is_complementary).collect();
    Ok((formatted, comp_flags))
}

/// Greedy set cover: find a small set of variables whose complementary pairs
/// collectively appear in every path. Returns variable indices in cover order.
fn greedy_cover(paths: &[matrix::Path], n_vars: usize) -> Vec<usize> {
    let covers: Vec<Vec<usize>> = (0..n_vars as u32).map(|var| {
        let pos = matrix::Lit { var, neg: false };
        let neg = matrix::Lit { var, neg: true  };
        paths.iter().enumerate()
            .filter(|(_, p)| p.contains(&pos) && p.contains(&neg))
            .map(|(i, _)| i)
            .collect()
    }).collect();

    let mut uncovered: BTreeSet<usize> = (0..paths.len()).collect();
    let mut used      = vec![false; n_vars];
    let mut result    = Vec::new();

    while !uncovered.is_empty() {
        let best = (0..n_vars)
            .filter(|&v| !used[v])
            .max_by_key(|&v| covers[v].iter().filter(|i| uncovered.contains(i)).count());
        match best {
            Some(v) => {
                covers[v].iter().for_each(|i| { uncovered.remove(i); });
                used[v] = true;
                result.push(v);
            }
            None => break,
        }
    }
    result
}

/// Returns `(true, None, pairs)` if valid (with a greedy cover of complementary
/// pairs), or `(false, Some(path), [])` with the first uncomplimentary path.
pub fn check_valid(formula: &str) -> Result<(bool, Option<String>, Vec<String>), String> {
    let (m, vars) = parse_to_matrix(formula)?;
    let all_paths = matrix::paths(&m);
    match all_paths.iter().find(|p| !matrix::is_complementary(p)) {
        Some(path) => Ok((false, Some(format_path(path, &vars)), vec![])),
        None => {
            let cover = greedy_cover(&all_paths, vars.len());
            let pairs = cover.iter()
                .map(|&v| format!("{{{}, {}'}}", vars[v], vars[v]))
                .collect();
            Ok((true, None, pairs))
        }
    }
}

/// Returns `(true, Some(path), [])` with first uncomplimentary path in the
/// complement if satisfiable, or `(false, None, pairs)` with a greedy cover of
/// complementary pairs in the complement if unsatisfiable.
pub fn check_satisfiable(formula: &str) -> Result<(bool, Option<String>, Vec<String>), String> {
    let (m, vars) = parse_to_matrix(formula)?;
    let comp_paths = matrix::paths(&m.complement());
    match comp_paths.iter().find(|p| !matrix::is_complementary(p)) {
        Some(path) => Ok((true, Some(format_path(path, &vars)), vec![])),
        None => {
            let cover = greedy_cover(&comp_paths, vars.len());
            let pairs = cover.iter()
                .map(|&v| format!("{{{}, {}'}}", vars[v], vars[v]))
                .collect();
            Ok((false, None, pairs))
        }
    }
}
