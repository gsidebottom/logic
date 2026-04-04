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

#[cfg(test)]
mod tests {
    use super::*;

    // Formula: R'H' + L H R' + L' + R
    // Variables alphabetically: H(0), L(1), R(2)
    // This is a tautology — every path through the matrix is complementary.
    const F: &str = "R'H' + L H R' + L' + R";

    #[test]
    fn test_get_paths_count_and_complementarity() {
        let (paths, comp) = get_paths(F).unwrap();
        assert_eq!(paths.len(), 6);
        assert!(comp.iter().all(|&c| c), "all paths should be complementary");
    }

    #[test]
    fn test_get_paths_contents() {
        let (paths, _) = get_paths(F).unwrap();
        assert!(paths.contains(&"{L, L', R, R'}".to_string()));
        assert!(paths.contains(&"{H, L', R, R'}".to_string()));
        assert!(paths.contains(&"{L', R, R'}".to_string()));
        assert!(paths.contains(&"{H', L, L', R}".to_string()));
        assert!(paths.contains(&"{H, H', L', R}".to_string()));
        assert!(paths.contains(&"{H', L', R, R'}".to_string()));
    }

    #[test]
    fn test_check_valid() {
        let (valid, path, pairs) = check_valid(F).unwrap();
        assert!(valid);
        assert!(path.is_none());
        // Greedy cover picks R first (covers 4 paths), then L, then H.
        assert!(pairs.contains(&"{R, R'}".to_string()));
        assert!(pairs.contains(&"{L, L'}".to_string()));
        assert!(pairs.contains(&"{H, H'}".to_string()));
    }

    #[test]
    fn test_check_satisfiable_tautology_is_satisfiable() {
        let (sat, path, pairs) = check_satisfiable(F).unwrap();
        // A tautology is satisfiable; complement has non-complementary paths.
        assert!(sat);
        assert_eq!(path.as_deref(), Some("{H, R}"));
        assert!(pairs.is_empty());
    }

    #[test]
    fn test_check_valid_non_tautology() {
        // Simple variable is not a tautology.
        let (valid, path, _) = check_valid("A").unwrap();
        assert!(!valid);
        assert_eq!(path.as_deref(), Some("{A}"));
    }

    #[test]
    fn test_check_satisfiable_contradiction() {
        // A · A' is unsatisfiable.
        let (sat, path, _) = check_satisfiable("A · A'").unwrap();
        assert!(!sat);
        assert!(path.is_none());
    }
}
