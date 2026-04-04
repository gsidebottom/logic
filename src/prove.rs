use std::collections::BTreeSet;
use crate::matrix::{self, format_path, parse_to_matrix};

pub fn get_paths(formula: &str) -> Result<(Vec<String>, Vec<bool>), String> {
    let (m, vars) = parse_to_matrix(formula)?;
    let all_paths = matrix::paths(&m);
    let formatted  = all_paths.iter().map(|p| format_path(p, &m, &vars)).collect();
    let comp_flags = all_paths.iter().map(|p| matrix::is_complementary(p, &m)).collect();
    Ok((formatted, comp_flags))
}

/// Greedy set cover over complementary literal pairs.
///
/// Enumerates every `(posA, posB)` pair where the literals at those positions
/// are complements of each other. A pair *covers* a path when the path contains
/// both positions. Returns a minimal covering set of such pairs.
fn greedy_cover(
    m: &matrix::Matrix,
    paths: &[matrix::Path],
    n_vars: usize,
) -> Vec<(matrix::Position, matrix::Position)> {
    // Enumerate every complementary pair present in the matrix.
    let mut all_pairs: Vec<(matrix::Position, matrix::Position)> = Vec::new();
    for var in 0..n_vars as u32 {
        let pos_lits = matrix::literal_positions(m, &matrix::Lit { var, neg: false });
        let neg_lits = matrix::literal_positions(m, &matrix::Lit { var, neg: true  });
        for p in &pos_lits {
            for n in &neg_lits {
                all_pairs.push((p.clone(), n.clone()));
            }
        }
    }

    // For each pair, which paths contain both positions?
    let covers: Vec<Vec<usize>> = all_pairs.iter().map(|(pa, pb)| {
        paths.iter().enumerate()
            .filter(|(_, path)| path.contains(pa) && path.contains(pb))
            .map(|(i, _)| i)
            .collect()
    }).collect();

    let mut uncovered: BTreeSet<usize> = (0..paths.len()).collect();
    let mut used      = vec![false; all_pairs.len()];
    let mut result    = Vec::new();

    while !uncovered.is_empty() {
        let best = (0..all_pairs.len())
            .filter(|&i| !used[i])
            .max_by_key(|&i| covers[i].iter().filter(|&&j| uncovered.contains(&j)).count());
        match best {
            Some(i) => {
                covers[i].iter().for_each(|&j| { uncovered.remove(&j); });
                used[i] = true;
                result.push(all_pairs[i].clone());
            }
            None => break,
        }
    }
    result
}

/// Returns `(true, None, pairs)` if valid (with a greedy cover of complementary
/// pairs), or `(false, Some(path), [])` with the first uncomplimentary path.
pub fn check_valid(
    formula: &str,
) -> Result<(bool, Option<String>, Vec<(matrix::Position, matrix::Position)>), String> {
    let (m, vars) = parse_to_matrix(formula)?;
    let all_paths = matrix::paths(&m);
    match all_paths.iter().find(|p| !matrix::is_complementary(p, &m)) {
        Some(path) => Ok((false, Some(format_path(path, &m, &vars)), vec![])),
        None => {
            let pairs = greedy_cover(&m, &all_paths, vars.len());
            Ok((true, None, pairs))
        }
    }
}

/// Returns `(true, Some(path), [])` with first uncomplimentary path in the
/// complement if satisfiable, or `(false, None, pairs)` with a greedy cover of
/// complementary pairs in the complement if unsatisfiable.
pub fn check_satisfiable(
    formula: &str,
) -> Result<(bool, Option<String>, Vec<(matrix::Position, matrix::Position)>), String> {
    let (m, vars) = parse_to_matrix(formula)?;
    let comp = m.complement();
    let comp_paths = matrix::paths(&comp);
    match comp_paths.iter().find(|p| !matrix::is_complementary(p, &comp)) {
        Some(path) => Ok((true, Some(format_path(path, &comp, &vars)), vec![])),
        None => {
            let pairs = greedy_cover(&comp, &comp_paths, vars.len());
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
        assert!(paths.contains(&"{L', R, R', R'}".to_string()));
        assert!(paths.contains(&"{H', L, L', R}".to_string()));
        assert!(paths.contains(&"{H, H', L', R}".to_string()));
        assert!(paths.contains(&"{H', L', R, R'}".to_string()));
    }

    #[test]
    fn test_check_valid() {
        let (valid, path, pairs) = check_valid(F).unwrap();
        assert!(valid);
        assert!(path.is_none());
        // Matrix: Sum([Prod([R'@[0,0], H'@[0,1]]), Prod([L@[1,0], H@[1,1], R'@[1,2]]), L'@[2], R@[3]])
        // R' appears at [0,0] and [1,2], yielding two R/R' pairs.
        // Greedy: (R@[3], R'@[0,0]) covers paths {0,1,2}; then (R@[3], R'@[1,2]) covers {5};
        // then (L@[1,0], L'@[2]) covers {3}; then (H@[1,1], H'@[0,1]) covers {4}.
        assert_eq!(pairs, vec![
            (vec![3],    vec![0, 0]),
            (vec![3],    vec![1, 2]),
            (vec![1, 0], vec![2]),
            (vec![1, 1], vec![0, 1]),
        ]);
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
