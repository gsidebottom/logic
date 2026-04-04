use crate::matrix::{self, format_path, parse_to_matrix, Position};

type CoverPairs = Vec<(Position, Position)>;
type ProveResult = Result<(bool, Option<String>, CoverPairs), String>;

pub fn get_paths(formula: &str) -> Result<(Vec<String>, Vec<bool>), String> {
    let (m, vars) = parse_to_matrix(formula)?;
    let all_paths = matrix::paths(&m);
    let formatted  = all_paths.iter().map(|p| format_path(p, &m, &vars)).collect();
    let comp_flags = all_paths.iter().map(|p| matrix::is_complementary(p, &m)).collect();
    Ok((formatted, comp_flags))
}

/// Covering pairs for all paths.
///
/// Iterates through each path. If any pair already in the cover has both its
/// positions in the path, the path is already covered. Otherwise, finds the
/// first complementary literal pair within the path and adds it to the cover.
fn greedy_cover(m: &matrix::Matrix, paths: &[matrix::Path]) -> CoverPairs {
    let resolved: Vec<Vec<matrix::Position>> = paths.iter()
        .map(|p| matrix::positions_on_path(m, p))
        .collect();

    let mut result: CoverPairs = Vec::new();

    'path: for positions in &resolved {
        for (pa, pb) in &result {
            if positions.contains(pa) && positions.contains(pb) {
                continue 'path;
            }
        }
        // Path not yet covered — find the first complementary pair within it.
        'found: for pos_a in positions {
            if let Some(lit_a) = matrix::lit_at(m, pos_a) {
                for pos_b in positions {
                    if let Some(lit_b) = matrix::lit_at(m, pos_b) {
                        if lit_a.is_complement_of(lit_b) {
                            result.push((pos_a.clone(), pos_b.clone()));
                            break 'found;
                        }
                    }
                }
            }
        }
    }

    result
}

/// Returns `(true, None, pairs)` if valid (with a greedy cover of complementary
/// pairs), or `(false, Some(path), [])` with the first uncomplimentary path.
pub fn check_valid(formula: &str) -> ProveResult {
    let (m, vars) = parse_to_matrix(formula)?;
    let all_paths = matrix::paths(&m);
    match all_paths.iter().find(|p| !matrix::is_complementary(p, &m)) {
        Some(path) => Ok((false, Some(format_path(path, &m, &vars)), vec![])),
        None => {
            let pairs = greedy_cover(&m, &all_paths);
            Ok((true, None, pairs))
        }
    }
}

/// Returns `(true, Some(path), [])` with first uncomplimentary path in the
/// complement if satisfiable, or `(false, None, pairs)` with a greedy cover of
/// complementary pairs in the complement if unsatisfiable.
pub fn check_satisfiable(formula: &str) -> ProveResult {
    let (m, vars) = parse_to_matrix(formula)?;
    let comp = m.complement();
    let comp_paths = matrix::paths(&comp);
    match comp_paths.iter().find(|p| !matrix::is_complementary(p, &comp)) {
        Some(path) => Ok((true, Some(format_path(path, &comp, &vars)), vec![])),
        None => {
            let pairs = greedy_cover(&comp, &comp_paths);
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
        // Path 0 ([0,0]R',[1,0]L,[2]L',[3]R): first comp pair = (R'@[0,0], R@[3])
        // Path 1 covered by ([0,0],[3])
        // Path 2 covered by ([0,0],[3])
        // Path 3 ([0,1]H',[1,0]L,[2]L',[3]R): first comp pair = (L@[1,0], L'@[2])
        // Path 4 ([0,1]H',[1,1]H,[2]L',[3]R): first comp pair = (H'@[0,1], H@[1,1])
        // Path 5 ([0,1]H',[1,2]R',[2]L',[3]R): first comp pair = (R'@[1,2], R@[3])
        assert_eq!(pairs, vec![
            (vec![0, 0], vec![3]),
            (vec![1, 0], vec![2]),
            (vec![0, 1], vec![1, 1]),
            (vec![1, 2], vec![3]),
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
