use crate::matrix::{format_path, parse_to_matrix, Cover, Proof};

type ProveResult = Result<(bool, Option<String>, Cover), String>;

pub fn get_paths(formula: &str) -> Result<(Vec<String>, Vec<bool>), String> {
    let (m, vars) = parse_to_matrix(formula)?;
    let all_paths: Vec<_> = m.paths_iter().collect();
    let formatted  = all_paths.iter().map(|p| format_path(p, &m, &vars)).collect();
    let comp_flags = all_paths.iter().map(|p| m.is_complementary(p)).collect();
    Ok((formatted, comp_flags))
}

/// Returns `(true, None, pairs)` if valid (with a greedy cover of complementary
/// pairs), or `(false, Some(path), [])` with the first uncomplimentary path.
pub fn check_valid(formula: &str) -> ProveResult {
    let (m, vars) = parse_to_matrix(formula)?;
    let Proof { cover, first_uncovered_path } = m.check_valid();
    match first_uncovered_path {
        Some(path) => Ok((false, Some(format_path(&path, &m, &vars)), vec![])),
        None       => Ok((true, None, cover)),
    }
}

/// Returns `(true, Some(path), [])` with first uncomplimentary path in the
/// complement if satisfiable, or `(false, None, pairs)` with a greedy cover of
/// complementary pairs in the complement if unsatisfiable.
pub fn check_satisfiable(formula: &str) -> ProveResult {
    let (m, vars) = parse_to_matrix(formula)?;
    let comp = m.complement();
    let Proof { cover, first_uncovered_path } = comp.check_valid();
    match first_uncovered_path {
        Some(path) => Ok((true, Some(format_path(&path, &comp, &vars)), vec![])),
        None       => Ok((false, None, cover)),
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
        // Every pair in the cover must consist of complementary literals.
        let (m, _) = parse_to_matrix(F).unwrap();
        for (pa, pb) in &pairs {
            let la = m.lit_at(pa).expect("position a should resolve");
            let lb = m.lit_at(pb).expect("position b should resolve");
            assert!(la.is_complement_of(lb), "{:?} and {:?} should be complementary", pa, pb);
        }
        // Every path must be covered by at least one pair.
        let all_paths: Vec<crate::matrix::Path> = m.paths_iter().collect();
        for path in &all_paths {
            let positions = m.positions_on_path(path);
            assert!(pairs.iter().any(|(pa, pb)|
                positions.contains(pa) && positions.contains(pb)),
                "cover misses path {:?}", path);
        }
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
