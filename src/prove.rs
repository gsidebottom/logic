use crate::controller::PathSearchController;
use crate::matrix::{format_path, parse_to_nnf, BacktrackWhenCoveredController, Cover, PathParams, PathPrefix};

type CoveredPrefixes = Vec<PathPrefix>;
type UncoveredPositions = Option<PathPrefix>;
type ProveResult = Result<(bool, Option<String>, UncoveredPositions, Cover, CoveredPrefixes), String>;

pub fn get_paths(formula: &str) -> Result<(Vec<String>, Vec<bool>), String> {
    let (m, vars) = parse_to_nnf(formula)?;
    let all_paths: Vec<_> = m.paths_iter().collect();
    let formatted  = all_paths.iter().map(|p| format_path(p, &m, &vars)).collect();
    let comp_flags = all_paths.iter().map(|p| m.is_complementary(p)).collect();
    Ok((formatted, comp_flags))
}

/// Returns `(valid, uncovered_path, uncovered_positions, cover, prefixes)`.
pub fn check_valid(formula: &str) -> ProveResult {
    let (m, vars) = parse_to_nnf(formula)?;
    let mut classes = Vec::new();
    let hit_limit = {
        let mut ctrl = BacktrackWhenCoveredController::with_on_class(
            Some(PathParams { paths_class_limit: usize::MAX, uncovered_path_limit: usize::MAX, covered_prefix_limit: usize::MAX, no_cover: false }),
            |class, _hit_limit| { classes.push(class); true },
        );
        m.paths(&mut ctrl);
        ctrl.hit_limit()
    };
    let result = crate::matrix::Paths { classes, hit_limit };
    let cover = result.cover();
    let prefixes: Vec<PathPrefix> = result.covered_path_prefixes().map(|cp| cp.prefix.clone()).collect();
    let first_uncovered = result.uncovered_paths().next();
    let path = first_uncovered.map(|p| format_path(p, &m, &vars));
    let positions = first_uncovered.map(|p| m.positions_on_path(p));
    Ok((first_uncovered.is_none(), path, positions, cover, prefixes))
}

/// Returns `(satisfiable, uncovered_path_in_complement, uncovered_positions, cover, prefixes)`.
pub fn check_satisfiable(formula: &str) -> ProveResult {
    let (m, vars) = parse_to_nnf(formula)?;
    let comp = m.complement();
    let mut classes = Vec::new();
    let hit_limit = {
        let mut ctrl = BacktrackWhenCoveredController::with_on_class(
            Some(PathParams { paths_class_limit: usize::MAX, uncovered_path_limit: usize::MAX, covered_prefix_limit: usize::MAX, no_cover: false }),
            |class, _hit_limit| { classes.push(class); true },
        );
        comp.paths(&mut ctrl);
        ctrl.hit_limit()
    };
    let result = crate::matrix::Paths { classes, hit_limit };
    let cover = result.cover();
    let prefixes: Vec<PathPrefix> = result.covered_path_prefixes().map(|cp| cp.prefix.clone()).collect();
    let first_uncovered = result.uncovered_paths().next();
    let path = first_uncovered.map(|p| format_path(p, &comp, &vars));
    let positions = first_uncovered.map(|p| comp.positions_on_path(p));
    Ok((first_uncovered.is_some(), path, positions, cover, prefixes))
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
        assert!(paths.contains(&"{R', L, L', R}".to_string()));
        assert!(paths.contains(&"{R', H, L', R}".to_string()));
        assert!(paths.contains(&"{R', R', L', R}".to_string()));
        assert!(paths.contains(&"{H', L, L', R}".to_string()));
        assert!(paths.contains(&"{H', H, L', R}".to_string()));
        assert!(paths.contains(&"{H', R', L', R}".to_string()));
    }

    #[test]
    fn test_check_valid() {
        let (valid, path, _positions, pairs, prefixes) = check_valid(F).unwrap();
        assert!(valid);
        assert!(path.is_none());
        // Every pair in the cover must consist of complementary literals.
        let (m, _) = parse_to_nnf(F).unwrap();
        for (pa, pb) in &pairs {
            let la = m.lit_at(pa).expect("position a should resolve");
            let lb = m.lit_at(pb).expect("position b should resolve");
            assert!(la.is_complement_of(lb), "{:?} and {:?} should be complementary", pa, pb);
        }
        // Every path must be covered by at least one pair.
        let all_paths: Vec<crate::matrix::ProdPath> = m.paths_iter().collect();
        for path in &all_paths {
            let positions = m.positions_on_path(path);
            assert!(pairs.iter().any(|(pa, pb)|
                positions.contains(pa) && positions.contains(pb)),
                "cover misses path {:?}", path);
        }
        // Each cover pair has a corresponding prefix.
        assert_eq!(pairs.len(), prefixes.len());
    }

    #[test]
    fn test_check_satisfiable_tautology_is_satisfiable() {
        let (sat, path, _, _pairs, _prefixes) = check_satisfiable(F).unwrap();
        // A tautology is satisfiable; complement has non-complementary paths.
        assert!(sat);
        assert_eq!(path.as_deref(), Some("{R, H}"));
    }

    #[test]
    fn test_check_valid_non_tautology() {
        // Simple variable is not a tautology.
        let (valid, path, _, _, _) = check_valid("A").unwrap();
        assert!(!valid);
        assert_eq!(path.as_deref(), Some("{A}"));
    }

    #[test]
    fn test_check_satisfiable_contradiction() {
        // A · A' is unsatisfiable.
        let (sat, path, _, _, _) = check_satisfiable("A · A'").unwrap();
        assert!(!sat);
        assert!(path.is_none());
    }
}
