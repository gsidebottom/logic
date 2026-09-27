//! A CNF as two flat arrays.
//!
//! `Vec<Vec<i32>>` is a heap allocation per clause: 24 bytes for the `Vec`
//! in the outer buffer plus the allocator's block for the literals, which
//! for a ternary clause is a 16-byte quantum holding 12 bytes — about
//! **40 bytes of container for 9 bytes of payload** at the 2.3-literal
//! average of a competition instance.  And the outer `Vec` doubles as it
//! grows, so at 316 M clauses its final reallocation needs the old 7.6 GB
//! buffer and a new 15 GB one live at once.  That transient is how one
//! parse reached past 64 GB on 2026-09-20 (`doc/data/boxes_memory_2026-09-20.txt`).
//!
//! Here a clause is a range of one literal array: **4 bytes per literal and
//! 4 per clause**, no allocation per clause, and both arrays can be
//! `reserve`d from the `p cnf` header so nothing doubles.  On that instance
//! it is 4.1 GB in place of 12.6 GB steady state, and no spike.
//!
//! Offsets are `u32`, so a formula is limited to 2³² − 1 literals; that is
//! 17 GB of literals alone, past what any run here can search, and the
//! parser refuses cleanly before it (`push` panics as a last line, with the
//! reason).  Literals are DIMACS integers, as in the file.

/// A CNF formula: clause `i` is `lits[start(i)..ends[i]]`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Cnf {
    lits: Vec<i32>,
    /// One past the last literal of each clause; clause `i` begins where
    /// clause `i − 1` ended, or at 0.
    ends: Vec<u32>,
}

impl Cnf {
    pub fn new() -> Cnf {
        Cnf::default()
    }

    /// Room for `clauses` clauses holding `lits` literals in total — from a
    /// `p cnf` line, so that the arrays never reallocate while parsing.
    pub fn with_capacity(clauses: usize, lits: usize) -> Cnf {
        Cnf { lits: Vec::with_capacity(lits), ends: Vec::with_capacity(clauses) }
    }

    pub fn reserve(&mut self, clauses: usize, lits: usize) {
        self.ends.reserve(clauses);
        self.lits.reserve(lits);
    }

    /// Number of clauses.
    pub fn len(&self) -> usize {
        self.ends.len()
    }

    pub fn is_empty(&self) -> bool {
        self.ends.is_empty()
    }

    /// Total literals over all clauses.
    pub fn num_lits(&self) -> usize {
        self.lits.len()
    }

    /// Append a clause.  Panics past 2³² − 1 literals; the DIMACS parser
    /// returns an error well before that.
    pub fn push(&mut self, clause: &[i32]) {
        let end = self.lits.len() + clause.len();
        assert!(end <= u32::MAX as usize, "a CNF of more than 4 294 967 295 literals is not supported");
        self.lits.extend_from_slice(clause);
        self.ends.push(end as u32);
    }

    #[inline]
    fn start(&self, i: usize) -> usize {
        if i == 0 { 0 } else { self.ends[i - 1] as usize }
    }

    /// Clause `i` as a slice of DIMACS literals.
    #[inline]
    pub fn get(&self, i: usize) -> &[i32] {
        &self.lits[self.start(i)..self.ends[i] as usize]
    }

    /// The clauses in order.
    pub fn iter(&self) -> impl Iterator<Item = &[i32]> + '_ {
        let mut start = 0usize;
        self.ends.iter().map(move |&e| {
            let c = &self.lits[start..e as usize];
            start = e as usize;
            c
        })
    }

    /// The literals of every clause, flat, in clause order.
    pub fn lits(&self) -> &[i32] {
        &self.lits
    }

    /// Release growth slack (nothing to release after a `with_capacity`
    /// sized from an accurate header).
    pub fn shrink_to_fit(&mut self) {
        self.lits.shrink_to_fit();
        self.ends.shrink_to_fit();
    }

    /// For the stages still written against `Vec<Vec<i32>>`.  This
    /// materialises the per-clause allocations the flat form exists to
    /// avoid, so callers on the large-instance path should not use it.
    pub fn to_vecs(&self) -> Vec<Vec<i32>> {
        self.iter().map(|c| c.to_vec()).collect()
    }

    pub fn from_vecs<C: AsRef<[i32]>>(clauses: impl IntoIterator<Item = C>) -> Cnf {
        let mut cnf = Cnf::new();
        for c in clauses {
            cnf.push(c.as_ref());
        }
        cnf
    }
}

impl<'a> IntoIterator for &'a Cnf {
    type Item = &'a [i32];
    type IntoIter = Box<dyn Iterator<Item = &'a [i32]> + 'a>;
    fn into_iter(self) -> Self::IntoIter {
        Box::new(self.iter())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clauses_round_trip_through_the_flat_form() {
        let v = vec![vec![1, -2, 3], vec![], vec![-4], vec![5, 6]];
        let cnf = Cnf::from_vecs(&v);
        assert_eq!(cnf.len(), 4);
        assert_eq!(cnf.num_lits(), 6);
        assert_eq!(cnf.get(0), &[1, -2, 3]);
        assert_eq!(cnf.get(1), &[] as &[i32]);   // the empty clause survives
        assert_eq!(cnf.get(2), &[-4]);
        assert_eq!(cnf.get(3), &[5, 6]);
        assert_eq!(cnf.iter().collect::<Vec<_>>(), v.iter().map(|c| c.as_slice()).collect::<Vec<_>>());
        assert_eq!(cnf.to_vecs(), v);
        assert_eq!((&cnf).into_iter().count(), 4);
    }

    #[test]
    fn capacity_from_a_header_means_no_reallocation() {
        let mut cnf = Cnf::with_capacity(3, 7);
        let (lc, ec) = (cnf.lits.capacity(), cnf.ends.capacity());
        cnf.push(&[1, 2, 3]);
        cnf.push(&[-1, -2, -3]);
        cnf.push(&[4]);
        assert_eq!((cnf.lits.capacity(), cnf.ends.capacity()), (lc, ec));
        assert_eq!(cnf.lits(), &[1, 2, 3, -1, -2, -3, 4]);
    }

    #[test]
    fn empty_and_default_agree() {
        assert!(Cnf::new().is_empty());
        assert_eq!(Cnf::new(), Cnf::default());
        assert_eq!(Cnf::new().iter().count(), 0);
    }
}
