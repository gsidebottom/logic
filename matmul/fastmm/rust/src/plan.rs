//! Plans: fused levels from the top, ending in a leaf.  Written as in the C library: G (one GEMM),
//! Gk (a level's products as k single-threaded GEMM streams), B2 (classical blocked 2x2), SW
//! (the <2x2x2:7> level: DPS's dyadic accurate point, or Strassen-Winograd with gen_kernels.py
//! --sw winograd), D48 (the rank-48 <4x4x4:48> scheme of Dumas, Pernet and
//! Sedoglavic), R336 / R363 / R633 (their accurate <3x3x6:40> scheme in its three orientations,
//! rectangular levels), and X+p (the level's sub-problems pipelined on p pass threads).
//!
//! A problem has a shape (m x k)(k x n); a level of grid g1 x g2 x g3 splits A into g1 x g2 blocks
//! of m/g1 x k/g2, B into g2 x g3 blocks of k/g2 x n/g3 and C into g1 x g3 blocks of m/g1 x n/g3,
//! and its r products have the shape (m/g1, k/g2, n/g3).

use std::fmt;

/// extra elements between scratch blocks (FMM_PAD, default 1040): blocks of power-of-two size
/// would otherwise start at one offset modulo the cache's set span
pub fn pad() -> usize {
    std::env::var("FMM_PAD").ok().and_then(|s| s.parse().ok()).unwrap_or(1040)
}

/// the smallest block size the planner considers (FMM_MINB, default 256)
pub fn minb() -> usize {
    std::env::var("FMM_MINB").ok().and_then(|s| s.parse().ok()).unwrap_or(256)
}

/// pass threads of a pipelined level written without a count (FMM_PASS_THREADS, default 2)
pub fn default_pass_threads() -> usize {
    std::env::var("FMM_PASS_THREADS").ok().and_then(|s| s.parse().ok()).unwrap_or(2)
}

/// the shape of a product: (m x k)(k x n)
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct Shape {
    pub m: usize,
    pub k: usize,
    pub n: usize,
}

impl Shape {
    pub const fn sq(n: usize) -> Shape {
        Shape { m: n, k: n, n }
    }
    pub const fn new(m: usize, k: usize, n: usize) -> Shape {
        Shape { m, k, n }
    }
    pub fn is_sq(&self) -> bool {
        self.m == self.k && self.k == self.n
    }
    pub fn min_dim(&self) -> usize {
        self.m.min(self.k).min(self.n)
    }
}

impl fmt::Display for Shape {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_sq() { write!(f, "{}", self.m) } else { write!(f, "{}x{}x{}", self.m, self.k, self.n) }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum Level {
    G,
    B2,
    Sw,
    D48,
    R336,
    R363,
    R633,
}

impl Level {
    pub const ALL: [Level; 7] = [Level::G, Level::B2, Level::Sw, Level::D48, Level::R336, Level::R363, Level::R633];
    /// the fused levels the planner uses
    pub const FUSED: [Level; 5] = [Level::Sw, Level::D48, Level::R336, Level::R363, Level::R633];

    pub fn is_leaf(self) -> bool {
        matches!(self, Level::G | Level::B2)
    }
    /// g1 x g2 x g3
    pub fn grid(self) -> (usize, usize, usize) {
        match self {
            Level::G => (1, 1, 1),
            Level::B2 | Level::Sw => (2, 2, 2),
            Level::D48 => (4, 4, 4),
            Level::R336 => (3, 3, 6),
            Level::R363 => (3, 6, 3),
            Level::R633 => (6, 3, 3),
        }
    }
    pub fn rank(self) -> usize {
        match self {
            Level::G => 1,
            Level::B2 => 8,
            Level::Sw => 7,
            Level::D48 => 48,
            Level::R336 | Level::R363 | Level::R633 => 40,
        }
    }
    pub fn name(self) -> &'static str {
        match self {
            Level::G => "G",
            Level::B2 => "B2",
            Level::Sw => "SW",
            Level::D48 => "D48",
            Level::R336 => "R336",
            Level::R363 => "R363",
            Level::R633 => "R633",
        }
    }
    pub fn from_name(s: &str) -> Option<Level> {
        Level::ALL.into_iter().find(|l| l.name() == s)
    }
    /// whether the level's grid divides the shape
    pub fn divides(self, s: Shape) -> bool {
        let (g1, g2, g3) = self.grid();
        s.m % g1 == 0 && s.k % g2 == 0 && s.n % g3 == 0
    }
    /// the shape of the level's products
    pub fn sub(self, s: Shape) -> Shape {
        let (g1, g2, g3) = self.grid();
        Shape::new(s.m / g1, s.k / g2, s.n / g3)
    }
    /// the problem whose products have shape t
    pub fn up(self, t: Shape) -> Shape {
        let (g1, g2, g3) = self.grid();
        Shape::new(t.m * g1, t.k * g2, t.n * g3)
    }
}

/// one level of a plan: a leaf with its GEMM streams (0: Accelerate's own threading), or a
/// fused level, pipelined on `pipe` pass threads (Some(0): the default count)
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct Entry {
    pub level: Level,
    pub streams: u8,
    pub pipe: Option<u8>,
}

impl Entry {
    pub const fn new(level: Level) -> Entry {
        Entry { level, streams: 0, pipe: None }
    }
    pub const fn gemm(streams: u8) -> Entry {
        Entry { level: Level::G, streams, pipe: None }
    }
    pub fn pass_threads(&self) -> usize {
        match self.pipe {
            Some(0) => default_pass_threads(),
            Some(p) => p as usize,
            None => 0,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct Plan(pub Vec<Entry>);

impl Plan {
    pub fn classical() -> Plan {
        Plan(vec![Entry::new(Level::G)])
    }

    /// scratch elements the plan needs on a problem of shape s: each fused level r blocks of each
    /// of its three block shapes, pad apart (S, T, M), the levels below reusing theirs product
    /// after product, a pipelined level twice
    pub fn work(&self, s: Shape) -> usize {
        fn w(p: &[Entry], s: Shape) -> usize {
            let e = p[0];
            if e.level.is_leaf() {
                return 0;
            }
            let t = e.level.sub(s);
            let blocks = e.level.rank() * ((t.m * t.k + pad()) + (t.k * t.n + pad()) + (t.m * t.n + pad()));
            blocks + if e.pipe.is_some() { 2 } else { 1 } * w(&p[1..], t)
        }
        w(&self.0, s)
    }

    /// whether every level divides the shape it receives
    pub fn divides(&self, s: Shape) -> bool {
        let mut cur = s;
        for e in &self.0 {
            if !e.level.divides(cur) {
                return false;
            }
            cur = e.level.sub(cur);
        }
        true
    }

    /// "D48+3/D48/G6", or a named method of bench_fmm ("dps48", "sw3rec", "r336x2", ...)
    pub fn parse(s: &str) -> Option<Plan> {
        const NAMED: [(&str, &str); 16] = [("classical", "G"), ("blk2", "B2"), ("sw1", "SW/G"), ("sw2rec", "SW/SW/G"),
                                           ("sw3rec", "SW/SW/SW/G"), ("sw4rec", "SW/SW/SW/SW/G"), ("dps48", "D48/G"),
                                           ("dps48sw", "D48/SW/G"), ("dps48x2", "D48/D48/G"), ("r336", "R336/G"),
                                           ("r363", "R363/G"), ("r633", "R633/G"), ("r336x2", "R336/R363/G"),
                                           ("r336x3", "R336/R363/R633/G"), ("swr336", "SW/R336/G"), ("r336sw", "R336/SW/G")];
        let s = s.strip_prefix("plan=").unwrap_or(s);
        let s = NAMED.iter().find(|(n, _)| *n == s).map(|(_, l)| *l).unwrap_or(s);
        let parts: Vec<&str> = s.split('/').collect();
        let mut v = vec![];
        for (k, t) in parts.iter().enumerate() {
            let (t, pipe) = match t.split_once('+') {
                Some((name, p)) => (name, Some(if p.is_empty() { 0 } else { p.parse().ok()? })),
                None => (*t, None),
            };
            let (level, streams) = match Level::from_name(t) {
                Some(l) => (l, 0),
                None if t.starts_with('G') && t.len() > 1 => (Level::G, t[1..].parse().ok()?),
                None => return None,
            };
            // a leaf ends the plan; streams only below a level; pipelines only of levels
            if level.is_leaf() != (k + 1 == parts.len()) || (streams > 0 && k == 0) || (pipe.is_some() && level.is_leaf()) {
                return None;
            }
            v.push(Entry { level, streams, pipe });
        }
        Some(Plan(v))
    }
}

impl fmt::Display for Plan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (k, e) in self.0.iter().enumerate() {
            if k > 0 {
                write!(f, "/")?;
            }
            write!(f, "{}", e.level.name())?;
            if e.streams > 0 {
                write!(f, "{}", e.streams)?;
            }
            match e.pipe {
                Some(0) => write!(f, "+")?,
                Some(p) => write!(f, "+{p}")?,
                None => {}
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_round_trip() {
        for s in ["G", "B2", "SW/G", "D48/G6", "D48+3/D48/G6", "SW/D48+4/D48/G6", "D48+/SW/G3", "SW+2/SW/B2", "R336/R363/R633/G",
                  "R363+3/D48/G6", "SW/R363+3/R633/G6"] {
            assert_eq!(Plan::parse(s).map(|p| p.to_string()), Some(s.to_string()));
        }
        assert_eq!(Plan::parse("dps48x2").map(|p| p.to_string()), Some("D48/D48/G".to_string()));
        assert_eq!(Plan::parse("r336x3").map(|p| p.to_string()), Some("R336/R363/R633/G".to_string()));
        assert_eq!(Plan::parse("plan=sw1").map(|p| p.to_string()), Some("SW/G".to_string()));
        for s in ["", "G/D48", "D48", "G6", "D48/X", "G+2", "D48+x/G", "D48//G", "SW/G/G", "R36/G"] {
            assert!(Plan::parse(s).is_none(), "{s}");
        }
    }

    #[test]
    fn work_and_divisibility() {
        let p = Plan::parse("D48/G").unwrap();
        assert_eq!(p.work(Shape::sq(4096)), 3 * 48 * (1024 * 1024 + pad()));
        let p = Plan::parse("D48+2/SW/G").unwrap();
        assert_eq!(p.work(Shape::sq(4096)), 3 * 48 * (1024 * 1024 + pad()) + 2 * 3 * 7 * (512 * 512 + pad()));
        // R336 on 54^3: products (18, 18, 9): S blocks 18x18, T blocks 18x9, M blocks 18x9
        let p = Plan::parse("R336/G").unwrap();
        assert_eq!(p.work(Shape::sq(54)), 40 * ((18 * 18 + pad()) + (18 * 9 + pad()) + (18 * 9 + pad())));
        assert!(Plan::parse("D48/D48/G").unwrap().divides(Shape::sq(4096)));
        assert!(!Plan::parse("D48/D48/G").unwrap().divides(Shape::sq(4100)));
        assert!(Plan::parse("SW/G").unwrap().divides(Shape::sq(4100)));
        assert!(Plan::parse("R336/R363/R633/G").unwrap().divides(Shape::sq(54)));
        assert!(!Plan::parse("R336/R363/R633/G").unwrap().divides(Shape::sq(36)));
        assert!(Plan::parse("R336/G").unwrap().divides(Shape::new(3, 3, 6)));
        assert!(!Plan::parse("R336/G").unwrap().divides(Shape::new(3, 6, 3)));
        assert_eq!(Level::R363.sub(Shape::new(6, 12, 9)), Shape::new(2, 2, 3));
        assert_eq!(Level::R363.up(Shape::new(2, 2, 3)), Shape::new(6, 12, 9));
        assert_eq!(Shape::sq(7).to_string(), "7");
        assert_eq!(Shape::new(1, 2, 3).to_string(), "1x2x3");
    }
}
