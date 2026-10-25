//! Plans: fused levels from the top, ending in a leaf.  Written as in the C library: G (one GEMM),
//! Gk (a level's products as k single-threaded GEMM streams), B2 (classical blocked 2x2), SW
//! (Strassen-Winograd <2x2x2:7>), D48 (the rank-48 <4x4x4:48> scheme of Dumas, Pernet and
//! Sedoglavic), and D48+p / SW+p (the level's sub-problems pipelined on p pass threads).

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

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum Level {
    G,
    B2,
    Sw,
    D48,
}

impl Level {
    pub fn is_leaf(self) -> bool {
        matches!(self, Level::G | Level::B2)
    }
    pub fn grid(self) -> usize {
        match self {
            Level::G => 1,
            Level::B2 | Level::Sw => 2,
            Level::D48 => 4,
        }
    }
    pub fn rank(self) -> usize {
        match self {
            Level::Sw => 7,
            Level::D48 => 48,
            Level::B2 => 8,
            Level::G => 1,
        }
    }
    pub fn name(self) -> &'static str {
        match self {
            Level::G => "G",
            Level::B2 => "B2",
            Level::Sw => "SW",
            Level::D48 => "D48",
        }
    }
    pub fn from_name(s: &str) -> Option<Level> {
        [Level::G, Level::B2, Level::Sw, Level::D48].into_iter().find(|l| l.name() == s)
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

    /// scratch elements the plan needs at size n: each fused level 3 r blocks of m*m + pad (S,
    /// T, M), the levels below reusing theirs product after product, a pipelined level twice
    pub fn work(&self, n: usize) -> usize {
        fn w(p: &[Entry], n: usize) -> usize {
            let e = p[0];
            if e.level.is_leaf() {
                return 0;
            }
            let m = n / e.level.grid();
            3 * e.level.rank() * (m * m + pad()) + if e.pipe.is_some() { 2 } else { 1 } * w(&p[1..], m)
        }
        w(&self.0, n)
    }

    /// whether every level divides the size it receives
    pub fn divides(&self, n: usize) -> bool {
        let mut s = n;
        for e in &self.0 {
            if s % e.level.grid() != 0 {
                return false;
            }
            s /= e.level.grid();
        }
        true
    }

    /// "D48+3/D48/G6", or a named method of bench_fmm ("dps48", "sw3rec", ...)
    pub fn parse(s: &str) -> Option<Plan> {
        const NAMED: [(&str, &str); 9] = [("classical", "G"), ("blk2", "B2"), ("sw1", "SW/G"), ("sw2rec", "SW/SW/G"),
                                          ("sw3rec", "SW/SW/SW/G"), ("sw4rec", "SW/SW/SW/SW/G"), ("dps48", "D48/G"),
                                          ("dps48sw", "D48/SW/G"), ("dps48x2", "D48/D48/G")];
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
        for s in ["G", "B2", "SW/G", "D48/G6", "D48+3/D48/G6", "SW/D48+4/D48/G6", "D48+/SW/G3", "SW+2/SW/B2"] {
            assert_eq!(Plan::parse(s).map(|p| p.to_string()), Some(s.to_string()));
        }
        assert_eq!(Plan::parse("dps48x2").map(|p| p.to_string()), Some("D48/D48/G".to_string()));
        assert_eq!(Plan::parse("plan=sw1").map(|p| p.to_string()), Some("SW/G".to_string()));
        for s in ["", "G/D48", "D48", "G6", "D48/X", "G+2", "D48+x/G", "D48//G", "SW/G/G"] {
            assert!(Plan::parse(s).is_none(), "{s}");
        }
    }

    #[test]
    fn work_and_divisibility() {
        let p = Plan::parse("D48/G").unwrap();
        assert_eq!(p.work(4096), 3 * 48 * (1024 * 1024 + pad()));
        let p = Plan::parse("D48+2/SW/G").unwrap();
        assert_eq!(p.work(4096), 3 * 48 * (1024 * 1024 + pad()) + 2 * 3 * 7 * (512 * 512 + pad()));
        assert!(Plan::parse("D48/D48/G").unwrap().divides(4096));
        assert!(!Plan::parse("D48/D48/G").unwrap().divides(4100));
        assert!(Plan::parse("SW/G").unwrap().divides(4100));
    }
}
