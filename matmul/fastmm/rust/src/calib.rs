//! The calibration: measured seconds per (kind, size), cached in the C library's file format
//! (FMM_CALIB_DIR, default ~/Library/Caches/fmm, calib_f32.txt / calib_f64.txt), so the C and
//! Rust libraries share one cache.  A cache is used only if it was measured on this machine,
//! with this padding, format and D48 program.
//!
//! Kinds: G m, B2 m (a plan's top leaf alone: one GEMM, classical blocked 2x2, at size m); SW m,
//! D48 m (the three passes of such a level whose blocks have size m); GSW m, GkD48 m (the GEMM
//! time per product inside such a level, run one at a time or as k streams); PYkKpPs m, PYkKpPo m
//! (the steady time per sub-problem and the fill and drain of a pipeline of level-Y sub-problems
//! with blocks m over K streams with P pass threads); ESW, ED48, ED48D48 at 2048 (the error
//! model's measurements).

use crate::kernels;
use crate::plan::{pad, Level};
use std::collections::BTreeMap;
use std::path::PathBuf;
use std::sync::OnceLock;

pub const FORMAT: u32 = 4;
/// the size of the error model's measurements
pub const N_E: usize = 2048;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum Kind {
    Leaf(Level),
    Passes(Level),
    Gin(Level, u8),
    Pipe { level: Level, streams: u8, passes: u8, over: bool },
    Err(u8),
}

impl Kind {
    pub fn name(&self) -> String {
        match *self {
            Kind::Leaf(l) | Kind::Passes(l) => l.name().to_string(),
            Kind::Gin(l, 0) => format!("G{}", l.name()),
            Kind::Gin(l, k) => format!("G{k}{}", l.name()),
            Kind::Pipe { level, streams, passes, over } => {
                format!("P{}k{streams}p{passes}{}", level.name(), if over { 'o' } else { 's' })
            }
            Kind::Err(i) => ["ESW", "ED48", "ED48D48"][i as usize].to_string(),
        }
    }

    pub fn parse(s: &str) -> Option<Kind> {
        if let Some(l) = Level::from_name(s) {
            return Some(if l.is_leaf() { Kind::Leaf(l) } else { Kind::Passes(l) });
        }
        if let Some(i) = ["ESW", "ED48", "ED48D48"].iter().position(|e| *e == s) {
            return Some(Kind::Err(i as u8));
        }
        if let Some(rest) = s.strip_prefix('P') {
            let (name, rest) = rest.split_once('k')?;
            let (k, rest) = rest.split_once('p')?;
            let (p, part) = rest.split_at(rest.len().checked_sub(1)?);
            let level = Level::from_name(name)?;
            return Some(Kind::Pipe { level, streams: k.parse().ok()?, passes: p.parse().ok()?, over: part == "o" })
                .filter(|_| part == "o" || part == "s");
        }
        let rest = s.strip_prefix('G')?;
        let digits = rest.bytes().take_while(u8::is_ascii_digit).count();
        let k = if digits == 0 { 0 } else { rest[..digits].parse().ok()? };
        let level = Level::from_name(&rest[digits..]).filter(|l| !l.is_leaf())?;
        Some(Kind::Gin(level, k))
    }
}

#[derive(Clone, Default, Debug)]
pub struct Calib {
    pub entries: BTreeMap<(Kind, usize), f64>,
}

impl Calib {
    pub fn get(&self, kind: Kind, m: usize) -> Option<f64> {
        self.entries.get(&(kind, m)).copied()
    }

    pub fn put(&mut self, kind: Kind, m: usize, t: f64) {
        self.entries.insert((kind, m), t);
    }

    /// a cost-model entry at any size m: the measured value, else log-log interpolation between
    /// the nearest measured sizes below and above (times go like m^3 for GEMMs and m^2 for passes,
    /// a straight line in log-log); None outside the measured range
    pub fn cost(&self, kind: Kind, m: usize) -> Option<f64> {
        if let Some(t) = self.get(kind, m) {
            return Some(t);
        }
        let below = self.entries.range((kind, 0)..(kind, m)).next_back().map(|(&(_, s), &t)| (s, t));
        let above = self.entries.range((kind, m + 1)..=(kind, usize::MAX)).next().map(|(&(_, s), &t)| (s, t));
        let ((lo, tlo), (hi, thi)) = (below?, above?);
        if lo == 0 || tlo <= 0.0 || thi <= 0.0 {
            return None;
        }
        let x = (m as f64 / lo as f64).ln() / (hi as f64 / lo as f64).ln();
        Some(tlo * (thi / tlo).powf(x))
    }
}

/// the stream counts the planner considers for a level's products, and its pipelines
pub const STREAMS: [u8; 4] = [0, 3, 4, 6];
pub const PIPE_K: [u8; 2] = [3, 6];
pub const PIPE_P: [u8; 3] = [2, 3, 4];

/// the entries the planner needs for n: the leaves alone at n, and for each fused level its
/// passes, per-product GEMM (every stream count) and pipelines of the levels below, at blocks
/// n/g, and the needs of n/g
pub fn need(n: usize) -> Vec<(Kind, usize)> {
    fn put(out: &mut Vec<(Kind, usize)>, k: Kind, m: usize) {
        if !out.contains(&(k, m)) {
            out.push((k, m));
        }
    }
    fn rec(n: usize, out: &mut Vec<(Kind, usize)>) {
        let put = |out: &mut Vec<(Kind, usize)>, k: Kind, m: usize| put(out, k, m);
        if n >= N_E {
            for i in 0..3 {
                put(out, Kind::Err(i), N_E);
            }
        }
        put(out, Kind::Leaf(Level::G), n);
        if n % 2 == 0 && n / 2 >= crate::plan::minb() {
            put(out, Kind::Leaf(Level::B2), n);
        }
        for lv in [Level::Sw, Level::D48] {
            let g = lv.grid();
            if n % g != 0 || n / g < crate::plan::minb() {
                continue;
            }
            put(out, Kind::Passes(lv), n / g);
            for k in STREAMS {
                put(out, Kind::Gin(lv, k), n / g);
            }
            for ly in [Level::Sw, Level::D48] {
                let gy = ly.grid();
                let my = n / g / gy;
                if (n / g) % gy != 0 || my < crate::plan::minb() {
                    continue;
                }
                for k in PIPE_K {
                    for p in PIPE_P {
                        for over in [false, true] {
                            put(out, Kind::Pipe { level: ly, streams: k, passes: p, over }, my);
                        }
                    }
                }
            }
            rec(n / g, out);
        }
    }
    let mut out = vec![];
    rec(n, &mut out);
    out
}

pub fn machine() -> &'static str {
    static M: OnceLock<String> = OnceLock::new();
    M.get_or_init(|| {
        std::process::Command::new("sysctl")
            .args(["-n", "machdep.cpu.brand_string"])
            .output()
            .ok()
            .and_then(|o| String::from_utf8(o.stdout).ok())
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty())
            .unwrap_or_else(|| "unknown".to_string())
    })
}

/// the cache: FMM_CALIB_DIR, default ~/Library/Caches/fmm
pub fn path(f64: bool) -> PathBuf {
    let dir = std::env::var_os("FMM_CALIB_DIR").map(PathBuf::from).unwrap_or_else(|| {
        let home = std::env::var_os("HOME").map(PathBuf::from).unwrap_or_else(|| PathBuf::from("."));
        home.join("Library/Caches/fmm")
    });
    dir.join(if f64 { "calib_f64.txt" } else { "calib_f32.txt" })
}

fn kernels_key() -> String {
    format!("{} {}", kernels::DPS48_PROGRAM, kernels::DPS48_OPS)
}

/// the cache, if it was measured on this machine with this padding, format and D48 program
pub fn load(f64: bool) -> Calib {
    let mut c = Calib::default();
    if std::env::var("FMM_RECALIB").ok().and_then(|s| s.parse::<i32>().ok()).unwrap_or(0) != 0 {
        return c;
    }
    let Ok(text) = std::fs::read_to_string(path(f64)) else { return c };
    let (mut ok_machine, mut ok_pad, mut ok_format, mut ok_kernels) = (false, false, false, false);
    for line in text.lines() {
        if let Some(v) = line.strip_prefix("# machine ") {
            ok_machine = v == machine();
        } else if let Some(v) = line.strip_prefix("# pad ") {
            ok_pad = v.trim().parse::<usize>().ok() == Some(pad());
        } else if let Some(v) = line.strip_prefix("# format ") {
            ok_format = v.trim().parse::<u32>().ok() == Some(FORMAT);
        } else if let Some(v) = line.strip_prefix("# kernels ") {
            ok_kernels = v == kernels_key();
        } else if !line.starts_with('#') {
            let mut f = line.split_whitespace();
            if let (Some(k), Some(m), Some(t)) = (f.next(), f.next(), f.next())
                && let (Some(kind), Ok(m), Ok(t)) = (Kind::parse(k), m.parse(), t.parse())
            {
                c.put(kind, m, t);
            }
        }
    }
    if ok_machine && ok_pad && ok_format && ok_kernels { c } else { Calib::default() }
}

pub fn save(c: &Calib, f64: bool) -> std::io::Result<()> {
    let p = path(f64);
    if let Some(dir) = p.parent() {
        std::fs::create_dir_all(dir)?;
    }
    let mut s = format!(
        "# bench_fmm calibration, {}, seconds: G m = one GEMM of size m, B2 m = classical blocked 2x2 at size m \
         (one call each); SW m, D48 m = the three passes of one such level with blocks of size m; GSW m, GD48 m = \
         its GEMM time per product, GkSW m, GkD48 m = the same with k GEMM streams\n",
        if f64 { "f64" } else { "f32" }
    );
    s += &format!("# machine {}\n# pad {}\n# format {}\n# kernels {}\n", machine(), pad(), FORMAT, kernels_key());
    for (&(kind, m), &t) in &c.entries {
        s += &format!("{} {} {}\n", kind.name(), m, fmt_g9(t));
    }
    std::fs::write(p, s)
}

/// C's %.{prec}e (an exponent with a sign and at least two digits)
pub fn fmt_e(x: f64, prec: usize) -> String {
    let s = format!("{x:.prec$e}");
    let (mant, exp) = s.split_once('e').unwrap_or((&s, "0"));
    let e: i32 = exp.parse().unwrap_or(0);
    format!("{mant}e{}{:02}", if e < 0 { '-' } else { '+' }, e.abs())
}

/// nine significant digits, as the C library's %.9g (so both libraries write the same file)
fn fmt_g9(t: f64) -> String {
    if t == 0.0 {
        return "0".to_string();
    }
    let trim = |x: &str| if x.contains('.') { x.trim_end_matches('0').trim_end_matches('.').to_string() } else { x.to_string() };
    let s = format!("{t:.8e}");                     // the exponent after rounding to nine digits
    let (mant, exp) = s.split_once('e').unwrap_or((&s, "0"));
    let e: i32 = exp.parse().unwrap_or(0);
    if (-4..9).contains(&e) {
        trim(&format!("{t:.*}", (8 - e) as usize))
    } else {
        format!("{}e{}{:02}", trim(mant), if e < 0 { '-' } else { '+' }, e.abs())
    }
}

/// the error model: a plan's error (max-norm, relative, against the classical GEMM on uniform
/// random inputs) is the classical error scale times one factor per fused level, growing like
/// sqrt(n); fitted from SW/G, D48/G and D48/D48/G at N_E
#[derive(Clone, Copy, Debug)]
pub struct ErrModel {
    pub base: f64,
    pub f_sw: f64,
    pub f_d48: f64,
}

impl Calib {
    pub fn err_model(&self) -> Option<ErrModel> {
        let (esw, e1, e2) = (self.get(Kind::Err(0), N_E)?, self.get(Kind::Err(1), N_E)?, self.get(Kind::Err(2), N_E)?);
        if esw <= 0.0 || e1 <= 0.0 || e2 <= 0.0 {
            return None;
        }
        let f_d48 = e2 / e1;
        let base = e1 / f_d48;
        Some(ErrModel { base, f_sw: esw / base, f_d48 })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn g9_matches_c() {
        for (x, c) in [(0.0123456789012, "0.0123456789"), (1.5, "1.5"), (2.37e-14, "2.37e-14"), (1234567890.0, "1.23456789e+09"),
                       (5.1234e-05, "5.1234e-05"), (0.000123456789, "0.000123456789"), (1.0, "1"), (0.31337, "0.31337"),
                       (9.9999999996e8, "1e+09"), (4.47e-06, "4.47e-06"), (11.8984, "11.8984"), (1e-05, "1e-05"), (0.0, "0")] {
            assert_eq!(fmt_g9(x), c, "{x:e}");
        }
        for (x, p, c) in [(3.9804829e-06, 3, "3.980e-06"), (0.0, 2, "0.00e+00"), (2.37e-14, 2, "2.37e-14"), (1234.5, 2, "1.23e+03")] {
            assert_eq!(fmt_e(x, p), c);
        }
    }

    #[test]
    fn kind_names_round_trip() {
        let need = need(16384);
        assert!(need.len() > 100);
        for (k, _) in need {
            assert_eq!(Kind::parse(&k.name()), Some(k), "{}", k.name());
        }
        for s in ["G", "B2", "SW", "D48", "GSW", "G6D48", "PD48k6p2s", "PSWk3p4o", "ESW", "ED48D48"] {
            assert_eq!(Kind::parse(s).map(|k| k.name()), Some(s.to_string()));
        }
        for s in ["", "X", "GG", "G6", "PD48k6p2", "PD48k6p2x", "E"] {
            assert_eq!(Kind::parse(s), None, "{s}");
        }
    }

    #[test]
    fn interpolation() {
        let mut c = Calib::default();
        c.put(Kind::Leaf(Level::G), 1024, 1.0);
        c.put(Kind::Leaf(Level::G), 4096, 64.0);
        let t = c.cost(Kind::Leaf(Level::G), 2048).unwrap();
        assert!((t - 8.0).abs() < 1e-9);
        assert_eq!(c.cost(Kind::Leaf(Level::G), 512), None);
        assert_eq!(c.cost(Kind::Leaf(Level::G), 8192), None);
        assert_eq!(c.cost(Kind::Leaf(Level::B2), 2048), None);
    }
}
