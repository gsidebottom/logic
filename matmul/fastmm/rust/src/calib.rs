//! The calibration: measured seconds per (kind, shape), cached in the C library's file format
//! (FMM_CALIB_DIR, default ~/Library/Caches/fmm, calib5_f32.txt / calib5_f64.txt), so the C and
//! Rust libraries share one cache.  A cache is used only if it was measured on this machine,
//! with this padding, format and kernels.
//!
//! An entry's shape is that of a product (m x k)(k x n).  Kinds: G, B2 (a plan's top leaf alone:
//! one GEMM, classical blocked 2x2, on that shape); SW, D48, R336, R363, R633 (the three passes of
//! such a level whose products have that shape); GSW, GkD48, ... (the GEMM time per product inside
//! such a level, run one at a time or as k streams); PYkKpPs, PYkKpPo (the steady time per
//! sub-problem and the fill and drain of a pipeline of level-Y sub-problems whose products have
//! that shape, over K streams with P pass threads); ESW, ED48, ED48D48, ER336, ER363, ER633 at
//! N_E (the error model's measurements).

use crate::kernels;
use crate::plan::{pad, Level, Shape};
use std::collections::BTreeMap;
use std::path::PathBuf;
use std::sync::OnceLock;

pub const FORMAT: u32 = 5;
/// the size of the error model's measurements: 16 (D48/D48), 3 and 6 (the R levels) divide it
pub const N_E: usize = 2304;
/// the error model's plans and their entry names
/// the error model's plans at N_E, each measured against the exact product; the last, the
/// classical GEMM alone (EG), is the model's base, and a cache without it has the old entries
/// (measured against the GEMM) and re-measures all of them
pub const ERR_PLANS: [&str; 7] = ["SW/G", "D48/G", "D48/D48/G", "R336/G", "R363/G", "R633/G", "G"];
pub const ERR_NAMES: [&str; 7] = ["ESW", "ED48", "ED48D48", "ER336", "ER363", "ER633", "EG"];

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
            Kind::Err(i) => ERR_NAMES[i as usize].to_string(),
        }
    }

    pub fn parse(s: &str) -> Option<Kind> {
        if let Some(l) = Level::from_name(s) {
            return Some(if l.is_leaf() { Kind::Leaf(l) } else { Kind::Passes(l) });
        }
        if let Some(i) = ERR_NAMES.iter().position(|e| *e == s) {
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
    pub entries: BTreeMap<(Kind, Shape), f64>,
}

impl Calib {
    pub fn get(&self, kind: Kind, s: Shape) -> Option<f64> {
        self.entries.get(&(kind, s)).copied()
    }

    pub fn put(&mut self, kind: Kind, s: Shape, t: f64) {
        self.entries.insert((kind, s), t);
    }

    /// a cost-model entry at any shape: the measured value, else log-log interpolation between the
    /// nearest measured square sizes below and above the shape's equivalent square size (times go
    /// like m^3 for GEMMs and m^2 for passes, a straight line in log-log; for a rectangular shape
    /// an estimate, which `calibrate_mkn` replaces by measurements); None outside the measured range
    pub fn cost(&self, kind: Kind, s: Shape) -> Option<f64> {
        if let Some(t) = self.get(kind, s) {
            return Some(t);
        }
        let m = equivalent(kind, s);
        let (mut lo, mut hi, mut teq): (Option<(f64, f64)>, Option<(f64, f64)>, Option<f64>) = (None, None, None);
        for (&(_, cs), &t) in self.entries.range((kind, Shape::sq(0))..=(kind, Shape::new(usize::MAX, usize::MAX, usize::MAX))) {
            if !cs.is_sq() {
                continue;
            }
            let cm = cs.m as f64;
            if cm == m {
                teq = Some(t);
            } else if cm < m && lo.is_none_or(|(l, _)| cm > l) {
                lo = Some((cm, t));
            } else if cm > m && hi.is_none_or(|(h, _)| cm < h) {
                hi = Some((cm, t));
            }
        }
        if teq.is_some() {
            return teq;
        }
        let ((lo, tlo), (hi, thi)) = (lo?, hi?);
        if lo <= 0.0 || tlo <= 0.0 || thi <= 0.0 {
            return None;
        }
        let x = (m / lo).ln() / (hi / lo).ln();
        Some(tlo * (thi / tlo).powf(x))
    }
}

/// the square size whose entry of this kind costs what a rectangular shape's would, for a shape
/// that was not measured: GEMM-like entries (a leaf, the GEMM per product, a pipeline's steady and
/// fill times) go by flops, cbrt(m k n) (Accelerate runs rectangular shapes within 5% of the square
/// rate), the passes of a level by their traffic, (g1 g2 + r) m k + (g2 g3 + r) k n + (g1 g3 + r) m n
/// words for its blocks of each operand against (g1 g2 + g2 g3 + g1 g3 + 3 r) m'^2 for a square m'.
/// The same arithmetic as the C library's shape_equiv, so both price a shape alike.
pub fn equivalent(kind: Kind, s: Shape) -> f64 {
    if s.is_sq() {
        return s.m as f64;
    }
    let (m, k, n) = (s.m as f64, s.k as f64, s.n as f64);
    match kind {
        Kind::Passes(lv) => {
            let (g1, g2, g3) = lv.grid();
            let r = lv.rank();
            let w = ((g1 * g2 + r) as f64) * (m * k) + ((g2 * g3 + r) as f64) * (k * n) + ((g1 * g3 + r) as f64) * (m * n);
            (w / ((g1 * g2 + g2 * g3 + g1 * g3 + 3 * r) as f64)).sqrt()
        }
        _ => (m * k * n).cbrt(),
    }
}

/// the stream counts the planner considers for a level's products, and its pipelines
pub const STREAMS: [u8; 4] = [0, 3, 4, 6];
pub const PIPE_K: [u8; 2] = [3, 6];
pub const PIPE_P: [u8; 3] = [2, 3, 4];

/// the entries the planner needs for a problem of shape s: the leaves alone at s, and for each
/// fused level dividing s its passes, per-product GEMM (every stream count) and pipelines of the
/// levels below, at its product shape, and the needs of that shape; the error model once, for
/// square problems of N_E and up
pub fn need(s: Shape) -> Vec<(Kind, Shape)> {
    fn put(out: &mut Vec<(Kind, Shape)>, k: Kind, s: Shape) {
        if !out.contains(&(k, s)) {
            out.push((k, s));
        }
    }
    fn rec(s: Shape, out: &mut Vec<(Kind, Shape)>) {
        let minb = crate::plan::minb();
        if s.is_sq() && s.m >= N_E {
            for i in 0..ERR_PLANS.len() {
                put(out, Kind::Err(i as u8), Shape::sq(N_E));
            }
        }
        put(out, Kind::Leaf(Level::G), s);
        if s.is_sq() && s.m % 2 == 0 && s.m / 2 >= minb {
            put(out, Kind::Leaf(Level::B2), s);
        }
        for lv in Level::FUSED {
            if !lv.divides(s) || lv.sub(s).min_dim() < minb {
                continue;
            }
            let t = lv.sub(s);
            put(out, Kind::Passes(lv), t);
            for k in STREAMS {
                put(out, Kind::Gin(lv, k), t);
            }
            for ly in Level::FUSED {
                if !ly.divides(t) || ly.sub(t).min_dim() < minb {
                    continue;
                }
                let ty = ly.sub(t);
                for k in PIPE_K {
                    for p in PIPE_P {
                        for over in [false, true] {
                            put(out, Kind::Pipe { level: ly, streams: k, passes: p, over }, ty);
                        }
                    }
                }
            }
            rec(t, out);
        }
    }
    let mut out = vec![];
    rec(s, &mut out);
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
    dir.join(if f64 { "calib5_f64.txt" } else { "calib5_f32.txt" })
}

/// the kernels the cache was measured with: the D48 program, the R levels' operation counts and the
/// 2x2 level's programs (the C library writes the same string)
fn kernels_key() -> String {
    format!("{} {} R {} SW {} {}", kernels::DPS48_PROGRAM, kernels::DPS48_OPS, kernels::R_OPS,
            kernels::SW_PROGRAM, kernels::SW_OPS)
}

/// the cache, if it was measured on this machine with this padding, format and kernels
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
            let f: Vec<&str> = line.split_whitespace().collect();
            if f.len() == 5
                && let (Some(kind), Ok(m), Ok(k), Ok(n), Ok(t)) =
                    (Kind::parse(f[0]), f[1].parse(), f[2].parse(), f[3].parse(), f[4].parse())
            {
                c.put(kind, Shape::new(m, k, n), t);
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
        "# bench_fmm calibration, {}, seconds; entries kind m k n t for a product of shape (m x k)(k x n): G = one GEMM of \
         that shape, B2 = classical blocked 2x2 (one call each); SW, D48, R336, R363, R633 = the three passes of one such \
         level whose products have that shape; GSW, GD48, ... = its GEMM time per product, GkSW, GkD48, ... = the same \
         with k GEMM streams; PYkKpPs, PYkKpPo = pipelined sub-problems of level Y (steady time, fill and drain); E... = \
         errors at n = N_E\n",
        if f64 { "f64" } else { "f32" }
    );
    s += &format!("# machine {}\n# pad {}\n# format {}\n# kernels {}\n", machine(), pad(), FORMAT, kernels_key());
    for (&(kind, sh), &t) in &c.entries {
        s += &format!("{} {} {} {} {}\n", kind.name(), sh.m, sh.k, sh.n, fmt_g9(t));
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

/// the error model: a plan's error (max-norm, relative, against the exact product on uniform
/// random inputs) is the classical GEMM's own error times one factor per fused level, growing
/// like the square root of the inner dimension; the GEMM's error and the factors (one level over
/// the GEMM, divided by the GEMM alone) are the ERR_PLANS' measurements at N_E; a factor below 1
/// is a level more accurate than the GEMM, because its leaves sum k/g2 products instead of k; a
/// second level does not get that again, so the two-level plan D48/D48 measures the depth factor
/// rho by which the product of the factors is multiplied once per fused level after the first
#[derive(Clone, Copy, Debug)]
pub struct ErrModel {
    pub base: f64,
    pub rho: f64,
    /// the factor of each fused level, by Level::ALL's order
    pub f: [f64; 7],
}

impl ErrModel {
    pub fn factor(&self, lv: Level) -> f64 {
        self.f[Level::ALL.iter().position(|l| *l == lv).unwrap_or(0)]
    }
}

impl Calib {
    pub fn err_model(&self) -> Option<ErrModel> {
        let mut v = [0.0; 7];
        for (i, x) in v.iter_mut().enumerate() {
            *x = self.get(Kind::Err(i as u8), Shape::sq(N_E))?;
            if *x <= 0.0 {
                return None;
            }
        }
        let base = v[6];                        /* the classical GEMM's own error at N_E */
        let rho = v[2] * base / (v[1] * v[1]);  /* D48/D48 over the product of two D48 factors */
        let mut f = [1.0; 7];
        let set = |f: &mut [f64; 7], lv: Level, x: f64| f[Level::ALL.iter().position(|l| *l == lv).unwrap()] = x;
        set(&mut f, Level::Sw, v[0] / base);
        set(&mut f, Level::D48, v[1] / base);
        set(&mut f, Level::R336, v[3] / base);
        set(&mut f, Level::R363, v[4] / base);
        set(&mut f, Level::R633, v[5] / base);
        Some(ErrModel { base, rho, f })
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
        let need = need(Shape::sq(13824));
        assert!(need.len() > 300, "{}", need.len());
        for (k, _) in need {
            assert_eq!(Kind::parse(&k.name()), Some(k), "{}", k.name());
        }
        for s in ["G", "B2", "SW", "D48", "R336", "GSW", "G6D48", "G3R363", "PD48k6p2s", "PSWk3p4o", "PR633k6p4s", "ESW", "ED48D48", "ER633"] {
            assert_eq!(Kind::parse(s).map(|k| k.name()), Some(s.to_string()));
        }
        for s in ["", "X", "GG", "G6", "PD48k6p2", "PD48k6p2x", "E", "R36"] {
            assert_eq!(Kind::parse(s), None, "{s}");
        }
    }

    #[test]
    fn interpolation() {
        let mut c = Calib::default();
        c.put(Kind::Leaf(Level::G), Shape::sq(1024), 1.0);
        c.put(Kind::Leaf(Level::G), Shape::sq(4096), 64.0);
        c.put(Kind::Leaf(Level::G), Shape::new(2048, 2048, 1024), 3.0);   // rectangular: exact only
        let t = c.cost(Kind::Leaf(Level::G), Shape::sq(2048)).unwrap();
        assert!((t - 8.0).abs() < 1e-9);
        assert_eq!(c.cost(Kind::Leaf(Level::G), Shape::sq(512)), None);
        assert_eq!(c.cost(Kind::Leaf(Level::G), Shape::sq(8192)), None);
        assert_eq!(c.cost(Kind::Leaf(Level::B2), Shape::sq(2048)), None);
        assert_eq!(c.cost(Kind::Leaf(Level::G), Shape::new(2048, 2048, 1024)), Some(3.0));
        // a rectangular shape without an entry: the estimate at its equivalent square size, here
        // cbrt(2048 * 1024 * 2048) = 1625.5 for a GEMM, (1625.5 / 1024)^3 = 4 in the m^3 interpolation
        let t = c.cost(Kind::Leaf(Level::G), Shape::new(2048, 1024, 2048)).unwrap();
        assert!((t - 4.0).abs() < 1e-9, "{t}");
        // exactly on a measured size: cbrt(2048 * 4096 * 1024) = 2048
        c.put(Kind::Leaf(Level::G), Shape::sq(2048), 8.5);
        assert_eq!(c.cost(Kind::Leaf(Level::G), Shape::new(2048, 4096, 1024)), Some(8.5));
        // passes go by traffic: R336 on (1152, 1152, 288) moves (9+40) m k + (18+40) k n + (18+40) m n
        // words against (9 + 18 + 18 + 120) m'^2
        let e = equivalent(Kind::Passes(Level::R336), Shape::new(1152, 1152, 288));
        let w = 49.0 * 1152.0 * 1152.0 + 58.0 * 1152.0 * 288.0 + 58.0 * 1152.0 * 288.0;
        assert!((e - (w / 165.0f64).sqrt()).abs() < 1e-9);
        assert_eq!(equivalent(Kind::Gin(Level::R336, 6), Shape::new(1152, 1152, 288)), (1152.0f64 * 1152.0 * 288.0).cbrt());
        assert_eq!(equivalent(Kind::Passes(Level::D48), Shape::sq(512)), 512.0);
    }

    #[test]
    fn needs_include_rectangular_products() {
        let n = need(Shape::sq(6912));
        assert!(n.contains(&(Kind::Passes(Level::R336), Shape::new(2304, 2304, 1152))));
        assert!(n.contains(&(Kind::Gin(Level::R363, 6), Shape::new(2304, 1152, 2304))));
        assert!(n.contains(&(Kind::Pipe { level: Level::D48, streams: 3, passes: 2, over: false }, Shape::new(576, 576, 288))));
        assert!(n.contains(&(Kind::Err(5), Shape::sq(N_E))));
        let r = need(Shape::new(3456, 3456, 1728));
        assert!(r.contains(&(Kind::Leaf(Level::G), Shape::new(3456, 3456, 1728))));
        assert!(!r.iter().any(|(k, _)| matches!(k, Kind::Err(_))));
    }
}
