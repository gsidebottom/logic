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
//! N_E (the error model's measurements).  With the GPU (f32, the feature `gpu`): GMX, GkMX (the GEMM
//! time per product of level X with its products shared between the GPU and Accelerate's own
//! threading or k streams), PYkKpPMs, PYkKpPMo (pipelines so shared) and K16, K32, K64 (the
//! classical product in strips: no passes, 0), kept in their own file beside the cache
//! (calib5gpu_f32.txt) as the C library keeps them, so builds without the GPU never see them.

use crate::kernels;
use crate::plan::{pad, Level, Shape};
use std::collections::BTreeMap;
use std::path::PathBuf;
use std::sync::OnceLock;

pub const FORMAT: u32 = 5;
/// the size of the error model's measurements: 16 (D48/D48) and 36 (the R levels in pairs) divide it
pub const N_E: usize = 2304;
/// the error model's levels; its entries are the errors against the exact product, at N_E, of the
/// GEMM alone (XG, entry 0), of each of these levels over the GEMM (XSW, ...; entry 1 + a) and of
/// each ordered pair of them (XSW/D48: SW on top; entry 6 + 5 a + b): the root mean square over
/// ERR_SEEDS random instances, since the max-norm error of one instance scatters 10-20%
pub const ERR_LV: [Level; 5] = [Level::Sw, Level::D48, Level::R336, Level::R363, Level::R633];
pub const NERR: usize = 1 + 5 + 25;
pub const ERR_SEEDS: usize = 4;

/// the fused levels of error entry i, top first
pub fn err_levels(i: usize) -> Vec<Level> {
    if i > 5 {
        vec![ERR_LV[(i - 6) / 5], ERR_LV[(i - 6) % 5]]
    } else if i > 0 {
        vec![ERR_LV[i - 1]]
    } else {
        vec![]
    }
}

pub fn err_name(i: usize) -> String {
    let lv = err_levels(i);
    if lv.is_empty() { "XG".to_string() } else { format!("X{}", lv.iter().map(|l| l.name()).collect::<Vec<_>>().join("/")) }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum Kind {
    Leaf(Level),
    Passes(Level),
    Gin(Level, u8),
    /// the GEMM time per product inside a level whose products are shared with the GPU
    Ggpu(Level, u8),
    Pipe { level: Level, streams: u8, passes: u8, over: bool, gpu: bool },
    Err(u8),
}

impl Kind {
    pub fn name(&self) -> String {
        match *self {
            Kind::Leaf(l) | Kind::Passes(l) => l.name().to_string(),
            Kind::Gin(l, 0) => format!("G{}", l.name()),
            Kind::Gin(l, k) => format!("G{k}{}", l.name()),
            Kind::Ggpu(l, 0) => format!("GM{}", l.name()),
            Kind::Ggpu(l, k) => format!("G{k}M{}", l.name()),
            Kind::Pipe { level, streams, passes, over, gpu } => {
                format!("P{}k{streams}p{passes}{}{}", level.name(), if gpu { "M" } else { "" }, if over { 'o' } else { 's' })
            }
            Kind::Err(i) => err_name(i as usize),
        }
    }

    pub fn parse(s: &str) -> Option<Kind> {
        if let Some(l) = Level::from_name(s) {
            return Some(if l.is_leaf() { Kind::Leaf(l) } else { Kind::Passes(l) });
        }
        if s.starts_with('X') {
            return (0..NERR).find(|&i| err_name(i) == s).map(|i| Kind::Err(i as u8));
        }
        if let Some(rest) = s.strip_prefix('P') {
            let (name, rest) = rest.split_once('k')?;
            let (k, rest) = rest.split_once('p')?;
            let (p, part) = rest.split_at(rest.len().checked_sub(1)?);
            let (p, gpu) = match p.strip_suffix('M') {
                Some(p) => (p, true),
                None => (p, false),
            };
            let level = Level::from_name(name)?;
            return Some(Kind::Pipe { level, streams: k.parse().ok()?, passes: p.parse().ok()?, over: part == "o", gpu })
                .filter(|_| part == "o" || part == "s");
        }
        let rest = s.strip_prefix('G')?;
        let digits = rest.bytes().take_while(u8::is_ascii_digit).count();
        let k = if digits == 0 { 0 } else { rest[..digits].parse().ok()? };
        if let Some(level) = Level::from_name(&rest[digits..]).filter(|l| !l.is_leaf()) {
            return Some(Kind::Gin(level, k));
        }
        let level = Level::from_name(rest[digits..].strip_prefix('M')?).filter(|l| !l.is_leaf())?;
        Some(Kind::Ggpu(level, k))
    }

    /// an entry of the GPU's file (calib5gpu_f32.txt): the GPU's leaves and pipelines, the K levels
    pub fn is_gpu(&self) -> bool {
        match *self {
            Kind::Ggpu(..) | Kind::Pipe { gpu: true, .. } => true,
            Kind::Passes(l) => l.is_split(),
            _ => false,
        }
    }
}

#[derive(Clone, Default, Debug)]
pub struct Calib {
    pub entries: BTreeMap<(Kind, Shape), f64>,
    /// the planner may share products with the GPU (f32, the feature `gpu`, a GPU, FMM_GPU != 0)
    pub gpu: bool,
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
/// with the GPU: the products shared between it and Accelerate's own threading (GM) or six streams
/// (G6M); pipelines of six streams and the GPU with 3 or 4 pass threads (the C library's rules)
pub const GSTREAMS: [u8; 2] = [0, 6];
pub const GPIPE_K: u8 = 6;
pub const GPIPE_P: [u8; 2] = [3, 4];

/// the entries the planner needs for a problem of shape s: the leaves alone at s, and for each
/// fused level dividing s its passes, per-product GEMM (every stream count) and pipelines of the
/// levels below, at its product shape, and the needs of that shape; the error model once, for
/// square problems of N_E and up; with the GPU (gpu) its entries too, and on top the K levels (their
/// products are strips of the problem, so they are measured for this shape only)
pub fn need(s: Shape, gpu: bool) -> Vec<(Kind, Shape)> {
    fn put(out: &mut Vec<(Kind, Shape)>, k: Kind, s: Shape) {
        if !out.contains(&(k, s)) {
            out.push((k, s));
        }
    }
    fn rec(s: Shape, gpu: bool, out: &mut Vec<(Kind, Shape)>) {
        use crate::plan::GPU_MINB;
        let minb = crate::plan::minb();
        if s.is_sq() && s.m >= N_E {
            for i in 0..NERR {
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
            if gpu && t.min_dim() >= GPU_MINB {
                for k in GSTREAMS {
                    put(out, Kind::Ggpu(lv, k), t);
                }
            }
            for ly in Level::FUSED {
                if !ly.divides(t) || ly.sub(t).min_dim() < minb {
                    continue;
                }
                let ty = ly.sub(t);
                for k in PIPE_K {
                    for p in PIPE_P {
                        for over in [false, true] {
                            put(out, Kind::Pipe { level: ly, streams: k, passes: p, over, gpu: false }, ty);
                        }
                    }
                }
                if gpu && ty.min_dim() >= GPU_MINB {
                    for p in GPIPE_P {
                        for over in [false, true] {
                            put(out, Kind::Pipe { level: ly, streams: GPIPE_K, passes: p, over, gpu: true }, ty);
                        }
                    }
                }
            }
            rec(t, gpu, out);
        }
    }
    let mut out = vec![];
    rec(s, gpu, &mut out);
    if gpu {
        for lv in Level::SPLIT {
            if !lv.divides(s) || lv.sub(s).m < crate::plan::K_MINROWS {
                continue;
            }
            put(&mut out, Kind::Passes(lv), lv.sub(s));
            for k in GSTREAMS {
                put(&mut out, Kind::Ggpu(lv, k), lv.sub(s));
            }
        }
    }
    out
}

/// whether the planner may use the GPU in this precision: f32, the feature `gpu`, a GPU, and
/// FMM_GPU not 0
pub fn gpu_mode(f64: bool) -> bool {
    !f64 && std::env::var("FMM_GPU").ok().and_then(|v| v.trim().parse::<i64>().ok()) != Some(0) && crate::gpu::available()
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

/// the GPU's entries, beside the cache
pub fn path_gpu() -> PathBuf {
    path(false).with_file_name("calib5gpu_f32.txt")
}

/// the kernels the cache was measured with: the D48 program, the R levels' operation counts and the
/// 2x2 level's programs (the C library writes the same string)
fn kernels_key() -> String {
    format!("{} {} R {} SW {} {}", kernels::DPS48_PROGRAM, kernels::DPS48_OPS, kernels::R_OPS,
            kernels::SW_PROGRAM, kernels::SW_OPS)
}

/// the entries of a cache file whose header matches this machine, padding, format and kernels
/// (keep: which kinds to take), None if it does not
fn read_file(p: &std::path::Path, keep: impl Fn(Kind) -> bool) -> Option<Vec<(Kind, Shape, f64)>> {
    let text = std::fs::read_to_string(p).ok()?;
    let mut v = vec![];
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
                && keep(kind)
            {
                v.push((kind, Shape::new(m, k, n), t));
            }
        }
    }
    (ok_machine && ok_pad && ok_format && ok_kernels).then_some(v)
}

/// the cache, if it was measured on this machine with this padding, format and kernels, and with
/// the GPU (gpu_mode) the GPU's entries from their file if it was measured beside it
pub fn load(f64: bool) -> Calib {
    let mut c = Calib { gpu: gpu_mode(f64), ..Calib::default() };
    if std::env::var("FMM_RECALIB").ok().and_then(|s| s.parse::<i32>().ok()).unwrap_or(0) != 0 {
        return c;
    }
    let Some(v) = read_file(&path(f64), |k| !k.is_gpu()) else { return c };
    for (kind, s, t) in v {
        c.put(kind, s, t);
    }
    if c.gpu {
        for (kind, s, t) in read_file(&path_gpu(), |k| k.is_gpu()).unwrap_or_default() {
            c.put(kind, s, t);
        }
    }
    c
}

/// the cache's two files: the entries without the GPU, and the GPU's if there are any
pub fn save(c: &Calib, f64: bool) -> std::io::Result<()> {
    let p = path(f64);
    if let Some(dir) = p.parent() {
        std::fs::create_dir_all(dir)?;
    }
    let head = format!("# machine {}\n# pad {}\n# format {}\n# kernels {}\n", machine(), pad(), FORMAT, kernels_key());
    let body = |gpu: bool| -> String {
        c.entries
            .iter()
            .filter(|((k, _), _)| k.is_gpu() == gpu)
            .map(|(&(kind, sh), &t)| format!("{} {} {} {} {}\n", kind.name(), sh.m, sh.k, sh.n, fmt_g9(t)))
            .collect()
    };
    if !f64 && c.entries.keys().any(|(k, _)| k.is_gpu()) {
        let g = "# bench_fmm calibration, f32, the GPU's entries (beside calib5_f32.txt): GMX, GkMX = the GEMM time per product \
                 of level X with its products shared between Accelerate's own threading (k streams) and the GPU; PYkKpPMs, \
                 PYkKpPMo = pipelined sub-problems of level Y so shared; K16, K32, K64 = the classical product in strips of rows \
                 (no passes: 0)\n";
        std::fs::write(path_gpu(), format!("{g}{head}{}", body(true)))?;
    }
    let mut s = format!(
        "# bench_fmm calibration, {}, seconds; entries kind m k n t for a product of shape (m x k)(k x n): G = one GEMM of \
         that shape, B2 = classical blocked 2x2 (one call each); SW, D48, R336, R363, R633 = the three passes of one such \
         level whose products have that shape; GSW, GD48, ... = its GEMM time per product, GkSW, GkD48, ... = the same \
         with k GEMM streams; PYkKpPs, PYkKpPo = pipelined sub-problems of level Y (steady time, fill and drain); E... = \
         errors at n = N_E\n",
        if f64 { "f64" } else { "f32" }
    );
    s += &head;
    s += &body(false);
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

/// The error model (the C library's, fmm.c "the accuracy budget", operation for operation).  A
/// plan's error (max-norm, relative, against the exact product on uniform random inputs), for the
/// fused levels X_1 (top) .. X_d over a GEMM leaf on a problem of inner dimension k:
///
/// ```text
/// E^2 = (x + y / N^(3/4)) k_leaf A_d^2  +  sum_i z_{X_i} A_{i-1}^2,
/// ```
///
/// with k_leaf = k / (g2 of every level), A_i = a_{X_1} .. a_{X_i} and N = nu_{X_1} .. nu_{X_d}.
/// The first term is the leaf GEMM's error, growing like sqrt(k_leaf), times every level's
/// amplification ratio a_X; its factor is the tail of the GEMM's error distribution, which an
/// output averaging the errors of nu_X products per level loses (x: fully averaged, y: the excess
/// of a single product).  The second is each level's own rounding z_X, which every level above it
/// amplifies: this is what makes the order of the levels matter.  a_X and nu_X come from the
/// scheme (kernels.rs); x, y and the z_X are fitted to the entries at N_E by a weighted linear
/// least squares on the squared errors, negative unknowns set to zero.  The GEMM alone: E^2 = eg2 k.
#[derive(Clone, Copy, Debug)]
pub struct ErrModel {
    pub eg2: f64,
    pub x: f64,
    pub y: f64,
    /// each level's own rounding, by Level::ALL's order (0 for the others)
    pub z: [f64; 10],
}

/// the amplification ratio and the participation number of a fused level's scheme
pub fn err_consts(lv: Level) -> (f64, f64) {
    match lv {
        Level::Sw => (kernels::SW_AMP, kernels::SW_NU),
        Level::D48 => (kernels::DPS48_AMP, kernels::DPS48_NU),
        Level::R336 => (kernels::R336_AMP, kernels::R336_NU),
        Level::R363 => (kernels::R363_AMP, kernels::R363_NU),
        Level::R633 => (kernels::R633_AMP, kernels::R633_NU),
        _ => (1.0, 1.0),
    }
}

/// the coefficients of x, y and of every level's z (by Level::ALL's order) in the squared error of
/// a plan with these fused levels (top first) on a problem of inner dimension k
pub fn err_row(levels: &[Level], k: usize) -> (f64, f64, [f64; 10]) {
    let (mut kl, mut a2, mut nn) = (k as f64, 1.0f64, 1.0f64);
    let mut cz = [0.0f64; 10];
    for &lv in levels {
        let (amp, nu) = err_consts(lv);
        cz[Level::ALL.iter().position(|l| *l == lv).unwrap()] += a2;
        a2 *= amp * amp;
        kl /= lv.grid().1 as f64;
        nn *= nu;
    }
    (kl * a2, kl * a2 / (nn.sqrt() * nn.sqrt().sqrt()), cz)
}

impl ErrModel {
    /// a plan's predicted squared error
    pub fn err2(&self, levels: &[Level], k: usize) -> f64 {
        if levels.is_empty() {
            return self.eg2 * k as f64;
        }
        let (cx, cy, cz) = err_row(levels, k);
        let mut q = self.x * cx + self.y * cy;
        for i in 0..10 {
            q += self.z[i] * cz[i];
        }
        q
    }
}

impl Calib {
    pub fn err_model(&self) -> Option<ErrModel> {
        const NP: usize = 7;
        let mut v = [0.0f64; NERR];
        for (i, x) in v.iter_mut().enumerate() {
            *x = self.get(Kind::Err(i as u8), Shape::sq(N_E))?;
            if *x <= 0.0 {
                return None;
            }
        }
        let eg2 = v[0] * v[0] / N_E as f64;
        let zi = |lv: Level| Level::ALL.iter().position(|l| *l == lv).unwrap();
        // rows scaled by the measured squared errors, so that every plan counts by its relative error
        let mut row = [[0.0f64; NP]; NERR];
        for i in 1..NERR {
            let (cx, cy, cz) = err_row(&err_levels(i), N_E);
            let w = 1.0 / (v[i] * v[i]);
            row[i][0] = cx * w;
            row[i][1] = cy * w;
            for j in 0..5 {
                row[i][2 + j] = cz[zi(ERR_LV[j])] * w;
            }
        }
        let mut on = [true; NP];
        let mut p = [0.0f64; NP];
        loop {
            // the normal equations over the unknowns still in, by Gaussian elimination with partial pivoting
            let idx: Vec<usize> = (0..NP).filter(|&a| on[a]).collect();
            let n = idx.len();
            let mut m = [[0.0f64; NP + 1]; NP];
            for a in 0..n {
                for i in 1..NERR {
                    for b in 0..n {
                        m[a][b] += row[i][idx[a]] * row[i][idx[b]];
                    }
                    m[a][n] += row[i][idx[a]];
                }
            }
            for a in 0..n {
                let mut piv = a;
                for r in a + 1..n {
                    if m[r][a].abs() > m[piv][a].abs() {
                        piv = r;
                    }
                }
                if m[piv][a] == 0.0 {
                    return None;
                }
                m.swap(a, piv);
                for r in a + 1..n {
                    let f = m[r][a] / m[a][a];
                    for b in a..=n {
                        m[r][b] -= f * m[a][b];
                    }
                }
            }
            for a in (0..n).rev() {
                let mut t = m[a][n];
                for b in a + 1..n {
                    t -= m[a][b] * p[idx[b]];
                }
                p[idx[a]] = t / m[a][a];
            }
            let mut neg = false;
            for &a in &idx {
                if p[a] < 0.0 {
                    on[a] = false;
                    neg = true;
                }
            }
            if !neg {
                break;
            }
        }
        for a in 0..NP {
            if !on[a] {
                p[a] = 0.0;
            }
        }
        let mut z = [0.0f64; 10];
        for j in 0..5 {
            z[zi(ERR_LV[j])] = p[2 + j];
        }
        if p[0] + p[1] > 0.0 { Some(ErrModel { eg2, x: p[0], y: p[1], z }) } else { None }
    }

    /// the fitted model in units of the precision's unit roundoff u, as the C library prints it
    pub fn print_err_model(&self, u: f64) {
        if let Some(e) = self.err_model() {
            let zi = |lv: Level| Level::ALL.iter().position(|l| *l == lv).unwrap();
            println!("# error model: GEMM {:.3} u sqrt(k); leaf {:.3} u sqrt(k_leaf), tail excess {:.2}; the levels' own rounding (u): SW {:.1}, D48 {:.1}, R336 {:.1}, R363 {:.1}, R633 {:.1}",
                     e.eg2.sqrt() / u, e.x.sqrt() / u, if e.x > 0.0 { e.y / e.x } else { 0.0 }, e.z[zi(Level::Sw)].sqrt() / u,
                     e.z[zi(Level::D48)].sqrt() / u, e.z[zi(Level::R336)].sqrt() / u, e.z[zi(Level::R363)].sqrt() / u,
                     e.z[zi(Level::R633)].sqrt() / u);
        }
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
        let need = need(Shape::sq(13824), true);
        assert!(need.len() > 400, "{}", need.len());
        for (k, _) in need {
            assert_eq!(Kind::parse(&k.name()), Some(k), "{}", k.name());
        }
        for s in ["G", "B2", "SW", "D48", "R336", "GSW", "G6D48", "G3R363", "PD48k6p2s", "PSWk3p4o", "PR633k6p4s", "XG", "XSW", "XD48/D48", "XR633/R336",
                  "GMR363", "G6MD48", "GMK32", "G6MK16", "PR363k6p4Ms", "PSWk6p3Mo", "K32"] {
            assert_eq!(Kind::parse(s).map(|k| k.name()), Some(s.to_string()));
        }
        for (s, gpu) in [("GMR363", true), ("PR363k6p4Ms", true), ("K64", true), ("PR363k6p4s", false), ("G6R363", false), ("R363", false)] {
            assert_eq!(Kind::parse(s).unwrap().is_gpu(), gpu, "{s}");
        }
        for s in ["", "X", "GG", "G6", "PD48k6p2", "PD48k6p2x", "E", "ESW", "XSW/K16", "R36", "GM", "G6M", "GMG", "PD48k6pMs"] {
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
        let n = need(Shape::sq(6912), false);
        assert!(n.contains(&(Kind::Passes(Level::R336), Shape::new(2304, 2304, 1152))));
        assert!(n.contains(&(Kind::Gin(Level::R363, 6), Shape::new(2304, 1152, 2304))));
        assert!(n.contains(&(Kind::Pipe { level: Level::D48, streams: 3, passes: 2, over: false, gpu: false }, Shape::new(576, 576, 288))));
        assert!(n.contains(&(Kind::Err(30), Shape::sq(N_E))));
        assert_eq!(Kind::parse("XR363/R336").map(|k| k.name()), Some("XR363/R336".to_string()));
        assert!(!n.iter().any(|(k, _)| k.is_gpu()));
        let g = need(Shape::sq(6912), true);
        assert!(g.contains(&(Kind::Ggpu(Level::R363, 6), Shape::new(2304, 1152, 2304))));
        assert!(g.contains(&(Kind::Passes(Level::K32), Shape::new(216, 6912, 6912))));
        assert!(g.contains(&(Kind::Ggpu(Level::K64, 0), Shape::new(108, 6912, 6912))));
        let h = need(Shape::sq(13824), true);
        assert!(h.contains(&(Kind::Pipe { level: Level::R363, streams: 6, passes: 4, over: true, gpu: true }, Shape::new(1536, 768, 768))));
        assert!(!g.contains(&(Kind::Ggpu(Level::D48, 6), Shape::new(432, 432, 432))));     // under GPU_MINB
        let r = need(Shape::new(3456, 3456, 1728), false);
        assert!(r.contains(&(Kind::Leaf(Level::G), Shape::new(3456, 3456, 1728))));
        assert!(!r.iter().any(|(k, _)| matches!(k, Kind::Err(_))));
    }
}
