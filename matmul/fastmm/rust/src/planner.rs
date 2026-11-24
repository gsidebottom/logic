//! The planner: a fused level costs its passes plus r times its sub-plan on its products' shape, a
//! GEMM leaf its time inside the level above it (or alone, on top), a pipelined level its passes
//! plus r times the steady time per sub-problem plus fill and drain; dynamic programming picks the
//! cheapest plan, optionally within an error-growth budget, and pads the shape to one the plan
//! divides when that pays.  With the GPU (Calib::gpu) also the shared leaves GM and G6M, pipelines
//! over G6M and the K levels on top.  The same rules as the C library's, so both pick the same
//! plans from one cache.

use crate::calib::{Calib, ErrModel, Kind, GPIPE_K, GPIPE_P, GSTREAMS, PIPE_K, PIPE_P, STREAMS};
use crate::plan::{minb, Entry, Level, Plan, Shape, GPU_MINB, K_MINROWS};

/// the calibration as the planner sees it: with or without the GPU, and with or without the K
/// levels (nok: the caller's matrices cannot be wrapped for the GPU)
#[derive(Clone, Copy)]
pub struct View<'a> {
    pub c: &'a Calib,
    pub gpu: bool,
    pub nok: bool,
}

impl<'a> View<'a> {
    pub fn of(c: &'a Calib) -> View<'a> {
        View { c, gpu: c.gpu, nok: false }
    }
}

/// predicted seconds for a plan on shape s below a fused level of type parent (None: the top)
pub fn cost_in(v: View, plan: &[Entry], s: Shape, parent: Option<Level>) -> Option<f64> {
    let c = v.c;
    let e = *plan.first()?;
    match e.level {
        Level::G if e.gpu => match parent {
            Some(p) if v.gpu && (p.is_split() || s.min_dim() >= GPU_MINB) => c.cost(Kind::Ggpu(p, e.streams), s),
            _ => None,
        },
        Level::G => match parent {
            None if e.streams == 0 => c.cost(Kind::Leaf(Level::G), s),
            None => None,
            Some(p) => c.cost(Kind::Gin(p, e.streams), s),
        },
        Level::B2 => if parent.is_none() && s.is_sq() { c.cost(Kind::Leaf(Level::B2), s) } else { None },
        lv => {
            if !lv.divides(s) {
                return None;
            }
            let m = lv.sub(s);
            if lv.is_split() {
                // on top, with the GPU, its strips shared by the leaf below; no passes
                let next = *plan.get(1)?;
                if parent.is_some() || !v.gpu || v.nok || e.pipe.is_some() || next.level != Level::G || !next.gpu {
                    return None;
                }
                return Some(lv.rank() as f64 * cost_in(v, &plan[1..], m, Some(lv))?);
            }
            if e.pipe.is_some() {
                // its passes, then a pipeline of r sub-problems Y over Gk (or GkM)
                let (ly, lf) = (plan.get(1)?.level, *plan.get(2)?);
                if ly.is_leaf() || ly.is_split() || lf.level != Level::G || lf.streams == 0 || !ly.divides(m) {
                    return None;
                }
                let my = ly.sub(m);
                if lf.gpu && (!v.gpu || my.min_dim() < GPU_MINB) {
                    return None;
                }
                let pw = e.pass_threads() as u8;
                let pipe = |over| Kind::Pipe { level: ly, streams: lf.streams, passes: pw, over, gpu: lf.gpu };
                let st = c.cost(pipe(false), my)?;
                // sub-problems under 1 ms are not pipelined: tens of microseconds of dispatch per
                // step and a noisy calibration (2048 f64 mispredicted by 12%)
                if st < 1e-3 {
                    return None;
                }
                let ov = c.cost(pipe(true), my)?;
                return Some(c.cost(Kind::Passes(lv), m)? + lv.rank() as f64 * st + ov);
            }
            Some(c.cost(Kind::Passes(lv), m)? + lv.rank() as f64 * cost_in(v, &plan[1..], m, Some(lv))?)
        }
    }
}

pub fn cost(c: &Calib, plan: &Plan, s: Shape) -> Option<f64> {
    cost_in(View::of(c), &plan.0, s, None)
}

/// the first entries a plan below parent (None: the top) can start with, in the C library's order
fn firsts(v: View, parent: Option<Level>) -> Vec<Entry> {
    if parent.is_some_and(Level::is_split) {
        return GSTREAMS.iter().map(|&k| Entry::gemm_gpu(k)).collect();     // below a K level: the GPU's leaves
    }
    let mut out: Vec<Entry> = STREAMS.iter().filter(|&&k| parent.is_some() || k == 0).map(|&k| Entry::gemm(k)).collect();
    if v.gpu && parent.is_some() {
        out.extend(GSTREAMS.iter().map(|&k| Entry::gemm_gpu(k)));
    }
    if parent.is_none() {
        out.push(Entry::new(Level::B2));
    }
    out.extend(Level::FUSED.into_iter().map(Entry::new));
    if v.gpu && !v.nok && parent.is_none() {
        out.extend(Level::SPLIT.into_iter().map(Entry::new));
    }
    out
}

/// the cheapest plan for shape s below parent: dynamic programming over the first entry, a leaf, a
/// K level or a fused level over the cheapest plan for its products below it, and the pipelined
/// levels X+p/Y/Gk (and X+p/Y/G6M with the GPU)
fn best_in(v: View, s: Shape, parent: Option<Level>) -> Option<(Vec<Entry>, f64)> {
    let mut best: Option<(Vec<Entry>, f64)> = None;
    let mut consider = |p: Vec<Entry>, t: f64| {
        if best.as_ref().is_none_or(|b| t < b.1) {
            best = Some((p, t));
        }
    };
    for e in firsts(v, parent) {
        if e.level.is_leaf() {
            if let Some(t) = cost_in(v, &[e], s, parent) {
                consider(vec![e], t);
            }
        } else if e.level.is_split() {
            if !e.level.divides(s) || e.level.sub(s).m < K_MINROWS {
                continue;
            }
            if let Some((sub, below)) = best_in(v, e.level.sub(s), Some(e.level)) {
                let mut p = vec![e];
                p.extend(sub);
                consider(p, e.level.rank() as f64 * below);
            }
        } else {
            if !e.level.divides(s) || e.level.sub(s).min_dim() < minb() {
                continue;
            }
            let m = e.level.sub(s);
            if let (Some((sub, below)), Some(p)) = (best_in(v, m, Some(e.level)), v.c.cost(Kind::Passes(e.level), m)) {
                let mut pl = vec![e];
                pl.extend(sub);
                consider(pl, p + e.level.rank() as f64 * below);
            }
        }
    }
    if parent.is_some_and(Level::is_split) {
        return best;
    }
    for lx in Level::FUSED {
        for ly in Level::FUSED {
            for k in PIPE_K {
                for p in PIPE_P {
                    let pl = vec![Entry { pipe: Some(p), ..Entry::new(lx) }, Entry::new(ly), Entry::gemm(k)];
                    if let Some(t) = cost_in(v, &pl, s, parent) {
                        consider(pl, t);
                    }
                }
            }
            if v.gpu {
                for p in GPIPE_P {
                    let pl = vec![Entry { pipe: Some(p), ..Entry::new(lx) }, Entry::new(ly), Entry::gemm_gpu(GPIPE_K)];
                    if let Some(t) = cost_in(v, &pl, s, parent) {
                        consider(pl, t);
                    }
                }
            }
        }
    }
    best
}

pub fn best(c: &Calib, s: Shape) -> Option<(Plan, f64)> {
    best_with(View::of(c), s)
}

pub fn best_with(v: View, s: Shape) -> Option<(Plan, f64)> {
    best_in(v, s, None).map(|(p, t)| (Plan(p), t))
}

/// every plan for shape s down to blocks of minb() with its predicted time, cheapest first
pub fn enumerate(c: &Calib, s: Shape) -> Vec<(Plan, f64)> {
    enumerate_with(View::of(c), s)
}

pub fn enumerate_with(v: View, s: Shape) -> Vec<(Plan, f64)> {
    fn rec(v: View, s0: Shape, s: Shape, plan: &mut Vec<Entry>, out: &mut Vec<(Plan, f64)>) {
        let parent = plan.last().map(|e| e.level);
        for e in firsts(v, parent) {
            plan.push(e);
            if e.level.is_leaf() {
                if let Some(t) = cost_in(v, plan, s0, None) {
                    out.push((Plan(plan.clone()), t));
                }
                // the same with the level two above the leaf pipelined
                let d = plan.len();
                if d >= 3 && e.streams > 0 && !plan[d - 2].level.is_leaf() && !plan[d - 3].level.is_leaf() {
                    for p in PIPE_P {
                        let keep = plan[d - 3];
                        plan[d - 3].pipe = Some(p);
                        if let Some(t) = cost_in(v, plan, s0, None) {
                            out.push((Plan(plan.clone()), t));
                        }
                        plan[d - 3] = keep;
                    }
                }
            } else if if e.level.is_split() {
                e.level.divides(s) && e.level.sub(s).m >= K_MINROWS
            } else {
                e.level.divides(s) && e.level.sub(s).min_dim() >= minb()
            } {
                rec(v, s0, e.level.sub(s), plan, out);
            }
            plan.pop();
        }
    }
    let mut out = vec![];
    rec(v, s, s, &mut vec![], &mut out);
    out.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap());
    out
}

/// the factor by which a plan's error exceeds the classical GEMM's: the levels' factors, times
/// the depth factor once per fused level after the first (a K level's strips are the GEMM's own sums)
pub fn growth(e: &ErrModel, plan: &Plan) -> f64 {
    let levels: Vec<Level> =
        plan.0.iter().take_while(|x| !x.level.is_leaf()).map(|x| x.level).filter(|l| !l.is_split()).collect();
    let g: f64 = levels.iter().map(|lv| e.factor(*lv)).product();
    g * e.rho.powi((levels.len() as i32 - 1).max(0))
}

/// the predicted error of a plan on shape s: the classical scale grows with the inner dimension
pub fn predicted_error(e: &ErrModel, plan: &Plan, s: Shape) -> f64 {
    e.base * (s.k as f64 / crate::calib::N_E as f64).sqrt() * growth(e, plan)
}

/// the budget a call's max_growth = 0 means: no less accurate than the GEMM
pub const DEFAULT_GROWTH: f64 = 1.0;

/// plans predicted within 3% of the fastest are ties (2% until 2026-11-23, as in the C library) ...
pub const PLAN_TIE: f64 = 0.03;
/// ... which a plan predicted at least 25% more accurate wins (the error model is good to about
/// 25%; smaller predicted gains picked the less accurate plan at 6912 in both precisions)
pub const PLAN_TIE_GAIN: f64 = 0.25;
/// the window with the GPU, whose plans repeat to 10-20% only
pub const PLAN_TIE_GPU: f64 = 0.08;

/// a call's max_growth: a positive value is that budget, 0 the default, a negative value no
/// budget (the fastest plan whatever its error)
pub fn resolve_growth(g: f64) -> f64 {
    if g == 0.0 { DEFAULT_GROWTH } else { g }
}

/// the cheapest plan with growth at most gmax, or with tie: faster first, more accurate second --
/// of the admissible plans predicted within the tie window of the fastest (the predictions are
/// good to about that), one whose predicted error is at least PLAN_TIE_GAIN lower than the
/// fastest's (smaller differences are below what the error model resolves), the most accurate of
/// those, the fastest among equals
fn pick(v: View, e: &ErrModel, s: Shape, gmax: f64, tie: bool) -> Option<(Plan, f64)> {
    let all = enumerate_with(v, s);
    let i = all.iter().position(|(p, _)| growth(e, p) <= gmax * (1.0 + 1e-9))?;
    let window = if v.gpu { PLAN_TIE_GPU } else { PLAN_TIE };
    let mut pick = i;
    let mut gbest = growth(e, &all[i].0) * (1.0 - PLAN_TIE_GAIN);
    for j in i + 1..all.len() {
        if !tie || all[j].1 > all[i].1 * (1.0 + window) {
            break;
        }
        let g = growth(e, &all[j].0);
        if g < gbest * (1.0 - 1e-9) {
            gbest = g;
            pick = j;
        }
    }
    Some(all[pick].clone())
}

/// the plan for a budget (see pick), else (a budget below 1 that no plan meets) the classical
/// GEMM; None if nothing is calibrated
pub fn best_budget(c: &Calib, s: Shape, gmax: f64) -> Option<(Plan, f64)> {
    best_budget_with(View::of(c), s, gmax)
}

pub fn best_budget_with(v: View, s: Shape, gmax: f64) -> Option<(Plan, f64)> {
    let mut gmax = resolve_growth(gmax);
    if gmax < 0.0 {
        return best_with(v, s);
    }
    let e = v.c.err_model()?;
    if v.gpu {
        // the GPU must not cost accuracy: its plans are held to the predicted error of the fastest
        // plan the same budget admits without it (this keeps the classical product in strips, as
        // accurate as the GEMM and no more, from replacing a more accurate level it merely ties)
        if let Some((p0, _)) = pick(View { gpu: false, ..v }, &e, s, gmax, false) {
            gmax = gmax.min(growth(&e, &p0));
        }
    }
    if let Some(p) = pick(v, &e, s, gmax, true) {
        return Some(p);
    }
    let p = Plan::classical();
    let t = cost_in(v, &p.0, s, None)?;
    Some((p, t))
}

/// bytes per second of the padding copies
const PAD_BW: f64 = 80e9;

/// the padding copies' cost: twice the padded matrices' elements of traffic
pub fn pad_cost(s: Shape, sp: Shape, f64: bool) -> f64 {
    if sp == s {
        0.0
    } else {
        let words = (sp.m * sp.k + sp.k * sp.n + sp.m * sp.n) as f64;
        2.0 * words * if f64 { 8.0 } else { 4.0 } / PAD_BW
    }
}

/// the cheapest plan for shape s over the padded shapes (every dimension rounded up to the same
/// multiple of 2^a 3^b, a <= 10, b <= 3: what plans of 2x2 and 4x4 levels and of the 3x3x6 family
/// divide), the padding priced; returns (plan, padded shape, predicted seconds)
pub fn best_padded(c: &Calib, s: Shape, gmax: f64, f64: bool) -> Option<(Plan, Shape, f64)> {
    best_padded_with(View::of(c), s, gmax, f64)
}

pub fn best_padded_with(v: View, s: Shape, gmax: f64, f64: bool) -> Option<(Plan, Shape, f64)> {
    let mut best: Option<(Plan, Shape, f64)> = None;
    let mut tried = vec![];
    for j in -1i32..44 {
        let sp = if j < 0 {
            s
        } else {
            let d = 2usize.pow((j % 11) as u32) * 3usize.pow((j / 11) as u32);
            Shape::new(s.m.div_ceil(d) * d, s.k.div_ceil(d) * d, s.n.div_ceil(d) * d)
        };
        if tried.contains(&sp) {
            continue;
        }
        tried.push(sp);
        if let Some((p, t)) = best_budget_with(v, sp, gmax) {
            let t = t + pad_cost(s, sp, f64);
            if best.as_ref().is_none_or(|b| t < b.2) {
                best = Some((p, sp, t));
            }
        }
    }
    best
}
