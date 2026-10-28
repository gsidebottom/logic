//! The planner: a fused level costs its passes plus r times its sub-plan on its products' shape, a
//! GEMM leaf its time inside the level above it (or alone, on top), a pipelined level its passes
//! plus r times the steady time per sub-problem plus fill and drain; dynamic programming picks the
//! cheapest plan, optionally within an error-growth budget, and pads the shape to one the plan
//! divides when that pays.  The same rules as the C library's, so both pick the same plans from
//! one cache.

use crate::calib::{Calib, ErrModel, Kind, PIPE_K, PIPE_P, STREAMS};
use crate::plan::{minb, Entry, Level, Plan, Shape};

/// predicted seconds for a plan on shape s below a fused level of type parent (None: the top)
pub fn cost_in(c: &Calib, plan: &[Entry], s: Shape, parent: Option<Level>) -> Option<f64> {
    let e = *plan.first()?;
    match e.level {
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
            if e.pipe.is_some() {
                // its passes, then a pipeline of r sub-problems Y over Gk
                let (ly, lf) = (plan.get(1)?.level, *plan.get(2)?);
                if ly.is_leaf() || lf.level != Level::G || lf.streams == 0 || !ly.divides(m) {
                    return None;
                }
                let my = ly.sub(m);
                let pw = e.pass_threads() as u8;
                let st = c.cost(Kind::Pipe { level: ly, streams: lf.streams, passes: pw, over: false }, my)?;
                // sub-problems under 1 ms are not pipelined: tens of microseconds of dispatch per
                // step and a noisy calibration (2048 f64 mispredicted by 12%)
                if st < 1e-3 {
                    return None;
                }
                let ov = c.cost(Kind::Pipe { level: ly, streams: lf.streams, passes: pw, over: true }, my)?;
                return Some(c.cost(Kind::Passes(lv), m)? + lv.rank() as f64 * st + ov);
            }
            Some(c.cost(Kind::Passes(lv), m)? + lv.rank() as f64 * cost_in(c, &plan[1..], m, Some(lv))?)
        }
    }
}

pub fn cost(c: &Calib, plan: &Plan, s: Shape) -> Option<f64> {
    cost_in(c, &plan.0, s, None)
}

/// the first entries a plan below parent (None: the top) can start with
fn firsts(parent: Option<Level>) -> Vec<Entry> {
    let mut v: Vec<Entry> = STREAMS.iter().filter(|&&k| parent.is_some() || k == 0).map(|&k| Entry::gemm(k)).collect();
    if parent.is_none() {
        v.push(Entry::new(Level::B2));
    }
    v.extend(Level::FUSED.into_iter().map(Entry::new));
    v
}

/// the cheapest plan for shape s below parent: dynamic programming over the first entry, a leaf or
/// a fused level over the cheapest plan for its products below it, and the pipelined levels
/// X+p/Y/Gk
fn best_in(c: &Calib, s: Shape, parent: Option<Level>) -> Option<(Vec<Entry>, f64)> {
    let mut best: Option<(Vec<Entry>, f64)> = None;
    let mut consider = |p: Vec<Entry>, t: f64| {
        if best.as_ref().is_none_or(|b| t < b.1) {
            best = Some((p, t));
        }
    };
    for e in firsts(parent) {
        if e.level.is_leaf() {
            if let Some(t) = cost_in(c, &[e], s, parent) {
                consider(vec![e], t);
            }
        } else {
            if !e.level.divides(s) || e.level.sub(s).min_dim() < minb() {
                continue;
            }
            let m = e.level.sub(s);
            if let (Some((sub, below)), Some(p)) = (best_in(c, m, Some(e.level)), c.cost(Kind::Passes(e.level), m)) {
                let mut v = vec![e];
                v.extend(sub);
                consider(v, p + e.level.rank() as f64 * below);
            }
        }
    }
    for lx in Level::FUSED {
        for ly in Level::FUSED {
            for k in PIPE_K {
                for p in PIPE_P {
                    let v = vec![Entry { level: lx, streams: 0, pipe: Some(p) }, Entry::new(ly), Entry::gemm(k)];
                    if let Some(t) = cost_in(c, &v, s, parent) {
                        consider(v, t);
                    }
                }
            }
        }
    }
    best
}

pub fn best(c: &Calib, s: Shape) -> Option<(Plan, f64)> {
    best_in(c, s, None).map(|(v, t)| (Plan(v), t))
}

/// every plan for shape s down to blocks of minb() with its predicted time, cheapest first
pub fn enumerate(c: &Calib, s: Shape) -> Vec<(Plan, f64)> {
    fn rec(c: &Calib, s0: Shape, s: Shape, plan: &mut Vec<Entry>, out: &mut Vec<(Plan, f64)>) {
        let parent = plan.last().map(|e| e.level);
        for e in firsts(parent) {
            plan.push(e);
            if e.level.is_leaf() {
                if let Some(t) = cost(c, &Plan(plan.clone()), s0) {
                    out.push((Plan(plan.clone()), t));
                }
                // the same with the level two above the leaf pipelined
                let d = plan.len();
                if d >= 3 && e.streams > 0 && !plan[d - 2].level.is_leaf() && !plan[d - 3].level.is_leaf() {
                    for p in PIPE_P {
                        let keep = plan[d - 3];
                        plan[d - 3].pipe = Some(p);
                        if let Some(t) = cost(c, &Plan(plan.clone()), s0) {
                            out.push((Plan(plan.clone()), t));
                        }
                        plan[d - 3] = keep;
                    }
                }
            } else if e.level.divides(s) && e.level.sub(s).min_dim() >= minb() {
                rec(c, s0, e.level.sub(s), plan, out);
            }
            plan.pop();
        }
    }
    let mut out = vec![];
    rec(c, s, s, &mut vec![], &mut out);
    out.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap());
    out
}

/// the factor by which a plan's error exceeds the classical GEMM's
pub fn growth(e: &ErrModel, plan: &Plan) -> f64 {
    plan.0.iter().take_while(|x| !x.level.is_leaf()).map(|x| e.factor(x.level)).product()
}

/// the predicted error of a plan on shape s: the classical scale grows with the inner dimension
pub fn predicted_error(e: &ErrModel, plan: &Plan, s: Shape) -> f64 {
    e.base * (s.k as f64 / crate::calib::N_E as f64).sqrt() * growth(e, plan)
}

/// the cheapest plan whose error growth is at most gmax (0: no limit)
pub fn best_budget(c: &Calib, s: Shape, gmax: f64) -> Option<(Plan, f64)> {
    if gmax <= 0.0 {
        return best(c, s);
    }
    let e = c.err_model()?;
    enumerate(c, s).into_iter().find(|(p, _)| growth(&e, p) <= gmax * (1.0 + 1e-9))
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
        if let Some((p, t)) = best_budget(c, sp, gmax) {
            let t = t + pad_cost(s, sp, f64);
            if best.as_ref().is_none_or(|b| t < b.2) {
                best = Some((p, sp, t));
            }
        }
    }
    best
}
