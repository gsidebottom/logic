//! The planner: a fused level costs its passes plus r times its sub-plan at n/g, a GEMM leaf its
//! time inside the level above it (or alone, on top), a pipelined level its passes plus r times
//! the steady time per sub-problem plus fill and drain; dynamic programming picks the cheapest
//! plan, optionally within an error-growth budget, and pads n to a size the plan divides when
//! that pays.  The same rules as the C library's, so both pick the same plans from one cache.

use crate::calib::{Calib, ErrModel, Kind, PIPE_K, PIPE_P, STREAMS};
use crate::plan::{minb, Entry, Level, Plan};

/// predicted seconds for a plan at size n below a fused level of type parent (None: the top)
pub fn cost_in(c: &Calib, plan: &[Entry], n: usize, parent: Option<Level>) -> Option<f64> {
    let e = *plan.first()?;
    match e.level {
        Level::G => match parent {
            None if e.streams == 0 => c.cost(Kind::Leaf(Level::G), n),
            None => None,
            Some(p) => c.cost(Kind::Gin(p, e.streams), n),
        },
        Level::B2 => if parent.is_none() { c.cost(Kind::Leaf(Level::B2), n) } else { None },
        lv => {
            let g = lv.grid();
            if n % g != 0 {
                return None;
            }
            let m = n / g;
            if e.pipe.is_some() {
                // its passes, then a pipeline of r sub-problems Y over Gk
                let (ly, lf) = (plan.get(1)?.level, *plan.get(2)?);
                if ly.is_leaf() || lf.level != Level::G || lf.streams == 0 || m % ly.grid() != 0 {
                    return None;
                }
                let my = m / ly.grid();
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

pub fn cost(c: &Calib, plan: &Plan, n: usize) -> Option<f64> {
    cost_in(c, &plan.0, n, None)
}

/// the first entries a plan below parent (None: the top) can start with
fn firsts(parent: Option<Level>) -> Vec<Entry> {
    let mut v: Vec<Entry> = STREAMS.iter().filter(|&&k| parent.is_some() || k == 0).map(|&k| Entry::gemm(k)).collect();
    if parent.is_none() {
        v.push(Entry::new(Level::B2));
    }
    v.push(Entry::new(Level::Sw));
    v.push(Entry::new(Level::D48));
    v
}

/// the cheapest plan for n below parent: dynamic programming over the first entry, a leaf or a
/// fused level over the cheapest plan for n/g below it, and the pipelined levels X+p/Y/Gk
fn best_in(c: &Calib, n: usize, parent: Option<Level>) -> Option<(Vec<Entry>, f64)> {
    let mut best: Option<(Vec<Entry>, f64)> = None;
    let mut consider = |p: Vec<Entry>, t: f64| {
        if best.as_ref().is_none_or(|b| t < b.1) {
            best = Some((p, t));
        }
    };
    for e in firsts(parent) {
        if e.level.is_leaf() {
            if let Some(t) = cost_in(c, &[e], n, parent) {
                consider(vec![e], t);
            }
        } else {
            let g = e.level.grid();
            if n % g != 0 || n / g < minb() {
                continue;
            }
            if let (Some((sub, below)), Some(p)) = (best_in(c, n / g, Some(e.level)), c.cost(Kind::Passes(e.level), n / g)) {
                let mut v = vec![e];
                v.extend(sub);
                consider(v, p + e.level.rank() as f64 * below);
            }
        }
    }
    for lx in [Level::Sw, Level::D48] {
        for ly in [Level::Sw, Level::D48] {
            for k in PIPE_K {
                for p in PIPE_P {
                    let v = vec![Entry { level: lx, streams: 0, pipe: Some(p) }, Entry::new(ly), Entry::gemm(k)];
                    if let Some(t) = cost_in(c, &v, n, parent) {
                        consider(v, t);
                    }
                }
            }
        }
    }
    best
}

pub fn best(c: &Calib, n: usize) -> Option<(Plan, f64)> {
    best_in(c, n, None).map(|(v, t)| (Plan(v), t))
}

/// every plan for n down to blocks of minb() with its predicted time, cheapest first
pub fn enumerate(c: &Calib, n: usize) -> Vec<(Plan, f64)> {
    fn rec(c: &Calib, n0: usize, n: usize, plan: &mut Vec<Entry>, out: &mut Vec<(Plan, f64)>) {
        let parent = plan.last().map(|e| e.level);
        for e in firsts(parent) {
            plan.push(e);
            if e.level.is_leaf() {
                if let Some(t) = cost(c, &Plan(plan.clone()), n0) {
                    out.push((Plan(plan.clone()), t));
                }
                // the same with the level two above the leaf pipelined
                let d = plan.len();
                if d >= 3 && e.streams > 0 && !plan[d - 2].level.is_leaf() && !plan[d - 3].level.is_leaf() {
                    for p in PIPE_P {
                        let keep = plan[d - 3];
                        plan[d - 3].pipe = Some(p);
                        if let Some(t) = cost(c, &Plan(plan.clone()), n0) {
                            out.push((Plan(plan.clone()), t));
                        }
                        plan[d - 3] = keep;
                    }
                }
            } else if n % e.level.grid() == 0 && n / e.level.grid() >= minb() {
                rec(c, n0, n / e.level.grid(), plan, out);
            }
            plan.pop();
        }
    }
    let mut out = vec![];
    rec(c, n, n, &mut vec![], &mut out);
    out.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap());
    out
}

/// the factor by which a plan's error exceeds the classical GEMM's
pub fn growth(e: &ErrModel, plan: &Plan) -> f64 {
    plan.0.iter().take_while(|x| !x.level.is_leaf()).map(|x| if x.level == Level::Sw { e.f_sw } else { e.f_d48 }).product()
}

pub fn predicted_error(e: &ErrModel, plan: &Plan, n: usize) -> f64 {
    e.base * (n as f64 / crate::calib::N_E as f64).sqrt() * growth(e, plan)
}

/// the cheapest plan whose error growth is at most gmax (0: no limit)
pub fn best_budget(c: &Calib, n: usize, gmax: f64) -> Option<(Plan, f64)> {
    if gmax <= 0.0 {
        return best(c, n);
    }
    let e = c.err_model()?;
    enumerate(c, n).into_iter().find(|(p, _)| growth(&e, p) <= gmax * (1.0 + 1e-9))
}

/// bytes per second of the padding copies
const PAD_BW: f64 = 80e9;

pub fn pad_cost(n: usize, npad: usize, f64: bool) -> f64 {
    if npad == n { 0.0 } else { 6.0 * (npad * npad) as f64 * if f64 { 8.0 } else { 4.0 } / PAD_BW }
}

/// the cheapest plan for n over the padded sizes N >= n (n rounded up to a multiple of 8 * 2^j,
/// j = 0..7), the padding priced; returns (plan, N, predicted seconds)
pub fn best_padded(c: &Calib, n: usize, gmax: f64, f64: bool) -> Option<(Plan, usize, f64)> {
    let mut best: Option<(Plan, usize, f64)> = None;
    let mut tried = vec![];
    for j in -1i32..8 {
        let npad = if j < 0 { n } else { let a = 8usize << j; n.div_ceil(a) * a };
        if tried.contains(&npad) {
            continue;
        }
        tried.push(npad);
        if let Some((p, t)) = best_budget(c, npad, gmax) {
            let t = t + pad_cost(n, npad, f64);
            if best.as_ref().is_none_or(|b| t < b.2) {
                best = Some((p, npad, t));
            }
        }
    }
    best
}
