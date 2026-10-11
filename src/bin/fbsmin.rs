//! fbsmin: SIGNED free-basis addition minimization for one leg of a
//! bilinear scheme — the ring-valid (any field / non-commutative ring)
//! counterpart of `fbmin`'s F₂ search, deciding the Karstadt–Schwartz
//! per-step addition count over ℤ directly instead of lifting F₂
//! certificates.
//!
//! Input: a `.slegs` file, one signed row per line (9 space-separated
//! integers; 23 lines).  In FREE mode a target counts as produced when
//! the chain reaches it up to global sign (negation is free in the ±
//! model), and the result reports the realized sign per row for the
//! cross-leg ε bookkeeping.  In `--exact` mode targets must be hit with
//! the given signs exactly (used for the C leg after the per-product
//! balance ε_u·ε_v·ε_w = +1 is folded into the targets).
//!
//! Search space, mirroring fbmin's exact tier ladder restricted to
//! 9-TARGET bases (the free-non-target-vector tiers are unbounded over
//! ℤ and are OUT OF SCOPE — a "no" here means: no chain whose 9 free
//! forms are all target rows, with ≤2 non-target helper additions;
//! every "yes" is a complete ring-valid certificate):
//!   tier1  a = d−9: waste-free closure over ± sums (monotone, hence
//!          greedy-complete, same argument as mod 2);
//!   tier2  a = d−8: one helper, injected at the closure fixpoint
//!          (everything preceding the helper lies in the pure closure);
//!   tier3  a = d−7: two helpers at successive fixpoints.
//! d = number of distinct rows up to sign.  Basis subsets must be
//! unimodular (|det| = 1 over ℤ); per-row global signs do not change
//! |det|, so one determinant per subset suffices.
//!
//! Certificates are replayed by an independent checker before printing.

use rayon::prelude::*;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Mutex;

type V9 = [i32; 9];

fn canon(mut v: V9) -> (V9, i32) {
    for x in v {
        if x != 0 {
            if x < 0 {
                for e in v.iter_mut() {
                    *e = -*e;
                }
                return (v, -1);
            }
            return (v, 1);
        }
    }
    (v, 1)
}

fn vadd(x: &V9, y: &V9, s: i32) -> V9 {
    let mut out = [0i32; 9];
    for i in 0..9 {
        out[i] = x[i] + s * y[i];
    }
    out
}

fn is_zero(v: &V9) -> bool {
    v.iter().all(|&x| x == 0)
}

/// |det| of 9 rows over ℤ via fraction-free (Bareiss) elimination.
fn abs_det(rows: &[V9]) -> i128 {
    let mut a = [[0i128; 9]; 9];
    for (i, r) in rows.iter().enumerate() {
        for j in 0..9 {
            a[i][j] = r[j] as i128;
        }
    }
    let mut prev = 1i128;
    for k in 0..9 {
        if a[k][k] == 0 {
            if let Some(p) = (k + 1..9).find(|&p| a[p][k] != 0) {
                a.swap(k, p);
            } else {
                return 0;
            }
        }
        for i in k + 1..9 {
            for j in k + 1..9 {
                a[i][j] = (a[i][j] * a[k][k] - a[i][k] * a[k][j]) / prev;
            }
            a[i][k] = 0;
        }
        prev = a[k][k];
    }
    a[8][8].abs()
}

struct Leg {
    rows: Vec<V9>,          // the 23 signed rows, input order
    reps: Vec<V9>,          // distinct rows up to sign (canonical), d of them
    row_rep: Vec<(usize, i32)>, // row i = sign * reps[idx]
    exact: bool,
}

impl Leg {
    fn new(rows: Vec<V9>, exact: bool) -> Self {
        let mut reps: Vec<V9> = Vec::new();
        let mut row_rep = Vec::new();
        for r in &rows {
            assert!(!is_zero(r), "zero row");
            let (c, s) = if exact { (*r, 1) } else { canon(*r) };
            if let Some(i) = reps.iter().position(|x| *x == c) {
                row_rep.push((i, s));
            } else {
                reps.push(c);
                row_rep.push((reps.len() - 1, s));
            }
        }
        Leg { rows, reps, row_rep, exact }
    }

    fn d(&self) -> usize {
        self.reps.len()
    }

    /// index of an available form among reps: exact mode compares as-is,
    /// free mode compares canonically.
    fn rep_of(&self, v: &V9) -> Option<(usize, i32)> {
        if self.exact {
            self.reps.iter().position(|r| r == v).map(|i| (i, 1))
        } else {
            let (c, s) = canon(*v);
            self.reps.iter().position(|r| *r == c).map(|i| (i, s))
        }
    }

    fn subsets9(&self) -> Vec<Vec<usize>> {
        let d = self.d();
        let mut out = Vec::new();
        if d < 9 {
            return out;
        }
        let mut idx: Vec<usize> = (0..9).collect();
        loop {
            let rows: Vec<V9> = idx.iter().map(|&i| self.reps[i]).collect();
            if abs_det(&rows) == 1 {
                out.push(idx.clone());
            }
            let mut i = 9;
            loop {
                if i == 0 {
                    return out;
                }
                i -= 1;
                if idx[i] != i + d - 9 {
                    idx[i] += 1;
                    for j in i + 1..9 {
                        idx[j] = idx[j - 1] + 1;
                    }
                    break;
                }
            }
        }
    }
}

#[derive(Clone)]
struct State {
    avail: Vec<V9>,            // concrete signed values present
    built: u32,                // bitmask over reps
    steps: Vec<(V9, V9, i32, V9)>, // (x, y, sign, value)
}

/// Waste-free signed closure: add any x ± y that equals an unbuilt
/// target (exact or canonical per leg mode).
fn closure(leg: &Leg, st: &mut State) {
    loop {
        let mut grew = false;
        'outer: for i in 0..st.avail.len() {
            for j in i + 1..st.avail.len() {
                for s in [1i32, -1] {
                    let v = vadd(&st.avail[i], &st.avail[j], s);
                    if is_zero(&v) {
                        continue;
                    }
                    if let Some((t, _)) = leg.rep_of(&v) {
                        if st.built >> t & 1 == 0 {
                            st.built |= 1 << t;
                            st.steps.push((st.avail[i], st.avail[j], s, v));
                            st.avail.push(v);
                            grew = true;
                            break 'outer;
                        }
                    }
                }
            }
        }
        if !grew {
            return;
        }
    }
}

/// distinct non-present, non-zero pair sums of the available forms
fn helpers(leg: &Leg, st: &State) -> Vec<V9> {
    let mut out: Vec<V9> = Vec::new();
    for i in 0..st.avail.len() {
        for j in i + 1..st.avail.len() {
            for s in [1i32, -1] {
                let v = vadd(&st.avail[i], &st.avail[j], s);
                if is_zero(&v) || st.avail.contains(&v) || out.contains(&v) {
                    continue;
                }
                // a pair sum equal to an unbuilt target would have been
                // taken by the closure; equal to a built one is useless
                if leg.rep_of(&v).is_some() {
                    continue;
                }
                out.push(v);
            }
        }
    }
    out
}

#[derive(Clone)]
struct Cert {
    basis: Vec<V9>,
    steps: Vec<(V9, V9, i32, V9)>,
}

fn check_cert(leg: &Leg, c: &Cert, claimed: usize) -> bool {
    if c.basis.len() != 9 || abs_det(&c.basis) != 1 || c.steps.len() != claimed {
        return false;
    }
    let mut have = c.basis.clone();
    for (x, y, s, v) in &c.steps {
        if !have.contains(x) || !have.contains(y) || vadd(x, y, *s) != *v {
            return false;
        }
        have.push(*v);
    }
    // every row must be present up to the mode's sign convention
    leg.rows.iter().all(|r| {
        have.iter().any(|h| {
            if leg.exact {
                h == r
            } else {
                let (c1, _) = canon(*h);
                let (c2, _) = canon(*r);
                c1 == c2
            }
        })
    })
}

fn all_built(leg: &Leg) -> u32 {
    (1u32 << leg.d()) - 1
}

fn start_state(leg: &Leg, bidx: &[usize]) -> State {
    State {
        avail: bidx.iter().map(|&i| leg.reps[i]).collect(),
        built: bidx.iter().fold(0u32, |m, &i| m | 1 << i),
        steps: Vec::new(),
    }
}

fn solve(leg: &Leg, max_helpers: usize) -> (usize, Option<Cert>, String) {
    let d = leg.d();
    let bases = leg.subsets9();
    let done = all_built(leg);
    if bases.is_empty() {
        return (d - 9, None, "no unimodular 9-target basis exists".into());
    }

    // tier 1: zero helpers
    let hit = AtomicBool::new(false);
    let found: Mutex<Option<Cert>> = Mutex::new(None);
    bases.par_iter().for_each(|b| {
        if hit.load(Ordering::Relaxed) {
            return;
        }
        let mut st = start_state(leg, b);
        closure(leg, &mut st);
        if st.built == done {
            hit.store(true, Ordering::Relaxed);
            *found.lock().unwrap() = Some(Cert {
                basis: b.iter().map(|&i| leg.reps[i]).collect(),
                steps: st.steps,
            });
        }
    });
    if let Some(c) = found.into_inner().unwrap() {
        return (d - 9, Some(c), format!("tier1 signed ({} unimodular bases)", bases.len()));
    }
    if max_helpers == 0 {
        return (d - 8, None, "tier1 exhausted".into());
    }

    // tier 2: one helper at the fixpoint
    let hit = AtomicBool::new(false);
    let found: Mutex<Option<Cert>> = Mutex::new(None);
    bases.par_iter().for_each(|b| {
        if hit.load(Ordering::Relaxed) {
            return;
        }
        let mut st0 = start_state(leg, b);
        closure(leg, &mut st0);
        for h in helpers(leg, &st0) {
            let (px, py, ps) = find_parent(&st0.avail, &h);
            let mut st = st0.clone();
            st.steps.push((px, py, ps, h));
            st.avail.push(h);
            closure(leg, &mut st);
            if st.built == done {
                hit.store(true, Ordering::Relaxed);
                *found.lock().unwrap() = Some(Cert {
                    basis: b.iter().map(|&i| leg.reps[i]).collect(),
                    steps: st.steps,
                });
                return;
            }
        }
    });
    if let Some(c) = found.into_inner().unwrap() {
        return (d - 8, Some(c), "tier2 signed: 1 helper".into());
    }
    if max_helpers == 1 {
        return (d - 7, None, "tiers 1-2 (9-target bases) exhausted".into());
    }

    // tier 3: two helpers at successive fixpoints
    let hit = AtomicBool::new(false);
    let found: Mutex<Option<Cert>> = Mutex::new(None);
    bases.par_iter().for_each(|b| {
        if hit.load(Ordering::Relaxed) {
            return;
        }
        let mut st0 = start_state(leg, b);
        closure(leg, &mut st0);
        for h1 in helpers(leg, &st0) {
            let (p1x, p1y, p1s) = find_parent(&st0.avail, &h1);
            let mut st1 = st0.clone();
            st1.steps.push((p1x, p1y, p1s, h1));
            st1.avail.push(h1);
            closure(leg, &mut st1);
            if st1.built == done {
                continue; // would be tier2; already exhausted
            }
            for h2 in helpers(leg, &st1) {
                let (p2x, p2y, p2s) = find_parent(&st1.avail, &h2);
                let mut st = st1.clone();
                st.steps.push((p2x, p2y, p2s, h2));
                st.avail.push(h2);
                closure(leg, &mut st);
                if st.built == done {
                    hit.store(true, Ordering::Relaxed);
                    *found.lock().unwrap() = Some(Cert {
                        basis: b.iter().map(|&i| leg.reps[i]).collect(),
                        steps: st.steps,
                    });
                    return;
                }
            }
        }
    });
    if let Some(c) = found.into_inner().unwrap() {
        return (d - 7, Some(c), "tier3 signed: 2 helpers".into());
    }
    if max_helpers == 2 {
        return (d - 6, None, "tiers 1-3 (9-target bases) exhausted".into());
    }

    // tier 4: three helpers at successive fixpoints (typically used as a
    // find-only witness pass; completing it is also a valid exhaustion)
    let hit = AtomicBool::new(false);
    let found: Mutex<Option<Cert>> = Mutex::new(None);
    bases.par_iter().for_each(|b| {
        if hit.load(Ordering::Relaxed) {
            return;
        }
        let mut st0 = start_state(leg, b);
        closure(leg, &mut st0);
        for h1 in helpers(leg, &st0) {
            let (p1x, p1y, p1s) = find_parent(&st0.avail, &h1);
            let mut st1 = st0.clone();
            st1.steps.push((p1x, p1y, p1s, h1));
            st1.avail.push(h1);
            closure(leg, &mut st1);
            for h2 in helpers(leg, &st1) {
                if hit.load(Ordering::Relaxed) {
                    return;
                }
                let (p2x, p2y, p2s) = find_parent(&st1.avail, &h2);
                let mut st2 = st1.clone();
                st2.steps.push((p2x, p2y, p2s, h2));
                st2.avail.push(h2);
                closure(leg, &mut st2);
                for h3 in helpers(leg, &st2) {
                    let (p3x, p3y, p3s) = find_parent(&st2.avail, &h3);
                    let mut st = st2.clone();
                    st.steps.push((p3x, p3y, p3s, h3));
                    st.avail.push(h3);
                    closure(leg, &mut st);
                    if st.built == done {
                        hit.store(true, Ordering::Relaxed);
                        *found.lock().unwrap() = Some(Cert {
                            basis: b.iter().map(|&i| leg.reps[i]).collect(),
                            steps: st.steps,
                        });
                        return;
                    }
                }
            }
        }
    });
    if let Some(c) = found.into_inner().unwrap() {
        return (d - 6, Some(c), "tier4 signed: 3 helpers".into());
    }
    (d - 5, None, "tiers 1-4 (9-target bases) exhausted".into())
}

fn find_parent(avail: &[V9], h: &V9) -> (V9, V9, i32) {
    for i in 0..avail.len() {
        for j in i + 1..avail.len() {
            for s in [1i32, -1] {
                if vadd(&avail[i], &avail[j], s) == *h {
                    return (avail[i], avail[j], s);
                }
            }
        }
    }
    unreachable!("helper has no parents")
}

fn fmt(v: &V9) -> String {
    v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" ")
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut threads = 2usize;
    let mut exact = false;
    let mut max_helpers = 2usize;
    let mut files: Vec<String> = Vec::new();
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--threads" => {
                i += 1;
                threads = args[i].parse().unwrap();
            }
            "--exact" => exact = true,
            "--max-helpers" => {
                i += 1;
                max_helpers = args[i].parse().unwrap();
            }
            f => files.push(f.to_string()),
        }
        i += 1;
    }
    rayon::ThreadPoolBuilder::new().num_threads(threads).build_global().unwrap();
    eprintln!("fbsmin: {threads} thread(s), exact={exact}");

    for f in &files {
        let rows: Vec<V9> = std::fs::read_to_string(f)
            .expect(f)
            .lines()
            .filter(|l| !l.trim().is_empty())
            .map(|l| {
                let v: Vec<i32> = l.split_whitespace().map(|t| t.parse().unwrap()).collect();
                assert_eq!(v.len(), 9, "bad signed row");
                let mut a = [0i32; 9];
                a.copy_from_slice(&v);
                a
            })
            .collect();
        let leg = Leg::new(rows, exact);
        let t0 = std::time::Instant::now();
        let (a, cert, how) = solve(&leg, max_helpers);
        let dt = t0.elapsed().as_secs_f64();
        match cert {
            Some(c) => {
                assert!(check_cert(&leg, &c, a), "SIGNED CERTIFICATE FAILED CHECK");
                println!("{f}: d={} min_adds={a} [{how}] ({dt:.1} s) CERT-OK", leg.d());
                // realized sign per input row (for cross-leg eps bookkeeping)
                let mut have = c.basis.clone();
                for st in &c.steps {
                    have.push(st.3);
                }
                let eps: Vec<i32> = leg
                    .rows
                    .iter()
                    .map(|r| {
                        if have.contains(r) {
                            1
                        } else {
                            -1 // present as the negation (free mode)
                        }
                    })
                    .collect();
                println!("  eps: {}", eps.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" "));
                for b in &c.basis {
                    println!("  basis: {}", fmt(b));
                }
                for (x, y, s, v) in &c.steps {
                    println!("  add [{}] {} [{}] -> [{}]", fmt(x), if *s == 1 { "+" } else { "-" }, fmt(y), fmt(v));
                }
            }
            None => {
                println!("{f}: d={} min_adds>={a} [{how}] ({dt:.1} s)", leg.d());
            }
        }
    }
}
