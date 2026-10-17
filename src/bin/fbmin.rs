//! fbmin: exact free-basis addition minimization for one leg of a
//! bilinear scheme over F_2 (the Karstadt–Schwartz alternative-basis
//! cost model of arXiv 2609.06588).
//!
//! Input: a `.legs` file, one 9-char 0/1 mask per line (a 23×9 leg of a
//! rank-23 3×3 scheme; duplicate rows fine).  Question: minimize, over
//! invertible B ∈ GL(9, F₂), the number of XOR additions needed to
//! compute all rows of X·B from the 9 transformed inputs.  Basis-free
//! form: choose any 9 linearly independent free forms, then build every
//! distinct target form by pairwise XORs, 1 add each.
//!
//! Exactness: a chain with a additions, k of the 9 free forms being
//! targets and h helper (non-target) additions satisfies
//! a = (d − k) + h, where d = number of distinct targets.  Hence
//!   a = d−9  ⟺  some independent 9-target basis CLOSES to all of T
//!              under "add any pair-XOR that is an unbuilt target"
//!              (the closure is monotone, so greedy closure decides
//!              waste-free reachability exactly);
//!   a = d−8  ⟺  (i)  a 9-target basis plus ONE helper — and every
//!              form preceding the helper lies in the pure closure C₀,
//!              so the helper is a pair-XOR of C₀, injectable at the
//!              fixpoint (complete enumeration over pairsums(C₀)); or
//!              (ii) an independent 8-target basis plus one free
//!              non-target vector g, zero helpers (closure of B ∪ {g}).
//! The sweep over these cases is exhaustive, so "no" answers are
//! proofs, and every "yes" prints a chain certificate that an
//! independent checker (`check_cert`) replays before it is reported.
//!
//! The a = d−7 tier ((9T,2h), (8T+1g,1h), (7T+2g,0h)) is implemented
//! behind `--tier3`; its two-helper case injects helpers sequentially
//! at successive fixpoints, complete by the same preceding-forms
//! argument applied twice.
//!
//! Threads default to 2 (session cap); raise with --threads when
//! allowed.

use rayon::prelude::*;
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, Ordering};

type Mask = u16;

fn rank(masks: &[Mask]) -> usize {
    let mut piv: Vec<Mask> = Vec::with_capacity(9);
    for &m in masks {
        let mut x = m;
        for &p in &piv {
            let hb = 15 - p.leading_zeros() as usize;
            if x >> hb & 1 == 1 {
                x ^= p;
            }
        }
        if x != 0 {
            piv.push(x);
        }
    }
    piv.len()
}

/// Waste-free closure: from the available forms, repeatedly add any
/// pair-XOR that is an unbuilt target.  Returns (available forms,
/// built-target bitmask, parent pairs for certificate reconstruction).
fn closure(
    targets: &[Mask],
    tidx: &[i8; 512],
    start: &[Mask],
    built0: u32,
) -> (Vec<Mask>, u32, Vec<(Mask, Mask, Mask)>) {
    let mut avail = start.to_vec();
    let mut built = built0;
    let mut steps = Vec::new();
    loop {
        let mut grew = false;
        'outer: for i in 0..avail.len() {
            for j in i + 1..avail.len() {
                let s = avail[i] ^ avail[j];
                let t = tidx[s as usize];
                if t >= 0 && built >> t & 1 == 0 {
                    built |= 1 << t;
                    steps.push((avail[i], avail[j], s));
                    avail.push(s);
                    grew = true;
                    break 'outer;
                }
            }
        }
        if !grew {
            let _ = targets;
            return (avail, built, steps);
        }
    }
}

#[derive(Clone)]
struct Cert {
    basis: Vec<Mask>,     // 9 free forms (independent)
    adds: Vec<(Mask, Mask, Mask)>, // (x, y, x^y) in build order
}

/// Independent replay: basis independent, 9 long; every add's operands
/// already available; all targets end up available; add count = claimed.
fn check_cert(targets: &[Mask], c: &Cert, claimed: usize) -> bool {
    if c.basis.len() != 9 || rank(&c.basis) != 9 || c.adds.len() != claimed {
        return false;
    }
    let mut have: Vec<Mask> = c.basis.clone();
    for &(x, y, s) in &c.adds {
        if !have.contains(&x) || !have.contains(&y) || x ^ y != s {
            return false;
        }
        have.push(s);
    }
    targets.iter().all(|t| have.contains(t))
}

struct Leg {
    targets: Vec<Mask>,
    tidx: [i8; 512],
    all_built: u32,
}

impl Leg {
    fn new(rows: &[Mask]) -> Self {
        let mut targets: Vec<Mask> = Vec::new();
        for &r in rows {
            assert!(r != 0, "zero factor row");
            if !targets.contains(&r) {
                targets.push(r);
            }
        }
        assert!(rank(&targets) == 9, "leg does not span F_2^9");
        let mut tidx = [-1i8; 512];
        for (i, &t) in targets.iter().enumerate() {
            tidx[t as usize] = i as i8;
        }
        let all_built = (1u32 << targets.len()) - 1;
        Leg { targets, tidx, all_built }
    }

    fn d(&self) -> usize {
        self.targets.len()
    }

    /// all independent k-subsets of targets, as index vectors
    fn subsets(&self, k: usize) -> Vec<Vec<usize>> {
        let d = self.d();
        let mut out = Vec::new();
        let mut idx: Vec<usize> = (0..k).collect();
        loop {
            let masks: Vec<Mask> = idx.iter().map(|&i| self.targets[i]).collect();
            if rank(&masks) == k {
                out.push(idx.clone());
            }
            // next combination
            let mut i = k;
            loop {
                if i == 0 {
                    return out;
                }
                i -= 1;
                if idx[i] != i + d - k {
                    idx[i] += 1;
                    for j in i + 1..k {
                        idx[j] = idx[j - 1] + 1;
                    }
                    break;
                }
            }
        }
    }

    fn built_of(&self, basis_idx: &[usize]) -> u32 {
        basis_idx.iter().fold(0u32, |m, &i| m | 1 << i)
    }

    /// distinct nonzero pair-XORs of `forms` that are not already present
    fn helper_cands(&self, forms: &[Mask]) -> Vec<Mask> {
        let mut out: Vec<Mask> = Vec::new();
        for i in 0..forms.len() {
            for j in i + 1..forms.len() {
                let s = forms[i] ^ forms[j];
                if s != 0 && !forms.contains(&s) && !out.contains(&s) {
                    out.push(s);
                }
            }
        }
        out
    }
}

fn solve(leg: &Leg, tier3: bool, want: usize, tier1_only: bool) -> (usize, Vec<Cert>, String) {
    let d = leg.d();
    let floor = d - 9;

    // ---- tier 1: a = d-9 (9-target basis, waste-free closure) ----
    let bases9 = leg.subsets(9);
    let found: Mutex<Option<Cert>> = Mutex::new(None);
    let hit = AtomicBool::new(false);
    bases9.par_iter().for_each(|bidx| {
        if hit.load(Ordering::Relaxed) {
            return;
        }
        let basis: Vec<Mask> = bidx.iter().map(|&i| leg.targets[i]).collect();
        let (_, built, steps) = closure(&leg.targets, &leg.tidx, &basis, leg.built_of(bidx));
        if built == leg.all_built {
            hit.store(true, Ordering::Relaxed);
            *found.lock().unwrap() = Some(Cert { basis, adds: steps });
        }
    });
    if let Some(c) = found.into_inner().unwrap() {
        return (floor, vec![c], format!("tier1: 9-target basis closes ({} bases swept)", bases9.len()));
    }
    if tier1_only {
        // the floor d-9 is attained iff some 9-target basis closes
        return (floor + 1, Vec::new(), format!("tier1 exhausted: floor not attained ({} bases swept)", bases9.len()));
    }

    // ---- tier 2a: a = d-8 via 9-target basis + one helper ----
    let found: Mutex<Vec<Cert>> = Mutex::new(Vec::new());
    let hit = AtomicBool::new(false);
    bases9.par_iter().for_each(|bidx| {
        if hit.load(Ordering::Relaxed) {
            return;
        }
        let basis: Vec<Mask> = bidx.iter().map(|&i| leg.targets[i]).collect();
        let b0 = leg.built_of(bidx);
        let (avail0, built0, steps0) = closure(&leg.targets, &leg.tidx, &basis, b0);
        for h in leg.helper_cands(&avail0) {
            // reconstruct the helper's parents from avail0
            let mut parent = None;
            'p: for i in 0..avail0.len() {
                for j in i + 1..avail0.len() {
                    if avail0[i] ^ avail0[j] == h {
                        parent = Some((avail0[i], avail0[j]));
                        break 'p;
                    }
                }
            }
            let mut start = avail0.clone();
            start.push(h);
            let (_, built, steps1) = closure(&leg.targets, &leg.tidx, &start, built0);
            if built == leg.all_built {
                let (px, py) = parent.unwrap();
                let mut adds = steps0.clone();
                adds.push((px, py, h));
                adds.extend(steps1);
                let mut v = found.lock().unwrap();
                v.push(Cert { basis: basis.clone(), adds });
                if v.len() >= want {
                    hit.store(true, Ordering::Relaxed);
                    return;
                }
            }
        }
    });
    let v = found.into_inner().unwrap();
    if !v.is_empty() {
        return (floor + 1, v, "tier2a: 9-target basis + 1 helper".into());
    }

    // ---- tier 2b: a = d-8 via 8-target basis + one free vector ----
    let bases8 = leg.subsets(8);
    let found: Mutex<Option<Cert>> = Mutex::new(None);
    let hit = AtomicBool::new(false);
    bases8.par_iter().for_each(|bidx| {
        if hit.load(Ordering::Relaxed) {
            return;
        }
        let basis8: Vec<Mask> = bidx.iter().map(|&i| leg.targets[i]).collect();
        let b0 = leg.built_of(bidx);
        for g in 1u16..512 {
            let mut basis = basis8.clone();
            basis.push(g);
            if rank(&basis) != 9 {
                continue;
            }
            let (_, built, steps) = closure(&leg.targets, &leg.tidx, &basis, b0);
            if built == leg.all_built {
                hit.store(true, Ordering::Relaxed);
                *found.lock().unwrap() = Some(Cert { basis, adds: steps });
                return;
            }
        }
    });
    if let Some(c) = found.into_inner().unwrap() {
        return (floor + 1, vec![c], format!("tier2b: 8-target basis + free vector ({} bases)", bases8.len()));
    }

    if !tier3 {
        return (floor + 2, Vec::new(), "tiers 1-2 exhausted: min >= d-7 (run --tier3 to decide)".into());
    }

    // ---- tier 3: a = d-7 ----
    // (9T, 2 helpers): helpers injected at successive fixpoints.
    let found: Mutex<Vec<Cert>> = Mutex::new(Vec::new());
    let hit = AtomicBool::new(false);
    bases9.par_iter().for_each(|bidx| {
        if hit.load(Ordering::Relaxed) {
            return;
        }
        let basis: Vec<Mask> = bidx.iter().map(|&i| leg.targets[i]).collect();
        let b0 = leg.built_of(bidx);
        let (avail0, built0, steps0) = closure(&leg.targets, &leg.tidx, &basis, b0);
        for h1 in leg.helper_cands(&avail0) {
            let mut s1 = avail0.clone();
            s1.push(h1);
            let (avail1, built1, steps1) = closure(&leg.targets, &leg.tidx, &s1, built0);
            for h2 in leg.helper_cands(&avail1) {
                let mut s2 = avail1.clone();
                s2.push(h2);
                let (_, built2, steps2) = closure(&leg.targets, &leg.tidx, &s2, built1);
                if built2 == leg.all_built {
                    let find_parent = |forms: &[Mask], h: Mask| -> (Mask, Mask) {
                        for i in 0..forms.len() {
                            for j in i + 1..forms.len() {
                                if forms[i] ^ forms[j] == h {
                                    return (forms[i], forms[j]);
                                }
                            }
                        }
                        unreachable!()
                    };
                    let (x1, y1) = find_parent(&avail0, h1);
                    let (x2, y2) = find_parent(&avail1, h2);
                    let mut adds = steps0.clone();
                    adds.push((x1, y1, h1));
                    adds.extend(steps1.clone());
                    adds.push((x2, y2, h2));
                    adds.extend(steps2);
                    let mut v = found.lock().unwrap();
                    v.push(Cert { basis: basis.clone(), adds });
                    if v.len() >= want {
                        hit.store(true, Ordering::Relaxed);
                        return;
                    }
                }
            }
        }
    });
    let v = found.into_inner().unwrap();
    if !v.is_empty() {
        return (floor + 2, v, "tier3: 9-target basis + 2 helpers".into());
    }

    // (8T + g, 1 helper)
    let found: Mutex<Vec<Cert>> = Mutex::new(Vec::new());
    let hit = AtomicBool::new(false);
    bases8.par_iter().for_each(|bidx| {
        if hit.load(Ordering::Relaxed) {
            return;
        }
        let basis8: Vec<Mask> = bidx.iter().map(|&i| leg.targets[i]).collect();
        let b0 = leg.built_of(bidx);
        for g in 1u16..512 {
            let mut basis = basis8.clone();
            basis.push(g);
            if rank(&basis) != 9 {
                continue;
            }
            let (avail0, built0, steps0) = closure(&leg.targets, &leg.tidx, &basis, b0);
            for h in leg.helper_cands(&avail0) {
                let mut s1 = avail0.clone();
                s1.push(h);
                let (_, built, steps1) = closure(&leg.targets, &leg.tidx, &s1, built0);
                if built == leg.all_built {
                    let mut parent = None;
                    'p: for i in 0..avail0.len() {
                        for j in i + 1..avail0.len() {
                            if avail0[i] ^ avail0[j] == h {
                                parent = Some((avail0[i], avail0[j]));
                                break 'p;
                            }
                        }
                    }
                    let (px, py) = parent.unwrap();
                    let mut adds = steps0.clone();
                    adds.push((px, py, h));
                    adds.extend(steps1);
                    let mut v = found.lock().unwrap();
                    v.push(Cert { basis: basis.clone(), adds });
                    if v.len() >= want {
                        hit.store(true, Ordering::Relaxed);
                        return;
                    }
                }
            }
        }
    });
    let v = found.into_inner().unwrap();
    if !v.is_empty() {
        return (floor + 2, v, "tier3: 8-target basis + free vector + 1 helper".into());
    }

    // (7T + 2g, 0 helpers)
    let bases7 = leg.subsets(7);
    let found: Mutex<Vec<Cert>> = Mutex::new(Vec::new());
    let hit = AtomicBool::new(false);
    bases7.par_iter().for_each(|bidx| {
        if hit.load(Ordering::Relaxed) {
            return;
        }
        let basis7: Vec<Mask> = bidx.iter().map(|&i| leg.targets[i]).collect();
        let b0 = leg.built_of(bidx);
        for g1 in 1u16..512 {
            let mut b9 = basis7.clone();
            b9.push(g1);
            if rank(&b9) != 8 {
                continue;
            }
            for g2 in g1 + 1..512 {
                let mut basis = b9.clone();
                basis.push(g2);
                if rank(&basis) != 9 {
                    continue;
                }
                let (_, built, steps) = closure(&leg.targets, &leg.tidx, &basis, b0);
                if built == leg.all_built {
                    let mut v = found.lock().unwrap();
                    v.push(Cert { basis: basis.clone(), adds: steps });
                    if v.len() >= want {
                        hit.store(true, Ordering::Relaxed);
                        return;
                    }
                }
            }
        }
    });
    let v = found.into_inner().unwrap();
    if !v.is_empty() {
        return (floor + 2, v, "tier3: 7-target basis + 2 free vectors".into());
    }

    (floor + 3, Vec::new(), "tiers 1-3 exhausted: min >= d-6".into())
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut threads = 2usize;
    let mut tier3 = false;
    let mut tier1_only = false;
    let mut want = 1usize;
    let mut files: Vec<String> = Vec::new();
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--threads" => {
                i += 1;
                threads = args[i].parse().unwrap();
            }
            "--enum" => {
                i += 1;
                want = args[i].parse::<usize>().unwrap().max(1);
            }
            "--tier3" => tier3 = true,
            "--tier1-only" => tier1_only = true,
            f => files.push(f.to_string()),
        }
        i += 1;
    }
    rayon::ThreadPoolBuilder::new().num_threads(threads).build_global().unwrap();
    eprintln!("fbmin: {} thread(s)", threads);

    for f in &files {
        let txt = std::fs::read_to_string(f).expect(f);
        let rows: Vec<Mask> = txt
            .lines()
            .filter(|l| !l.trim().is_empty())
            .map(|l| {
                assert_eq!(l.trim().len(), 9, "bad mask line");
                Mask::from_str_radix(l.trim(), 2).unwrap()
            })
            .collect();
        let leg = Leg::new(&rows);
        let t0 = std::time::Instant::now();
        let (a, certs, how) = solve(&leg, tier3, want, tier1_only);
        let dt = t0.elapsed().as_secs_f64();
        if certs.is_empty() {
            println!("{f}: d={} min_adds>={a} [{how}] ({dt:.1} s)", leg.d());
        } else {
            for c in &certs {
                assert!(check_cert(&leg.targets, c, a), "CERTIFICATE FAILED CHECK");
            }
            println!("{f}: d={} min_adds={a} [{how}] ({dt:.1} s) {} cert(s), all CERT-OK",
                     leg.d(), certs.len());
            for c in &certs {
                println!("  basis: {}", c.basis.iter().map(|m| format!("{m:09b}")).collect::<Vec<_>>().join(" "));
                for (x, y, s) in &c.adds {
                    println!("  add {x:09b} ^ {y:09b} = {s:09b}");
                }
            }
        }
    }
}
