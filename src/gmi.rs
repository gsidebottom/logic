//! Exact-rational Gomory (GMI) cutting-plane refutation — Rust port of
//! `neural/cp_gmi.py`.
//!
//! Standalone structural prover in the `cook_pbp` / `parity_pbp` tradition, but
//! GENERAL: one algorithm (exact rational simplex → Gomory cut → CG emission),
//! no per-family pattern-matching.  An UNSAT 0/1 system is refuted by the
//! cutting-plane method — solve the LP relaxation exactly; read a Gomory cut off
//! the optimal tableau (its fractional-part multipliers are nonnegative *by
//! construction*, so the cut emits as one VeriPB `pol Σ λ·Con  D d` over the PB
//! constraints and the literal bound axioms `xv` / `~xv`); iterate until the LP
//! is infeasible; close with an exact Farkas combination.  Every step is a legal
//! cutting-plane derivation, so the emitted `.pbp` is VeriPB-checkable.
//!
//! Arithmetic is `BigRational` throughout: a proof engine must never silently
//! overflow.  For the structured 0/1 systems here the basis subdeterminants stay
//! small, so the bignums stay small.

use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::collections::BTreeMap;

type Rat = BigRational;

fn bi(n: i64) -> BigInt {
    BigInt::from(n)
}
fn rat_i(n: i64) -> Rat {
    Rat::from_integer(bi(n))
}
fn ceil_div(a: &BigInt, b: &BigInt) -> BigInt {
    // b > 0
    (a + b - BigInt::one()).div_floor(b)
}
fn frac(z: &Rat) -> Rat {
    z.clone() - z.floor()
}

// ── PB constraint  Σ coef[v]·x_v >= rhs  (signed-variable form) ──────────────

#[derive(Clone, Debug)]
pub struct Pb {
    pub coef: BTreeMap<u32, BigInt>,
    pub rhs: BigInt,
}

impl Pb {
    fn norm(mut self) -> Pb {
        self.coef.retain(|_, c| !c.is_zero());
        self
    }

    pub fn from_clause(lits: &[i32]) -> Pb {
        let mut coef: BTreeMap<u32, BigInt> = BTreeMap::new();
        let mut rhs = BigInt::one();
        for &l in lits {
            let v = l.unsigned_abs();
            if l > 0 {
                *coef.entry(v).or_insert_with(BigInt::zero) += 1;
            } else {
                *coef.entry(v).or_insert_with(BigInt::zero) -= 1;
                rhs -= 1;
            }
        }
        Pb { coef, rhs }.norm()
    }

    fn is_contradiction(&self) -> bool {
        self.coef.is_empty() && self.rhs >= BigInt::one()
    }

    /// (lits, rhs') in literal-normalized form: each entry (var, negated, |coef|),
    /// all coefficients >= 0.
    fn to_lit_norm(&self) -> (Vec<(u32, bool, BigInt)>, BigInt) {
        let mut lits = Vec::new();
        let mut rhs = self.rhs.clone();
        for (&v, c) in &self.coef {
            if c.is_positive() {
                lits.push((v, false, c.clone()));
            } else if c.is_negative() {
                let a = -c;
                rhs += &a; // c·x = |c|·~x − |c|; move −|c| to rhs
                lits.push((v, true, a));
            }
        }
        (lits, rhs)
    }

    /// Chvátal–Gomory cut: literal-normalize, divide by d, round up.
    fn divide(&self, d: &BigInt) -> Pb {
        let (lits, rhs) = self.to_lit_norm();
        let mut coef: BTreeMap<u32, BigInt> = BTreeMap::new();
        for (v, neg, c) in &lits {
            let cc = ceil_div(c, d);
            let e = coef.entry(*v).or_insert_with(BigInt::zero);
            if *neg {
                *e -= &cc;
            } else {
                *e += &cc;
            }
        }
        let mut newrhs = ceil_div(&rhs, d);
        for (_, neg, c) in &lits {
            if *neg {
                newrhs -= ceil_div(c, d);
            }
        }
        Pb { coef, rhs: newrhs }.norm()
    }

    /// Sound canonical form for dedup: literal-normalize → saturate → gcd-divide.
    fn canonical(&self) -> Pb {
        let (lits, rhs) = self.to_lit_norm();
        if rhs <= BigInt::zero() || lits.is_empty() {
            return self.clone();
        }
        let mut sat: Vec<(u32, bool, BigInt)> = lits
            .into_iter()
            .map(|(v, n, c)| (v, n, if c > rhs { rhs.clone() } else { c }))
            .collect();
        let mut g = rhs.clone();
        for (_, _, c) in &sat {
            g = g.gcd(c);
        }
        let mut r = rhs;
        if g > BigInt::one() {
            for (_, _, c) in &mut sat {
                *c /= &g;
            }
            r /= &g;
        }
        let mut coef: BTreeMap<u32, BigInt> = BTreeMap::new();
        let mut srhs = r;
        for (v, neg, c) in sat {
            let e = coef.entry(v).or_insert_with(BigInt::zero);
            if neg {
                *e -= &c;
                srhs -= &c;
            } else {
                *e += &c;
            }
        }
        Pb { coef, rhs: srhs }.norm()
    }

    fn key(&self) -> String {
        let c = self.canonical();
        let mut s = String::new();
        for (v, a) in &c.coef {
            s.push_str(&format!("{}:{},", v, a));
        }
        s.push(';');
        s.push_str(&c.rhs.to_string());
        s
    }
}

/// a·ma + b·mb, signed-variable.
fn add_scaled(a: &Pb, ma: &BigInt, b: &Pb, mb: &BigInt) -> Pb {
    let mut coef: BTreeMap<u32, BigInt> = BTreeMap::new();
    for (&v, c) in &a.coef {
        *coef.entry(v).or_insert_with(BigInt::zero) += c * ma;
    }
    for (&v, c) in &b.coef {
        *coef.entry(v).or_insert_with(BigInt::zero) += c * mb;
    }
    Pb {
        coef,
        rhs: &a.rhs * ma + &b.rhs * mb,
    }
    .norm()
}

// ── exact two-phase simplex (Bland's rule) ──────────────────────────────────

#[derive(PartialEq, Debug)]
enum Status {
    Optimal,
    Infeasible,
}

/// In-place Bland-rule simplex minimizing cost·y on tableau (T, b, basis).
/// `cost.len()` is the working column count (= each row's length).
fn optimize(t: &mut [Vec<Rat>], b: &mut [Rat], basis: &mut [usize], cost: &[Rat]) {
    let nrows = basis.len();
    let ncols = cost.len();
    let zero = Rat::zero();
    loop {
        let cb: Vec<&Rat> = (0..nrows).map(|i| &cost[basis[i]]).collect();
        // entering: lowest-index column with negative reduced cost (Bland)
        let mut enter = usize::MAX;
        for j in 0..ncols {
            let mut rc = cost[j].clone();
            for i in 0..nrows {
                if !cb[i].is_zero() {
                    rc -= cb[i] * &t[i][j];
                }
            }
            if rc < zero {
                enter = j;
                break;
            }
        }
        if enter == usize::MAX {
            return;
        }
        // leaving: min ratio b[i]/t[i][enter] over t[i][enter] > 0, Bland tie-break
        let mut leave = usize::MAX;
        let mut best: Option<Rat> = None;
        for i in 0..nrows {
            if t[i][enter] > zero {
                let ratio = &b[i] / &t[i][enter];
                let take = match &best {
                    None => true,
                    Some(bv) => ratio < *bv || (ratio == *bv && basis[i] < basis[leave]),
                };
                if take {
                    best = Some(ratio);
                    leave = i;
                }
            }
        }
        if leave == usize::MAX {
            return; // unbounded — does not occur for the bounded LPs here
        }
        let piv = t[leave][enter].clone();
        for x in t[leave].iter_mut() {
            *x /= &piv;
        }
        b[leave] /= &piv;
        for i in 0..nrows {
            if i != leave && !t[i][enter].is_zero() {
                let f = t[i][enter].clone();
                for j in 0..t[i].len() {
                    let d = &f * &t[leave][j];
                    t[i][j] -= d;
                }
                let d = &f * &b[leave];
                b[i] -= d;
            }
        }
        basis[leave] = enter;
    }
}

/// Two-phase exact simplex for {a·y = b0, y >= 0} minimizing cost·y (cost over
/// the structural columns).  Returns (status, tableau, rhs, basis) with the
/// tableau restricted to the structural columns (artificials dropped).
fn two_phase(
    a: &[Vec<Rat>],
    b0: &[Rat],
    cost: &[Rat],
) -> (Status, Vec<Vec<Rat>>, Vec<Rat>, Vec<usize>) {
    let nrows = a.len();
    let ncols = if nrows > 0 { a[0].len() } else { 0 };
    let total = ncols + nrows;
    let mut t: Vec<Vec<Rat>> = Vec::with_capacity(nrows);
    let mut b: Vec<Rat> = Vec::with_capacity(nrows);
    for i in 0..nrows {
        let mut row = a[i].clone();
        row.resize(total, Rat::zero());
        let mut bi_ = b0[i].clone();
        if bi_ < Rat::zero() {
            for x in row.iter_mut() {
                *x = -std::mem::replace(x, Rat::zero());
            }
            bi_ = -bi_;
        }
        row[ncols + i] = Rat::one(); // artificial
        t.push(row);
        b.push(bi_);
    }
    let mut basis: Vec<usize> = (0..nrows).map(|i| ncols + i).collect();
    // phase 1: minimize sum of artificials
    let mut cost1 = vec![Rat::zero(); total];
    for j in ncols..total {
        cost1[j] = Rat::one();
    }
    optimize(&mut t, &mut b, &mut basis, &cost1);
    let art_val: Rat = (0..nrows)
        .filter(|&i| basis[i] >= ncols)
        .map(|i| b[i].clone())
        .fold(Rat::zero(), |acc, x| acc + x);
    if art_val > Rat::zero() {
        return (Status::Infeasible, vec![], vec![], vec![]);
    }
    // drive artificials still basic (at 0) out of the basis
    for i in 0..nrows {
        if basis[i] >= ncols {
            if let Some(pc) = (0..ncols).find(|&j| !t[i][j].is_zero()) {
                let piv = t[i][pc].clone();
                for x in t[i].iter_mut() {
                    *x /= &piv;
                }
                b[i] /= &piv;
                for k in 0..nrows {
                    if k != i && !t[k][pc].is_zero() {
                        let f = t[k][pc].clone();
                        for j in 0..t[k].len() {
                            let d = &f * &t[i][j];
                            t[k][j] -= d;
                        }
                        let d = &f * &b[i];
                        b[k] -= d;
                    }
                }
                basis[i] = pc;
            }
        }
    }
    // drop redundant rows (artificial still basic on an all-zero row) + artificials
    let keep: Vec<usize> = (0..nrows).filter(|&i| basis[i] < ncols).collect();
    let mut t2: Vec<Vec<Rat>> = keep
        .iter()
        .map(|&i| t[i][..ncols].to_vec())
        .collect();
    let mut b2: Vec<Rat> = keep.iter().map(|&i| b[i].clone()).collect();
    let mut basis2: Vec<usize> = keep.iter().map(|&i| basis[i]).collect();
    // phase 2: optimize the real objective
    let mut cost2 = vec![Rat::zero(); ncols];
    cost2[..cost.len()].clone_from_slice(cost);
    optimize(&mut t2, &mut b2, &mut basis2, &cost2);
    (Status::Optimal, t2, b2, basis2)
}

// ── standard form of the box LP {Σa·x >= b, 0 <= x <= 1} ─────────────────────

struct Std {
    n: usize,
    m: usize,
    ncols: usize,
}
impl Std {
    fn new(n: usize, m: usize) -> Std {
        Std {
            n,
            m,
            ncols: n + m + n,
        }
    }
    fn cx(&self, v: u32) -> usize {
        (v - 1) as usize
    }
    fn cs(&self, j: usize) -> usize {
        self.n + j
    }
    fn ct(&self, v: u32) -> usize {
        self.n + self.m + (v - 1) as usize
    }
    /// Build (A, b) of the standard form.  Columns [x_1..x_n | s_1..s_m | t_1..t_n]:
    ///   R_j: Σ_v a_jv x_v − s_j = b_j ;   U_v: x_v + t_v = 1.
    fn build(&self, cons: &[Pb]) -> (Vec<Vec<Rat>>, Vec<Rat>) {
        let nrows = self.m + self.n;
        let mut a = vec![vec![Rat::zero(); self.ncols]; nrows];
        let mut b = vec![Rat::zero(); nrows];
        for (j, c) in cons.iter().enumerate() {
            for (&v, co) in &c.coef {
                a[j][self.cx(v)] += Rat::from_integer(co.clone());
            }
            a[j][self.cs(j)] = -Rat::one();
            b[j] = Rat::from_integer(c.rhs.clone());
        }
        for v in 1..=self.n as u32 {
            let r = self.m + (v - 1) as usize;
            a[r][self.cx(v)] = Rat::one();
            a[r][self.ct(v)] = Rat::one();
            b[r] = Rat::one();
        }
        (a, b)
    }
}

fn primal(s: &Std, b: &[Rat], basis: &[usize]) -> Vec<Rat> {
    let mut x = vec![Rat::zero(); s.n];
    for i in 0..basis.len() {
        if basis[i] < s.n {
            x[basis[i]] = b[i].clone();
        }
    }
    x
}

// ── Gomory cuts from the optimal tableau ────────────────────────────────────

/// (D, lamC keyed by cons-index, lamL keyed by var, lamB keyed by var).
type Recipe = (BigInt, Vec<(usize, BigInt)>, Vec<(u32, BigInt)>, Vec<(u32, BigInt)>);

fn build_cut(cons: &[Pb], r: &Recipe) -> Pb {
    let (d, lam_c, lam_l, lam_b) = r;
    let mut acc: Option<Pb> = None;
    let add = |t: Pb, acc: &mut Option<Pb>| {
        *acc = Some(match acc.take() {
            None => t,
            Some(g) => add_scaled(&g, &BigInt::one(), &t, &BigInt::one()),
        });
    };
    for (idx, lam) in lam_c {
        let c = &cons[*idx];
        let coef = c.coef.iter().map(|(&v, a)| (v, a * lam)).collect();
        add(Pb { coef, rhs: &c.rhs * lam }.norm(), &mut acc);
    }
    for (v, lam) in lam_l {
        let mut coef = BTreeMap::new();
        coef.insert(*v, lam.clone());
        add(Pb { coef, rhs: BigInt::zero() }.norm(), &mut acc); // λ·(x_v >= 0)
    }
    for (v, lam) in lam_b {
        let mut coef = BTreeMap::new();
        coef.insert(*v, -lam);
        add(Pb { coef, rhs: -lam.clone() }.norm(), &mut acc); // λ·(1 − x_v >= 0)
    }
    acc.unwrap().divide(d)
}

/// All distinct violated Gomory cuts from the fractional basic rows.
fn gomory_cuts(s: &Std, t: &[Vec<Rat>], b: &[Rat], cons: &[Pb], x: &[Rat]) -> Vec<(Pb, Recipe)> {
    let mut out = Vec::new();
    let mut seen = std::collections::HashSet::new();
    for i in 0..b.len() {
        if frac(&b[i]).is_zero() {
            continue;
        }
        let row = &t[i];
        let mut lam_l: Vec<(u32, BigInt)> = Vec::new();
        let mut lam_c: Vec<(usize, BigInt)> = Vec::new();
        let mut lam_b: Vec<(u32, BigInt)> = Vec::new();
        let mut fracs: Vec<Rat> = Vec::new();
        for v in 1..=s.n as u32 {
            let f = frac(&row[s.cx(v)]);
            if !f.is_zero() {
                lam_l.push((v, BigInt::zero()));
                fracs.push(f);
            }
        }
        for j in 0..s.m {
            let f = frac(&row[s.cs(j)]);
            if !f.is_zero() {
                lam_c.push((j, BigInt::zero()));
                fracs.push(f);
            }
        }
        for v in 1..=s.n as u32 {
            let f = frac(&row[s.ct(v)]);
            if !f.is_zero() {
                lam_b.push((v, BigInt::zero()));
                fracs.push(f);
            }
        }
        if fracs.is_empty() {
            continue;
        }
        let mut d = BigInt::one();
        for f in &fracs {
            d = d.lcm(f.denom());
        }
        if d.is_one() {
            continue;
        }
        // fill the integer multipliers λ = frac · D, recomputing per column
        let scale = |raw: &Rat| -> BigInt { (raw * Rat::from_integer(d.clone())).to_integer() };
        for (v, lam) in lam_l.iter_mut() {
            *lam = scale(&frac(&row[s.cx(*v)]));
        }
        for (j, lam) in lam_c.iter_mut() {
            *lam = scale(&frac(&row[s.cs(*j)]));
        }
        for (v, lam) in lam_b.iter_mut() {
            *lam = scale(&frac(&row[s.ct(*v)]));
        }
        let recipe: Recipe = (d, lam_c, lam_l, lam_b);
        let cut = build_cut(cons, &recipe);
        if cut.coef.is_empty() {
            continue;
        }
        // violation at x*: rhs − Σ coef·x*
        let mut viol = Rat::from_integer(cut.rhs.clone());
        for (&v, a) in &cut.coef {
            viol -= Rat::from_integer(a.clone()) * &x[(v - 1) as usize];
        }
        if viol <= Rat::zero() {
            continue;
        }
        let k = cut.key();
        if seen.insert(k) {
            out.push((cut, recipe));
        }
    }
    out
}

// ── cut loop ────────────────────────────────────────────────────────────────

pub struct Refutation {
    pub cuts: Vec<Recipe>,        // cut k lives at constraint id n_inputs+1+k
    pub farkas: Vec<FarkasTerm>,  // final combination
    pub cons_len: usize,
}

#[derive(Clone)]
pub enum FarkasTerm {
    Con(usize, BigInt),  // constraint id-1 (index into inputs+cuts), multiplier
    Lower(u32, BigInt),  // x_v >= 0 axiom
    Upper(u32, BigInt),  // x_v <= 1 axiom (~x_v)
}

fn lcg_objs(n: usize, n_obj: usize, rnd: usize) -> Vec<Option<Vec<Rat>>> {
    let mut objs: Vec<Option<Vec<Rat>>> = vec![None]; // None = maximize Σx
    let mut seed: u64 = 0x9e3779b97f4a7c15u64 ^ (rnd as u64).wrapping_mul(0x100000001b3);
    for _ in 1..n_obj {
        let mut o = Vec::with_capacity(n);
        for _ in 0..n {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            o.push(rat_i(((seed >> 33) % 5) as i64 - 2)); // {−2..2}
        }
        objs.push(Some(o));
    }
    objs
}

/// Cutting-plane loop with Gomory separation.  Returns (cons, refuted, cuts).
fn gmi_loop(
    inputs: &[Pb],
    nvars: usize,
    max_rounds: usize,
    n_obj: usize,
    max_secs: f64,
) -> (Vec<Pb>, bool, Vec<Recipe>) {
    let start = std::time::Instant::now();
    let mut cons: Vec<Pb> = inputs.to_vec();
    let mut cuts: Vec<Recipe> = Vec::new();
    let mut seen: std::collections::HashSet<String> = cons.iter().map(|c| c.key()).collect();
    for rnd in 0..max_rounds {
        if max_secs > 0.0 && start.elapsed().as_secs_f64() > max_secs {
            return (cons, false, cuts); // wall-clock guard
        }
        let mut added = 0;
        for obj in lcg_objs(nvars, n_obj, rnd) {
            let s = Std::new(nvars, cons.len());
            let (a, b0) = s.build(&cons);
            let mut cost = vec![Rat::zero(); nvars];
            match &obj {
                None => {
                    for c in cost.iter_mut() {
                        *c = -Rat::one();
                    }
                }
                Some(o) => cost.clone_from_slice(o),
            }
            let (status, t, b, basis) = two_phase(&a, &b0, &cost);
            if status == Status::Infeasible {
                return (cons, true, cuts);
            }
            let x = primal(&s, &b, &basis);
            for (cut, recipe) in gomory_cuts(&s, &t, &b, &cons, &x) {
                let k = cut.key();
                if seen.insert(k) {
                    cons.push(cut);
                    cuts.push(recipe);
                    added += 1;
                }
            }
        }
        if added == 0 {
            return (cons, false, cuts);
        }
    }
    (cons, false, cuts)
}

// ── exact Farkas certificate ────────────────────────────────────────────────

/// Find nonneg integer multipliers over {cons, x_v<=1, x_v>=0} whose combination
/// is 0 >= positive (LP-infeasibility certificate).  Solved exactly via the LP
///   max Σ y·rhs  s.t.  Σ y·coef[i] = 0 ∀i,  Σ y <= 1,  y >= 0.
fn farkas(cons: &[Pb], nvars: usize) -> Option<Vec<FarkasTerm>> {
    // candidate constraints: cons, then (−x_v >= −1), then (x_v >= 0)
    let mut cands: Vec<Pb> = cons.to_vec();
    let n_con = cons.len();
    for v in 1..=nvars as u32 {
        let mut coef = BTreeMap::new();
        coef.insert(v, bi(-1));
        cands.push(Pb { coef, rhs: bi(-1) });
    }
    for v in 1..=nvars as u32 {
        let mut coef = BTreeMap::new();
        coef.insert(v, bi(1));
        cands.push(Pb { coef, rhs: bi(0) });
    }
    let k = cands.len();
    // LP variables: y_0..y_{k-1}, then a slack for Σy <= 1.  Rows: one equality
    // per problem variable (Σ y coef = 0) + the normalization row.
    let nrows = nvars + 1;
    let ncols = k + 1;
    let mut a = vec![vec![Rat::zero(); ncols]; nrows];
    let mut b0 = vec![Rat::zero(); nrows];
    for (kk, c) in cands.iter().enumerate() {
        for (&v, co) in &c.coef {
            a[(v - 1) as usize][kk] = Rat::from_integer(co.clone());
        }
        a[nvars][kk] = Rat::one(); // normalization Σ y + slack = 1
    }
    a[nvars][k] = Rat::one(); // slack column
    b0[nvars] = Rat::one();
    let mut cost = vec![Rat::zero(); ncols];
    for kk in 0..k {
        cost[kk] = -Rat::from_integer(cands[kk].rhs.clone()); // minimize −Σ y·rhs
    }
    let (status, _t, b, basis) = two_phase(&a, &b0, &cost);
    if status != Status::Optimal {
        return None;
    }
    // recover y* from the basis
    let mut y = vec![Rat::zero(); k];
    for i in 0..basis.len() {
        if basis[i] < k {
            y[basis[i]] = b[i].clone();
        }
    }
    let obj: Rat = (0..k)
        .map(|kk| &y[kk] * &Rat::from_integer(cands[kk].rhs.clone()))
        .fold(Rat::zero(), |acc, x| acc + x);
    if obj <= Rat::zero() {
        return None;
    }
    // clear denominators → integer multipliers
    let mut den = BigInt::one();
    for yi in &y {
        if !yi.is_zero() {
            den = den.lcm(yi.denom());
        }
    }
    let mult: Vec<BigInt> = y
        .iter()
        .map(|yi| (yi * Rat::from_integer(den.clone())).to_integer())
        .collect();
    let mut g = BigInt::zero();
    for m in &mult {
        g = g.gcd(m);
    }
    let mult: Vec<BigInt> = if g > BigInt::one() {
        mult.iter().map(|m| m / &g).collect()
    } else {
        mult
    };
    // verify EXACT cancellation: Σ mult·cand = 0 >= positive
    let mut acc: Option<Pb> = None;
    for (kk, m) in mult.iter().enumerate() {
        if m.is_zero() {
            continue;
        }
        let coef = cands[kk].coef.iter().map(|(&v, a)| (v, a * m)).collect();
        let term = Pb { coef, rhs: &cands[kk].rhs * m }.norm();
        acc = Some(match acc.take() {
            None => term,
            Some(g) => add_scaled(&g, &BigInt::one(), &term, &BigInt::one()),
        });
    }
    let acc = acc?;
    if !acc.is_contradiction() {
        return None;
    }
    // build provenance terms
    let mut terms = Vec::new();
    for (kk, m) in mult.iter().enumerate() {
        if m.is_zero() {
            continue;
        }
        if kk < n_con {
            terms.push(FarkasTerm::Con(kk, m.clone()));
        } else if kk < n_con + nvars {
            terms.push(FarkasTerm::Upper((kk - n_con + 1) as u32, m.clone()));
        } else {
            terms.push(FarkasTerm::Lower((kk - n_con - nvars + 1) as u32, m.clone()));
        }
    }
    Some(terms)
}

// ── top-level + emission ────────────────────────────────────────────────────

pub fn refute(
    clauses: &[Vec<i32>],
    nvars: usize,
    max_rounds: usize,
    n_obj: usize,
    max_secs: f64,
) -> Option<Refutation> {
    let inputs: Vec<Pb> = clauses.iter().map(|c| Pb::from_clause(c)).collect();
    let (cons, refuted, cuts) = gmi_loop(&inputs, nvars, max_rounds, n_obj, max_secs);
    if !refuted {
        return None;
    }
    let farkas = farkas(&cons, nvars)?;
    Some(Refutation {
        cuts,
        farkas,
        cons_len: inputs.len(),
    })
}

fn pol_terms(parts: &[(String, BigInt)], suffix: &str) -> String {
    let mut rp = String::from("pol ");
    let mut first = true;
    for (rf, lam) in parts {
        rp.push_str(&format!("{} {} *", rf, lam));
        if !first {
            rp.push_str(" +");
        }
        rp.push(' ');
        first = false;
    }
    rp.push_str(suffix);
    rp.push_str(" ;");
    rp
}

/// Emit the VeriPB proof for a refutation.  n_inputs = number of input clauses.
pub fn emit(n_inputs: usize, r: &Refutation) -> String {
    let mut lines = vec![
        "pseudo-Boolean proof version 3.0".to_string(),
        format!("f {};", n_inputs),
    ];
    for (d, lam_c, lam_l, lam_b) in &r.cuts {
        let mut parts: Vec<(String, BigInt)> = Vec::new();
        for (idx, lam) in lam_c {
            parts.push(((idx + 1).to_string(), lam.clone()));
        }
        for (v, lam) in lam_l {
            parts.push((format!("x{}", v), lam.clone()));
        }
        for (v, lam) in lam_b {
            parts.push((format!("~x{}", v), lam.clone()));
        }
        lines.push(pol_terms(&parts, &format!("{} d", d)));
    }
    let mut parts: Vec<(String, BigInt)> = Vec::new();
    for t in &r.farkas {
        match t {
            FarkasTerm::Con(idx, m) => parts.push(((idx + 1).to_string(), m.clone())),
            FarkasTerm::Lower(v, m) => parts.push((format!("x{}", v), m.clone())),
            FarkasTerm::Upper(v, m) => parts.push((format!("~x{}", v), m.clone())),
        }
    }
    lines.push(pol_terms(&parts, ""));
    lines.push("output NONE;".to_string());
    lines.push("conclusion UNSAT : -1;".to_string());
    lines.push("end pseudo-Boolean proof;".to_string());
    lines.join("\n") + "\n"
}
