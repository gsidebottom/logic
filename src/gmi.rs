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
//! Arithmetic is generic over a [`Scalar`] field, run fast-path first with a
//! plain `i128` rational ([`Q`]) and falling back to `BigRational` if that fails
//! to refute.  Soundness does NOT depend on the scalar: the i128 simplex only
//! *searches* for the cuts and the Farkas combination; the emitted proof is
//! reconstructed in exact `BigInt` and its Farkas step is checked to cancel
//! exactly, after which VeriPB verifies independently.  So an i128 overflow can
//! only cause a fallback, never an unsound proof.

use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};
use std::collections::BTreeMap;

fn bi(n: i64) -> BigInt {
    BigInt::from(n)
}
fn ceil_div(a: &BigInt, b: &BigInt) -> BigInt {
    // b > 0
    (a + b - BigInt::one()).div_floor(b)
}

fn igcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

// ── Scalar field: the simplex tableau entry type ─────────────────────────────

/// An ordered field with the bits the simplex + Gomory reader need.  Arithmetic
/// is by value (operands cloned); for `Q` that's a cheap `Copy`.
pub trait Scalar:
    Clone
    + PartialOrd
    + std::ops::Add<Output = Self>
    + std::ops::Sub<Output = Self>
    + std::ops::Mul<Output = Self>
    + std::ops::Div<Output = Self>
    + std::ops::Neg<Output = Self>
{
    fn zero() -> Self;
    fn one() -> Self;
    fn from_i64(n: i64) -> Self;
    fn from_bigint(n: &BigInt) -> Self;
    fn is_zero(&self) -> bool;
    fn frac(&self) -> Self;
    /// (numer, denom>0) as BigInt, reduced.
    fn ratio_bigint(&self) -> (BigInt, BigInt);
    fn to_f64(&self) -> f64;
}

/// Plain `i128` rational (kept reduced, denom > 0).  Arithmetic may wrap on
/// overflow — that is fine: see the module note (soundness is from the exact
/// BigInt reconstruction + VeriPB, and the iteration cap prevents runaway).
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Q {
    n: i128,
    d: i128,
}

impl Q {
    fn reduce(mut n: i128, mut d: i128) -> Q {
        if d == 0 {
            return Q { n: 0, d: 1 };
        }
        if d < 0 {
            n = -n;
            d = -d;
        }
        let g = igcd(n, d).max(1);
        Q { n: n / g, d: d / g }
    }
}

// Arithmetic wraps rather than panics on i128 overflow: a wrapped value can only
// make the i128 attempt FAIL (→ BigRational fallback), never an unsound proof.
impl std::ops::Add for Q {
    type Output = Q;
    fn add(self, o: Q) -> Q {
        Q::reduce(
            (self.n.wrapping_mul(o.d)).wrapping_add(o.n.wrapping_mul(self.d)),
            self.d.wrapping_mul(o.d),
        )
    }
}
impl std::ops::Sub for Q {
    type Output = Q;
    fn sub(self, o: Q) -> Q {
        Q::reduce(
            (self.n.wrapping_mul(o.d)).wrapping_sub(o.n.wrapping_mul(self.d)),
            self.d.wrapping_mul(o.d),
        )
    }
}
impl std::ops::Mul for Q {
    type Output = Q;
    fn mul(self, o: Q) -> Q {
        Q::reduce(self.n.wrapping_mul(o.n), self.d.wrapping_mul(o.d))
    }
}
impl std::ops::Div for Q {
    type Output = Q;
    fn div(self, o: Q) -> Q {
        Q::reduce(self.n.wrapping_mul(o.d), self.d.wrapping_mul(o.n))
    }
}
impl std::ops::Neg for Q {
    type Output = Q;
    fn neg(self) -> Q {
        Q {
            n: self.n.wrapping_neg(),
            d: self.d,
        }
    }
}
impl PartialOrd for Q {
    fn partial_cmp(&self, o: &Q) -> Option<std::cmp::Ordering> {
        // d > 0 for both
        Some((self.n.wrapping_mul(o.d)).cmp(&(o.n.wrapping_mul(self.d))))
    }
}
impl Scalar for Q {
    fn zero() -> Q {
        Q { n: 0, d: 1 }
    }
    fn one() -> Q {
        Q { n: 1, d: 1 }
    }
    fn from_i64(n: i64) -> Q {
        Q { n: n as i128, d: 1 }
    }
    fn from_bigint(n: &BigInt) -> Q {
        Q {
            n: n.to_i128().unwrap_or(0),
            d: 1,
        }
    }
    fn is_zero(&self) -> bool {
        self.n == 0
    }
    fn frac(&self) -> Q {
        Q::reduce(self.n.rem_euclid(self.d), self.d)
    }
    fn ratio_bigint(&self) -> (BigInt, BigInt) {
        (BigInt::from(self.n), BigInt::from(self.d))
    }
    fn to_f64(&self) -> f64 {
        self.n as f64 / self.d as f64
    }
}

impl Scalar for BigRational {
    fn zero() -> Self {
        <BigRational as Zero>::zero()
    }
    fn one() -> Self {
        <BigRational as One>::one()
    }
    fn from_i64(n: i64) -> Self {
        BigRational::from_integer(bi(n))
    }
    fn from_bigint(n: &BigInt) -> Self {
        BigRational::from_integer(n.clone())
    }
    fn is_zero(&self) -> bool {
        <BigRational as Zero>::is_zero(self)
    }
    fn frac(&self) -> Self {
        self.clone() - self.floor()
    }
    fn ratio_bigint(&self) -> (BigInt, BigInt) {
        (self.numer().clone(), self.denom().clone())
    }
    fn to_f64(&self) -> f64 {
        <BigRational as ToPrimitive>::to_f64(self).unwrap_or(0.0)
    }
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
/// `cost.len()` is the working column count (= each row's length).  An iteration
/// cap backstops termination (exact arithmetic + Bland always terminate; the cap
/// only matters if an i128 scalar wrapped — then we bail and fall back).
fn optimize<S: Scalar>(t: &mut [Vec<S>], b: &mut [S], basis: &mut [usize], cost: &[S]) {
    let nrows = basis.len();
    let ncols = cost.len();
    let maxit = 50_000 + 200 * (nrows + ncols);
    let mut it = 0usize;
    loop {
        it += 1;
        if it > maxit {
            return;
        }
        let cb: Vec<S> = (0..nrows).map(|i| cost[basis[i]].clone()).collect();
        // entering: lowest-index column with negative reduced cost (Bland)
        let mut enter = usize::MAX;
        for j in 0..ncols {
            let mut rc = cost[j].clone();
            for i in 0..nrows {
                if !cb[i].is_zero() {
                    rc = rc - cb[i].clone() * t[i][j].clone();
                }
            }
            if rc < S::zero() {
                enter = j;
                break;
            }
        }
        if enter == usize::MAX {
            return;
        }
        // leaving: min ratio b[i]/t[i][enter] over t[i][enter] > 0, Bland tie-break
        let mut leave = usize::MAX;
        let mut best: Option<S> = None;
        for i in 0..nrows {
            if t[i][enter] > S::zero() {
                let ratio = b[i].clone() / t[i][enter].clone();
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
            *x = x.clone() / piv.clone();
        }
        b[leave] = b[leave].clone() / piv.clone();
        for i in 0..nrows {
            if i != leave && !t[i][enter].is_zero() {
                let f = t[i][enter].clone();
                for j in 0..t[i].len() {
                    let d = f.clone() * t[leave][j].clone();
                    t[i][j] = t[i][j].clone() - d;
                }
                let d = f.clone() * b[leave].clone();
                b[i] = b[i].clone() - d;
            }
        }
        basis[leave] = enter;
    }
}

/// Two-phase exact simplex for {a·y = b0, y >= 0} minimizing cost·y (cost over
/// the structural columns).  Returns (status, tableau, rhs, basis) with the
/// tableau restricted to the structural columns (artificials dropped).
fn two_phase<S: Scalar>(
    a: &[Vec<S>],
    b0: &[S],
    cost: &[S],
) -> (Status, Vec<Vec<S>>, Vec<S>, Vec<usize>) {
    let nrows = a.len();
    let ncols = if nrows > 0 { a[0].len() } else { 0 };
    let total = ncols + nrows;
    let mut t: Vec<Vec<S>> = Vec::with_capacity(nrows);
    let mut b: Vec<S> = Vec::with_capacity(nrows);
    for i in 0..nrows {
        let mut row = a[i].clone();
        row.resize(total, S::zero());
        let mut bi_ = b0[i].clone();
        if bi_ < S::zero() {
            for x in row.iter_mut() {
                *x = -std::mem::replace(x, S::zero());
            }
            bi_ = -bi_;
        }
        row[ncols + i] = S::one(); // artificial
        t.push(row);
        b.push(bi_);
    }
    let mut basis: Vec<usize> = (0..nrows).map(|i| ncols + i).collect();
    // phase 1: minimize sum of artificials
    let mut cost1 = vec![S::zero(); total];
    for j in ncols..total {
        cost1[j] = S::one();
    }
    optimize(&mut t, &mut b, &mut basis, &cost1);
    let art_val: S = (0..nrows)
        .filter(|&i| basis[i] >= ncols)
        .map(|i| b[i].clone())
        .fold(S::zero(), |acc, x| acc + x);
    if art_val > S::zero() {
        return (Status::Infeasible, vec![], vec![], vec![]);
    }
    // drive artificials still basic (at 0) out of the basis
    for i in 0..nrows {
        if basis[i] >= ncols {
            if let Some(pc) = (0..ncols).find(|&j| !t[i][j].is_zero()) {
                let piv = t[i][pc].clone();
                for x in t[i].iter_mut() {
                    *x = x.clone() / piv.clone();
                }
                b[i] = b[i].clone() / piv.clone();
                for k in 0..nrows {
                    if k != i && !t[k][pc].is_zero() {
                        let f = t[k][pc].clone();
                        for j in 0..t[k].len() {
                            let d = f.clone() * t[i][j].clone();
                            t[k][j] = t[k][j].clone() - d;
                        }
                        let d = f.clone() * b[i].clone();
                        b[k] = b[k].clone() - d;
                    }
                }
                basis[i] = pc;
            }
        }
    }
    // drop redundant rows (artificial still basic on an all-zero row) + artificials
    let keep: Vec<usize> = (0..nrows).filter(|&i| basis[i] < ncols).collect();
    let mut t2: Vec<Vec<S>> = keep.iter().map(|&i| t[i][..ncols].to_vec()).collect();
    let mut b2: Vec<S> = keep.iter().map(|&i| b[i].clone()).collect();
    let mut basis2: Vec<usize> = keep.iter().map(|&i| basis[i]).collect();
    // phase 2: optimize the real objective
    let mut cost2 = vec![S::zero(); ncols];
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
    fn build<S: Scalar>(&self, cons: &[Pb]) -> (Vec<Vec<S>>, Vec<S>) {
        let nrows = self.m + self.n;
        let mut a = vec![vec![S::zero(); self.ncols]; nrows];
        let mut b = vec![S::zero(); nrows];
        for (j, c) in cons.iter().enumerate() {
            for (&v, co) in &c.coef {
                let cx = self.cx(v);
                a[j][cx] = a[j][cx].clone() + S::from_bigint(co);
            }
            a[j][self.cs(j)] = -S::one();
            b[j] = S::from_bigint(&c.rhs);
        }
        for v in 1..=self.n as u32 {
            let r = self.m + (v - 1) as usize;
            a[r][self.cx(v)] = S::one();
            a[r][self.ct(v)] = S::one();
            b[r] = S::one();
        }
        (a, b)
    }
}

fn primal<S: Scalar>(s: &Std, b: &[S], basis: &[usize]) -> Vec<S> {
    let mut x = vec![S::zero(); s.n];
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

/// frac of a tableau entry as (numer, denom) BigInt; both helpers in one place.
fn col_frac<S: Scalar>(e: &S) -> Option<(BigInt, BigInt)> {
    let f = e.frac();
    if f.is_zero() {
        None
    } else {
        Some(f.ratio_bigint())
    }
}

/// All distinct violated Gomory cuts from the fractional basic rows.
fn gomory_cuts<S: Scalar>(
    s: &Std,
    t: &[Vec<S>],
    b: &[S],
    cons: &[Pb],
    x: &[S],
) -> Vec<(Pb, Recipe)> {
    let mut out = Vec::new();
    let mut seen = std::collections::HashSet::new();
    for i in 0..b.len() {
        if b[i].frac().is_zero() {
            continue;
        }
        let row = &t[i];
        // collect (column-id, numer, denom) of every fractional entry, by kind
        let mut raw_l: Vec<(u32, BigInt, BigInt)> = Vec::new();
        let mut raw_c: Vec<(usize, BigInt, BigInt)> = Vec::new();
        let mut raw_b: Vec<(u32, BigInt, BigInt)> = Vec::new();
        let mut d = BigInt::one();
        for v in 1..=s.n as u32 {
            if let Some((fnum, fden)) = col_frac(&row[s.cx(v)]) {
                d = d.lcm(&fden);
                raw_l.push((v, fnum, fden));
            }
        }
        for j in 0..s.m {
            if let Some((fnum, fden)) = col_frac(&row[s.cs(j)]) {
                d = d.lcm(&fden);
                raw_c.push((j, fnum, fden));
            }
        }
        for v in 1..=s.n as u32 {
            if let Some((fnum, fden)) = col_frac(&row[s.ct(v)]) {
                d = d.lcm(&fden);
                raw_b.push((v, fnum, fden));
            }
        }
        if d.is_one() {
            continue;
        }
        // integer multiplier = frac · D = numer · (D / denom)
        let mul = |fnum: &BigInt, fden: &BigInt| fnum * (&d / fden);
        let lam_l: Vec<(u32, BigInt)> = raw_l.iter().map(|(v, n, dn)| (*v, mul(n, dn))).collect();
        let lam_c: Vec<(usize, BigInt)> = raw_c.iter().map(|(j, n, dn)| (*j, mul(n, dn))).collect();
        let lam_b: Vec<(u32, BigInt)> = raw_b.iter().map(|(v, n, dn)| (*v, mul(n, dn))).collect();
        let recipe: Recipe = (d, lam_c, lam_l, lam_b);
        let cut = build_cut(cons, &recipe);
        if cut.coef.is_empty() {
            continue;
        }
        // violation at x*: rhs − Σ coef·x*
        let mut viol = S::from_bigint(&cut.rhs);
        for (&v, a) in &cut.coef {
            viol = viol - S::from_bigint(a) * x[(v - 1) as usize].clone();
        }
        if viol <= S::zero() {
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

fn lcg_objs<S: Scalar>(n: usize, n_obj: usize, rnd: usize) -> Vec<Option<Vec<S>>> {
    let mut objs: Vec<Option<Vec<S>>> = vec![None]; // None = maximize Σx
    let mut seed: u64 = 0x9e3779b97f4a7c15u64 ^ (rnd as u64).wrapping_mul(0x100000001b3);
    for _ in 1..n_obj {
        let mut o = Vec::with_capacity(n);
        for _ in 0..n {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            o.push(S::from_i64(((seed >> 33) % 5) as i64 - 2)); // {−2..2}
        }
        objs.push(Some(o));
    }
    objs
}

/// Cutting-plane loop with Gomory separation.  Returns (cons, refuted, cuts).
fn gmi_loop<S: Scalar>(
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
        for obj in lcg_objs::<S>(nvars, n_obj, rnd) {
            let s = Std::new(nvars, cons.len());
            let (a, b0) = s.build::<S>(&cons);
            let mut cost = vec![S::zero(); nvars];
            match &obj {
                None => {
                    for c in cost.iter_mut() {
                        *c = -S::one();
                    }
                }
                Some(o) => cost.clone_from_slice(o),
            }
            let (status, t, b, basis) = two_phase::<S>(&a, &b0, &cost);
            if status == Status::Infeasible {
                return (cons, true, cuts);
            }
            let x = primal::<S>(&s, &b, &basis);
            for (cut, recipe) in gomory_cuts::<S>(&s, &t, &b, &cons, &x) {
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

// ── warm-start cutting-plane loop (dual simplex after each cut) ──────────────
//
// The cold loop above re-solves the whole growing system from scratch every
// round × objective.  Warm-start keeps ONE persistent tableau: after adding a cut
// (one row + one slack), the old optimal basis is dual-feasible but primal-
// infeasible only in the new row → a few DUAL-simplex pivots restore optimality
// (vs a full two-phase).  An objective rotation keeps primal feasibility → a
// PRIMAL re-optimize (no phase 1).  Soundness is unaffected: this only changes
// how cuts/Farkas are found; the proof is still BigInt-exact + veripb-checked,
// with the cold path as the ultimate fallback.

#[derive(Clone, Copy)]
enum ColKind {
    X(u32),       // original var x_v        → multiplier on the x_v >= 0 axiom
    Slack(usize), // surplus of cons[idx]    → multiplier on cons[idx]
    Upper(u32),   // slack of x_v <= 1       → multiplier on the ~x_v axiom
}

/// Standard pivot on (r, enter): normalize row r, eliminate the column elsewhere.
fn pivot<S: Scalar>(t: &mut [Vec<S>], b: &mut [S], basis: &mut [usize], r: usize, enter: usize) {
    let piv = t[r][enter].clone();
    for x in t[r].iter_mut() {
        *x = x.clone() / piv.clone();
    }
    b[r] = b[r].clone() / piv.clone();
    for i in 0..basis.len() {
        if i != r && !t[i][enter].is_zero() {
            let f = t[i][enter].clone();
            for j in 0..t[i].len() {
                let d = f.clone() * t[r][j].clone();
                t[i][j] = t[i][j].clone() - d;
            }
            let d = f.clone() * b[r].clone();
            b[i] = b[i].clone() - d;
        }
    }
    basis[r] = enter;
}

/// Learned cut-selection scorer — effective weights (w/sd) from cp_gmi_policy.py
/// (imitation on php-3-2/4-3/5-4; only the ratio matters for ranking).  Features:
/// [viol, D, nsrc, nbound, msum, degree, ncoef, maxc, density].  Higher = keep.
const CUT_W: [f64; 9] = [
    4.673984, -0.039576, -0.375185, -1.467375, -0.006227, -0.096239, -0.027566,
    -2.697505, -1.084399,
];

fn cut_score(cut: &Pb, recipe: &Recipe, viol: f64, nvars: usize) -> f64 {
    let (d, lam_c, lam_l, lam_b) = recipe;
    let fb = |x: &BigInt| x.to_f64().unwrap_or(0.0);
    let msum: f64 = lam_c.iter().map(|(_, m)| fb(m)).sum::<f64>()
        + lam_l.iter().map(|(_, m)| fb(m)).sum::<f64>()
        + lam_b.iter().map(|(_, m)| fb(m)).sum::<f64>();
    let degree = fb(&cut.rhs).abs();
    let ncoef = cut.coef.len() as f64;
    let maxc = cut.coef.values().map(|a| fb(a).abs()).fold(0.0, f64::max);
    let feats = [
        viol,
        fb(d),
        lam_c.len() as f64,
        (lam_l.len() + lam_b.len()) as f64,
        msum,
        degree,
        ncoef,
        maxc,
        ncoef / (nvars.max(1) as f64),
    ];
    feats.iter().zip(CUT_W.iter()).map(|(f, w)| f * w).sum()
}

struct Warm<S> {
    t: Vec<Vec<S>>,
    b: Vec<S>,
    basis: Vec<usize>,
    kind: Vec<ColKind>,
    cost: Vec<S>,
    ncols: usize,
    nvars: usize,
}

impl<S: Scalar> Warm<S> {
    fn from_cold(s: &Std, t: Vec<Vec<S>>, b: Vec<S>, basis: Vec<usize>, cost: Vec<S>, nvars: usize) -> Warm<S> {
        let mut kind = Vec::with_capacity(s.ncols);
        for v in 1..=s.n as u32 {
            kind.push(ColKind::X(v)); // cols 0..n-1
        }
        for j in 0..s.m {
            kind.push(ColKind::Slack(j)); // cols n..n+m-1 (input constraint j)
        }
        for v in 1..=s.n as u32 {
            kind.push(ColKind::Upper(v)); // cols n+m..2n+m-1
        }
        Warm { t, b, basis, kind, cost, ncols: s.ncols, nvars }
    }

    fn primal_x(&self) -> Vec<S> {
        let mut x = vec![S::zero(); self.nvars];
        for i in 0..self.basis.len() {
            if let ColKind::X(v) = self.kind[self.basis[i]] {
                x[(v - 1) as usize] = self.b[i].clone();
            }
        }
        x
    }

    /// Append cut (= cons[ci]) as a new row + surplus column, expressed in the
    /// current basis so the new slack is basic with a negative value (the cut is
    /// violated → primal-infeasible row, ready for the dual simplex).
    fn add_cut(&mut self, cut: &Pb, ci: usize) {
        let snew = self.ncols;
        for row in self.t.iter_mut() {
            row.push(S::zero());
        }
        self.kind.push(ColKind::Slack(ci));
        self.cost.push(S::zero());
        self.ncols += 1;
        let mut nr = vec![S::zero(); self.ncols];
        for (&v, g) in &cut.coef {
            nr[(v - 1) as usize] = S::from_bigint(g);
        }
        nr[snew] = -S::one();
        let mut rhs = S::from_bigint(&cut.rhs);
        for i in 0..self.basis.len() {
            let c = self.basis[i];
            if !nr[c].is_zero() {
                let g = nr[c].clone();
                for j in 0..self.ncols {
                    let d = g.clone() * self.t[i][j].clone();
                    nr[j] = nr[j].clone() - d;
                }
                rhs = rhs - g.clone() * self.b[i].clone();
            }
        }
        for x in nr.iter_mut() {
            *x = -std::mem::replace(x, S::zero()); // ×−1 → s_new basic with +1
        }
        self.t.push(nr);
        self.b.push(-rhs);
        self.basis.push(snew);
    }

    /// Dual simplex: restore primal feasibility from a dual-feasible basis.
    /// Returns Infeasible when an infeasible row has no eligible entering column
    /// (LP infeasible → refuted).
    fn dual_resolve(&mut self) -> Status {
        let cap = 50_000 + 200 * (self.basis.len() + self.ncols);
        let mut it = 0usize;
        loop {
            it += 1;
            if it > cap {
                return Status::Optimal; // bail; the cold fallback covers it
            }
            // leaving row: Bland — smallest basic-var index among b[r] < 0
            let mut leave = usize::MAX;
            let mut leave_bi = usize::MAX;
            for r in 0..self.basis.len() {
                if self.b[r] < S::zero() && self.basis[r] < leave_bi {
                    leave_bi = self.basis[r];
                    leave = r;
                }
            }
            if leave == usize::MAX {
                return Status::Optimal; // primal feasible → optimal
            }
            let cb: Vec<S> = (0..self.basis.len()).map(|i| self.cost[self.basis[i]].clone()).collect();
            // entering: min reduced-cost / (−t[leave][j]) over t[leave][j] < 0
            let mut enter = usize::MAX;
            let mut best: Option<S> = None;
            for j in 0..self.ncols {
                if self.t[leave][j] < S::zero() {
                    let mut rc = self.cost[j].clone();
                    for i in 0..self.basis.len() {
                        if !cb[i].is_zero() {
                            rc = rc - cb[i].clone() * self.t[i][j].clone();
                        }
                    }
                    let ratio = rc / (-self.t[leave][j].clone());
                    if best.as_ref().map_or(true, |bv| ratio < *bv) {
                        best = Some(ratio);
                        enter = j;
                    }
                }
            }
            if enter == usize::MAX {
                return Status::Infeasible; // primal infeasible → REFUTED
            }
            pivot(&mut self.t, &mut self.b, &mut self.basis, leave, enter);
        }
    }

    /// All distinct violated Gomory cuts from the current optimal tableau,
    /// routing each fractional column to its multiplier by `kind`.
    fn read_cuts(&self, cons: &[Pb], seen: &std::collections::HashSet<String>) -> Vec<(Pb, Recipe, f64)> {
        let x = self.primal_x();
        let mut out = Vec::new();
        let mut local = std::collections::HashSet::new();
        for i in 0..self.basis.len() {
            if self.b[i].frac().is_zero() {
                continue;
            }
            let mut raw: Vec<(usize, BigInt, BigInt)> = Vec::new();
            let mut d = BigInt::one();
            for col in 0..self.ncols {
                if let Some((n, dn)) = col_frac(&self.t[i][col]) {
                    d = d.lcm(&dn);
                    raw.push((col, n, dn));
                }
            }
            if d.is_one() {
                continue;
            }
            let mul = |n: &BigInt, dn: &BigInt| n * (&d / dn);
            let mut lam_l = Vec::new();
            let mut lam_c = Vec::new();
            let mut lam_b = Vec::new();
            for (col, n, dn) in &raw {
                let lam = mul(n, dn);
                match self.kind[*col] {
                    ColKind::X(v) => lam_l.push((v, lam)),
                    ColKind::Slack(ci) => lam_c.push((ci, lam)),
                    ColKind::Upper(v) => lam_b.push((v, lam)),
                }
            }
            let recipe: Recipe = (d, lam_c, lam_l, lam_b);
            let cut = build_cut(cons, &recipe);
            if cut.coef.is_empty() {
                continue;
            }
            let mut viol = S::from_bigint(&cut.rhs);
            for (&v, a) in &cut.coef {
                viol = viol - S::from_bigint(a) * x[(v - 1) as usize].clone();
            }
            if viol <= S::zero() {
                continue;
            }
            let k = cut.key();
            if seen.contains(&k) || !local.insert(k) {
                continue;
            }
            out.push((cut, recipe, viol.to_f64()));
        }
        out
    }
}

fn one_obj<S: Scalar>(n: usize, idx: usize) -> Vec<S> {
    let mut seed = 0x9e3779b97f4a7c15u64 ^ (idx as u64).wrapping_mul(0x100000001b3);
    (0..n)
        .map(|_| {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            S::from_i64(((seed >> 33) % 5) as i64 - 2)
        })
        .collect()
}

fn gmi_loop_warm<S: Scalar>(
    inputs: &[Pb],
    nvars: usize,
    max_rounds: usize,
    n_obj: usize,
    max_secs: f64,
    topfrac: f64,
) -> (Vec<Pb>, bool, Vec<Recipe>) {
    let start = std::time::Instant::now();
    let mut cons: Vec<Pb> = inputs.to_vec();
    // one cold solve for the initial optimal basis (default objective: maximize Σx)
    let s = Std::new(nvars, inputs.len());
    let (a, b0) = s.build::<S>(&cons);
    let mut cost0 = vec![S::zero(); s.ncols];
    for v in 1..=nvars as u32 {
        cost0[s.cx(v)] = -S::one();
    }
    let (status, t, b, basis) = two_phase::<S>(&a, &b0, &cost0);
    if status == Status::Infeasible {
        return (cons, true, Vec::new()); // inputs already LP-infeasible
    }
    let mut warm = Warm::from_cold(&s, t, b, basis, cost0, nvars);
    let mut cuts: Vec<Recipe> = Vec::new();
    let mut seen: std::collections::HashSet<String> = cons.iter().map(|c| c.key()).collect();
    let mut stale = 0usize;
    let mut rot = 0usize;
    for _ in 0..max_rounds * n_obj.max(1) {
        if max_secs > 0.0 && start.elapsed().as_secs_f64() > max_secs {
            return (cons, false, cuts);
        }
        let mut fresh = warm.read_cuts(&cons, &seen);
        if !fresh.is_empty() {
            stale = 0;
            if topfrac < 1.0 && fresh.len() > 1 {
                // learned selection: keep the top-scored fraction this round
                let mut scored: Vec<(f64, (Pb, Recipe, f64))> = fresh
                    .into_iter()
                    .map(|x| (cut_score(&x.0, &x.1, x.2, nvars), x))
                    .collect();
                scored.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap_or(std::cmp::Ordering::Equal));
                let keep = ((scored.len() as f64 * topfrac).round() as usize).max(1);
                fresh = scored.into_iter().take(keep).map(|(_, x)| x).collect();
            }
            for (cut, recipe, _viol) in fresh {
                let k = cut.key();
                if !seen.insert(k) {
                    continue;
                }
                let ci = cons.len();
                cons.push(cut.clone());
                cuts.push(recipe);
                warm.add_cut(&cut, ci);
            }
            if warm.dual_resolve() == Status::Infeasible {
                return (cons, true, cuts);
            }
        } else {
            stale += 1;
            if stale >= n_obj {
                return (cons, false, cuts);
            }
            rot += 1;
            let obj = one_obj::<S>(nvars, rot);
            for c in warm.cost.iter_mut() {
                *c = S::zero();
            }
            for v in 1..=nvars as u32 {
                warm.cost[s.cx(v)] = obj[(v - 1) as usize].clone();
            }
            let cost = warm.cost.clone();
            optimize(&mut warm.t, &mut warm.b, &mut warm.basis, &cost); // primal re-opt
        }
    }
    (cons, false, cuts)
}

// ── exact Farkas certificate ────────────────────────────────────────────────

/// Find nonneg integer multipliers over {cons, x_v<=1, x_v>=0} whose combination
/// is 0 >= positive (LP-infeasibility certificate).  Solved exactly via the LP
///   max Σ y·rhs  s.t.  Σ y·coef[i] = 0 ∀i,  Σ y <= 1,  y >= 0.
fn farkas<S: Scalar>(cons: &[Pb], nvars: usize) -> Option<Vec<FarkasTerm>> {
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
    let mut a = vec![vec![S::zero(); ncols]; nrows];
    let mut b0 = vec![S::zero(); nrows];
    for (kk, c) in cands.iter().enumerate() {
        for (&v, co) in &c.coef {
            a[(v - 1) as usize][kk] = S::from_bigint(co);
        }
        a[nvars][kk] = S::one(); // normalization Σ y + slack = 1
    }
    a[nvars][k] = S::one(); // slack column
    b0[nvars] = S::one();
    let mut cost = vec![S::zero(); ncols];
    for kk in 0..k {
        cost[kk] = -S::from_bigint(&cands[kk].rhs); // minimize −Σ y·rhs
    }
    let (status, _t, b, basis) = two_phase::<S>(&a, &b0, &cost);
    if status != Status::Optimal {
        return None;
    }
    // recover y* from the basis
    let mut y = vec![S::zero(); k];
    for i in 0..basis.len() {
        if basis[i] < k {
            y[basis[i]] = b[i].clone();
        }
    }
    let obj: S = (0..k)
        .map(|kk| y[kk].clone() * S::from_bigint(&cands[kk].rhs))
        .fold(S::zero(), |acc, x| acc + x);
    if obj <= S::zero() {
        return None;
    }
    // clear denominators → integer multipliers
    let mut den = BigInt::one();
    for yi in &y {
        if !yi.is_zero() {
            let (_, dd) = yi.ratio_bigint();
            den = den.lcm(&dd);
        }
    }
    let mult: Vec<BigInt> = y
        .iter()
        .map(|yi| {
            let (nn, dd) = yi.ratio_bigint();
            nn * (&den / &dd)
        })
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

fn refute_with<S: Scalar>(
    inputs: &[Pb],
    nvars: usize,
    max_rounds: usize,
    n_obj: usize,
    max_secs: f64,
) -> Option<Refutation> {
    let (cons, refuted, cuts) = gmi_loop::<S>(inputs, nvars, max_rounds, n_obj, max_secs);
    if !refuted {
        return None;
    }
    let farkas = farkas::<S>(&cons, nvars)?;
    Some(Refutation {
        cuts,
        farkas,
        cons_len: inputs.len(),
    })
}

fn refute_warm<S: Scalar>(
    inputs: &[Pb],
    nvars: usize,
    max_rounds: usize,
    n_obj: usize,
    max_secs: f64,
    topfrac: f64,
) -> Option<Refutation> {
    let (cons, refuted, cuts) = gmi_loop_warm::<S>(inputs, nvars, max_rounds, n_obj, max_secs, topfrac);
    if !refuted {
        return None;
    }
    let farkas = farkas::<S>(&cons, nvars)?;
    Some(Refutation {
        cuts,
        farkas,
        cons_len: inputs.len(),
    })
}

/// Refute `clauses` by Gomory cutting planes.  Fast path: warm-start (dual
/// simplex) on i128 rationals.  On failure (overflow, warm-start bug, or limit)
/// falls back to the trusted cold-start `BigRational` engine.  Either way the
/// returned proof is BigInt-exact (its Farkas step is verified to cancel) and
/// VeriPB-checkable.
pub fn refute(
    clauses: &[Vec<i32>],
    nvars: usize,
    max_rounds: usize,
    n_obj: usize,
    max_secs: f64,
) -> Option<Refutation> {
    let inputs: Vec<Pb> = clauses.iter().map(|c| Pb::from_clause(c)).collect();
    refute_warm::<Q>(&inputs, nvars, max_rounds, n_obj, max_secs, 1.0)
        .or_else(|| refute_with::<BigRational>(&inputs, nvars, max_rounds, n_obj, max_secs))
}

/// Like [`refute`] but with the learned cut-selection policy: each round keep
/// only the top `topfrac` of violated cuts by [`cut_score`].  Fewer cuts ⇒
/// smaller proof + smaller growing system.  Falls back to cold add-all on miss.
pub fn refute_policy(
    clauses: &[Vec<i32>],
    nvars: usize,
    max_rounds: usize,
    n_obj: usize,
    max_secs: f64,
    topfrac: f64,
) -> Option<Refutation> {
    let inputs: Vec<Pb> = clauses.iter().map(|c| Pb::from_clause(c)).collect();
    refute_warm::<Q>(&inputs, nvars, max_rounds, n_obj, max_secs, topfrac)
        .or_else(|| refute_with::<BigRational>(&inputs, nvars, max_rounds, n_obj, max_secs))
}

/// Cold-start engine (no warm-start) — i128 then BigRational.  For A/B timing.
pub fn refute_cold(
    clauses: &[Vec<i32>],
    nvars: usize,
    max_rounds: usize,
    n_obj: usize,
    max_secs: f64,
) -> Option<Refutation> {
    let inputs: Vec<Pb> = clauses.iter().map(|c| Pb::from_clause(c)).collect();
    refute_with::<Q>(&inputs, nvars, max_rounds, n_obj, max_secs)
        .or_else(|| refute_with::<BigRational>(&inputs, nvars, max_rounds, n_obj, max_secs))
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
