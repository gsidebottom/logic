//! kres: k-subset re-solve of an F2 matrix-multiplication scheme -- candidates and exact decisions.
//!
//! Drop k products of a scheme and ask whether their sum R (a tensor of rank at most k)
//! can be rewritten with k-1 products (a scheme of rank r-1) or with k different ones
//! (another scheme of rank r, possibly in a new equivalence class).  The rank of R is at
//! least each of its three flattening ranks; the c-flattening has rank k unless the k
//! c-factors are dependent or the k Kronecker products a_t (x) b_t are dependent (the
//! image of the flattening is U_ab applied to the row space of C), and likewise for a and
//! b.  So a rewrite with k-1 products needs, in every slot, dependent factors or
//! dependent Kronecker products of the other two slots ("R" candidates).  By Kruskal's
//! theorem a k-term decomposition whose factor matrices have Kruskal ranks summing to at
//! least 2k+2 is unique; for a scheme without repeated factors that holds as soon as two
//! slots are independent, so an alternative needs dependent factors in at least two slots
//! ("A" candidates).
//!
//! Exact decision (--decide, --lines, --subset).  Fix a direction and let S be its slice
//! space (dimension m = the flattening rank), a space of nr x nc matrices over the other
//! two slots.  A decomposition of R with d terms is the same thing as a space W with
//! S <= W, dim W <= d, spanned by its rank-one elements: the Kronecker matrices of the
//! terms span such a W, and a rank-one basis M_i of any such W gives R = sum_i M_i (x) w_i
//! with w_i read off from the coordinates of the slices.  (Restricting to the factor spans
//! loses nothing: projecting a decomposition onto the spans fixes R and keeps terms
//! rank-one.)  So:
//!   * m == target: W = S, decided by whether the rank-one elements of S span S (reduce)
//!     or whether S has more than k rank-one elements (alt: another rank-one basis);
//!   * m < target ("deficient", delta = target - m): W = S + <N_1, ..., N_delta> with
//!     rank-one N_i.  For delta = 1 the N are confined: W is spanned only if some N + s
//!     (s in S, s != 0) is rank-one too, and s must lie outside the span S' of the
//!     rank-one elements of S to add anything, so s = N + N' is a rank-two element of S
//!     outside S' and N is one of its six two-term rank-one splits; the exact test is
//!     S' + span{s in S : N + s rank-one} = S.
//!     For delta >= 2 the first N runs over every rank-one matrix outside S and the rest
//!     recurse; the cost is (2^nr - 1)(2^nc - 1) analyses of an (m+1)-dimensional space.
//!   Alternatives in the deficient case: some W other than the original space U, or U with
//!   more than k rank-one elements.
//! Every YES verdict comes with the new products (ambient bit strings) and is verified
//! against the tensor of the dropped products ("verified=1").
//!
//! usage: kres N1 N2 N3 scheme.bits --kmin 3 --kmax 8 [--threads 12] [--out FILE]
//!        [--both]   (print A candidates too; default prints R candidates only)
//!        [--decide] decide each candidate on the fly.  R candidates: "RED" (reducible, with
//!                   the new products) or refuted (counted) or "R" (open: delta beyond
//!                   --maxdelta, default 2).  A candidates and, with --both, the R candidates
//!                   too: "ALT" (another k-term decomposition, with its products), unique
//!                   (counted) or "A" (open: delta beyond --maxdelta-alt, default 1).
//!        kres N1 N2 N3 scheme.bits --lines FILE [--mode reduce|alt|both] [--threads 12] [--out FILE]
//!                   decide the R / A lines of FILE (k and idx= are read from each line).
//!        kres N1 N2 N3 scheme.bits --subset 0,3,17,...   one candidate, verbose.
//! bits layout: all a factors (n1*n2 bits each), then all b (n2*n3), then all c (n1*n3).
use std::io::Write;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

type Prod = [u32; 3];
type Wide = [u64; 4]; // a Kronecker product of two 16-bit factors, 256 bits

fn kron(x: u32, y: u32, wy: usize) -> Wide {
    // bit i*wy + j = x_i y_j
    let mut w: Wide = [0; 4];
    for i in 0..32 {
        if (x >> i) & 1 == 1 {
            let base = i * wy;
            for j in 0..wy {
                if (y >> j) & 1 == 1 {
                    let b = base + j;
                    w[b / 64] |= 1u64 << (b % 64);
                }
            }
        }
    }
    w
}

fn wide_lead(w: &Wide) -> i32 {
    for q in (0..4).rev() {
        if w[q] != 0 { return (q as i32) * 64 + 63 - w[q].leading_zeros() as i32; }
    }
    -1
}

#[derive(Clone)]
struct WBasis { v: Vec<Wide> } // echelon by leading bit, descending
impl WBasis {
    fn new() -> Self { WBasis { v: Vec::with_capacity(8) } }
    fn reduce(&self, mut x: Wide) -> Wide {
        for b in &self.v {
            let l = wide_lead(b);
            if l >= 0 && (x[(l / 64) as usize] >> (l % 64)) & 1 == 1 {
                for q in 0..4 { x[q] ^= b[q]; }
            }
        }
        x
    }
    fn insert(&mut self, x: Wide) {
        let l = wide_lead(&x);
        let pos = self.v.iter().position(|b| wide_lead(b) < l).unwrap_or(self.v.len());
        self.v.insert(pos, x);
    }
}

#[derive(Clone)]
struct Basis {
    v: Vec<u32>, // echelon: distinct leading bits, sorted by leading bit descending
}
impl Basis {
    fn new() -> Self { Basis { v: Vec::with_capacity(16) } }
    /// reduce x against the basis; a zero result means x is in the span
    fn reduce(&self, mut x: u32) -> u32 {
        for &b in &self.v {
            let lead = 31 - b.leading_zeros();
            if (x >> lead) & 1 == 1 { x ^= b; }
        }
        x
    }
    fn insert(&mut self, x: u32) {
        let lead = 31 - x.leading_zeros();
        let pos = self.v.iter().position(|&b| (31 - b.leading_zeros()) < lead).unwrap_or(self.v.len());
        self.v.insert(pos, x);
    }
    fn dim(&self) -> usize { self.v.len() }
}

fn arg_val<T: std::str::FromStr>(args: &[String], key: &str) -> Option<T> {
    args.iter().position(|a| a == key).and_then(|i| args.get(i + 1)).and_then(|s| s.parse().ok())
}

fn load(path: &str, n1: usize, n2: usize, n3: usize) -> Vec<Prod> {
    let txt = std::fs::read_to_string(path).expect("read scheme");
    let bits: Vec<u8> = txt.split_whitespace().last().unwrap().bytes().map(|b| b - b'0').collect();
    let (sa, sb, sg) = (n1 * n2, n2 * n3, n1 * n3);
    let per = sa + sb + sg;
    assert!(bits.len() % per == 0, "bits length {} not a multiple of {}", bits.len(), per);
    let r = bits.len() / per;
    let mut out = Vec::with_capacity(r);
    for m in 0..r {
        let mut p: Prod = [0, 0, 0];
        for k in 0..sa { p[0] |= (bits[m * sa + k] as u32) << k; }
        for k in 0..sb { p[1] |= (bits[r * sa + m * sb + k] as u32) << k; }
        for k in 0..sg { p[2] |= (bits[r * sa + r * sb + m * sg + k] as u32) << k; }
        out.push(p);
    }
    out
}

/// F2 vectors with coordinate tracking: add(v) returns v's coordinates (a mask over the basis
/// elements, which are the original vectors that were independent when added).
struct Coord { ech: Vec<(u32, u32)>, basis: Vec<u32> }
impl Coord {
    fn new() -> Self { Coord { ech: Vec::new(), basis: Vec::new() } }
    fn add(&mut self, v: u32) -> u32 {
        let (mut x, mut m) = (v, 0u32);
        for &(e, em) in &self.ech {
            let lead = 31 - e.leading_zeros();
            if (x >> lead) & 1 == 1 { x ^= e; m ^= em; }
        }
        if x == 0 { return m; }
        let idx = self.basis.len();
        self.basis.push(v);
        let mask = m ^ (1u32 << idx);
        let lead = 31 - x.leading_zeros();
        let pos = self.ech.iter().position(|&(e, _)| (31 - e.leading_zeros()) < lead).unwrap_or(self.ech.len());
        self.ech.insert(pos, (x, mask));
        1u32 << idx
    }
    /// the ambient vector with these coordinates
    fn ambient(&self, mask: u32) -> u32 {
        let mut v = 0u32;
        for (j, &b) in self.basis.iter().enumerate() { if (mask >> j) & 1 == 1 { v ^= b; } }
        v
    }
}

/// the same for matrix bitmasks (u128), coordinates over at most 32 basis elements
struct Coord128 { ech: Vec<(u128, u32)>, n: usize }
impl Coord128 {
    fn new() -> Self { Coord128 { ech: Vec::new(), n: 0 } }
    /// Some(coordinates) if v is in the span, else None after adding v as a new basis element
    fn add(&mut self, v: u128) -> Option<u32> {
        let (mut x, mut m) = (v, 0u32);
        for &(e, em) in &self.ech {
            let l = lead128(e);
            if (x >> l) & 1 == 1 { x ^= e; m ^= em; }
        }
        if x == 0 { return Some(m); }
        let idx = self.n; self.n += 1;
        let mask = m ^ (1u32 << idx);
        let l = lead128(x);
        let pos = self.ech.iter().position(|&(e, _)| lead128(e) < l).unwrap_or(self.ech.len());
        self.ech.insert(pos, (x, mask));
        None
    }
}

fn lead128(x: u128) -> i32 { if x == 0 { -1 } else { 127 - x.leading_zeros() as i32 } }

/// rank over F2 of u128 vectors, and the echelon basis (leading bits descending)
fn echelon128(vs: &[u128]) -> Vec<u128> {
    let mut ech: Vec<u128> = Vec::new();
    for &v in vs { insert128_into(&mut ech, v); }
    ech
}

fn reduce128(ech: &[u128], mut x: u128) -> u128 {
    for &e in ech {
        let l = lead128(e);
        if (x >> l) & 1 == 1 { x ^= e; }
    }
    x
}

/// add v to an echelon basis (no-op when v is in the span)
fn insert128_into(ech: &mut Vec<u128>, v: u128) {
    let x = reduce128(ech, v);
    if x != 0 {
        let l = lead128(x);
        let pos = ech.iter().position(|&e| lead128(e) < l).unwrap_or(ech.len());
        ech.insert(pos, x);
    }
}

fn insert128(ech: &[u128], v: u128) -> Vec<u128> {
    let mut e = ech.to_vec();
    insert128_into(&mut e, v);
    e
}

fn same_space(a: &[u128], b: &[u128]) -> bool {
    a.len() == b.len() && a.iter().all(|&x| reduce128(b, x) == 0)
}

/// Kronecker product of two small coordinate vectors as a matrix bitmask, bit v*nc + w = y_v z_w
fn kron_small(y: u32, z: u32, nc: usize) -> u128 {
    let mut m: u128 = 0;
    let zz = z as u128;
    for v in 0..32 {
        if (y >> v) & 1 == 1 { m |= zz << (v * nc); }
    }
    m
}

/// a matrix bitmask has rank one iff its nonzero rows are all equal
fn is_rank1(m: u128, nr: usize, nc: usize) -> bool {
    let rowmask: u128 = (1u128 << nc) - 1;
    let mut first: u128 = 0;
    for i in 0..nr {
        let r = (m >> (i * nc)) & rowmask;
        if r != 0 {
            if first == 0 { first = r; } else if r != first { return false; }
        }
    }
    first != 0
}

/// min(rank, 3) of an nr x nc matrix bitmask
fn rank_le3(m: u128, nr: usize, nc: usize) -> u8 {
    let rowmask: u128 = (1u128 << nc) - 1;
    let (mut u, mut v) = (0u128, 0u128);
    for i in 0..nr {
        let r = (m >> (i * nc)) & rowmask;
        if r == 0 { continue; }
        if u == 0 { u = r; continue; }
        if r == u { continue; }
        if v == 0 { v = r; continue; }
        if r == v || r == (u ^ v) { continue; }
        return 3;
    }
    if u == 0 { 0 } else if v == 0 { 1 } else { 2 }
}

/// (row indicator x, common row y) of a rank-one matrix: m = x (x) y
fn rank1_factors(m: u128, nr: usize, nc: usize) -> (u32, u32) {
    let rowmask: u128 = (1u128 << nc) - 1;
    let (mut x, mut y) = (0u32, 0u32);
    for i in 0..nr {
        let r = (m >> (i * nc)) & rowmask;
        if r != 0 { x |= 1 << i; y = r as u32; }
    }
    (x, y)
}

/// the six rank-one matrices N with N + N' = s for a rank-2 matrix s (three bases {p,q} of the row
/// space; the rows of s are 0, p, q or p+q, and s = x_p (x) p + x_q (x) q with x_p the rows containing p)
fn rank2_splits(s: u128, nr: usize, nc: usize, out: &mut Vec<u128>) {
    let rowmask: u128 = (1u128 << nc) - 1;
    let (mut u, mut v) = (0u128, 0u128);
    for i in 0..nr {
        let r = (s >> (i * nc)) & rowmask;
        if r == 0 { continue; }
        if u == 0 { u = r; } else if r != u { v = r; break; }
    }
    for (p, q) in [(u, v), (u, u ^ v), (v, u ^ v)] {
        let (mut xp, mut xq) = (0u32, 0u32);
        for i in 0..nr {
            let r = (s >> (i * nc)) & rowmask;
            if r == p || r == (p ^ q) { xp |= 1 << i; }
            if r == q || r == (p ^ q) { xq |= 1 << i; }
        }
        out.push(kron_small(xp, p as u32, nc));
        out.push(kron_small(xq, q as u32, nc));
    }
}

/// a space of nr x nc matrices with its rank-one and rank-two elements
struct Space { ech: Vec<u128>, r1: Vec<u128>, r2: Vec<u128>, spanned: bool }

fn analyze(ech: Vec<u128>, nr: usize, nc: usize) -> Space {
    let m = ech.len();
    let (mut r1, mut r2) = (Vec::new(), Vec::new());
    let mut cur: u128 = 0;
    for j in 1u64..(1u64 << m) {
        cur ^= ech[j.trailing_zeros() as usize];
        match rank_le3(cur, nr, nc) { 1 => r1.push(cur), 2 => r2.push(cur), _ => {} }
    }
    let spanned = echelon128(&r1).len() == m;
    Space { ech, r1, r2, spanned }
}

/// Visit every space W >= S (sp) with dim W <= dim S + delta that is spanned by its rank-one elements,
/// in the forms S, S + <N>, S + <N, N'>, ...  visit returns true to stop; the result says whether it stopped.
fn search_w(sp: &Space, nr: usize, nc: usize, delta: usize, visit: &mut dyn FnMut(&[u128]) -> bool) -> bool {
    if sp.spanned { return visit(&sp.ech); }
    if delta == 0 { return false; }
    if delta == 1 {
        // S' = span of the rank-one elements of S, a proper subspace here.  W = S + <N> is spanned by its rank-one
        // elements iff S' + span{s in S : N + s rank-one} = S.  The s that can add anything lie outside S', so they
        // are rank-two elements of S outside S', and N is one of the six two-term splits of such an s (the
        // candidates derived from rank-one elements of S are redundant: a working N is adjacent to some rank-two s).
        let m = sp.ech.len();
        let sp_ech = echelon128(&sp.r1);
        let r2x: Vec<u128> = sp.r2.iter().copied().filter(|&s| reduce128(&sp_ech, s) != 0).collect();
        if r2x.is_empty() { return false; }
        {
            let mut e = sp_ech.clone();
            for &s in &r2x { insert128_into(&mut e, s); }
            if e.len() < m { return false; }
        }
        let mut cands: Vec<u128> = Vec::with_capacity(6 * r2x.len());
        for &s in &r2x { rank2_splits(s, nr, nc, &mut cands); }
        cands.sort_unstable();
        cands.dedup();
        let mut e: Vec<u128> = Vec::with_capacity(m + 1);
        for &n in &cands {
            if reduce128(&sp.ech, n) == 0 { continue; }
            e.clear();
            e.extend_from_slice(&sp_ech);
            for &s in &r2x {
                if is_rank1(n ^ s, nr, nc) { insert128_into(&mut e, s); if e.len() == m { break; } }
            }
            if e.len() == m {
                let w = insert128(&sp.ech, n);
                if visit(&w) { return true; }
            }
        }
        return false;
    }
    for x in 1..(1u32 << nr) {
        for y in 1..(1u32 << nc) {
            let n = kron_small(x, y, nc);
            if reduce128(&sp.ech, n) == 0 { continue; }
            let sp1 = analyze(insert128(&sp.ech, n), nr, nc);
            if search_w(&sp1, nr, nc, delta - 1, visit) { return true; }
        }
    }
    false
}

/// a basis of W made of rank-one elements, preferring elements that are not in `orig` (sorted)
fn rank1_basis(w: &[u128], nr: usize, nc: usize, orig: &[u128]) -> Vec<u128> {
    let m = w.len();
    let mut r1: Vec<u128> = Vec::new();
    let mut cur: u128 = 0;
    for j in 1u64..(1u64 << m) {
        cur ^= w[j.trailing_zeros() as usize];
        if is_rank1(cur, nr, nc) { r1.push(cur); }
    }
    r1.sort_by_key(|x| orig.binary_search(x).is_ok()); // non-original first (stable sort)
    let mut co = Coord128::new();
    let mut basis = Vec::new();
    for &x in &r1 { if co.add(x).is_none() { basis.push(x); } }
    assert!(basis.len() == m, "W is not spanned by rank-one elements");
    basis
}

struct Dir { d: usize, r: usize, c: usize, nr: usize, nc: usize, kr: Vec<u128>, slices: Vec<u128>, ech: Vec<u128> }

/// the k products in restricted coordinates and the three slice-space directions
fn directions(prods: &[Prod]) -> ([Coord; 3], [usize; 3], Vec<Dir>) {
    let k = prods.len();
    let mut co = [Coord::new(), Coord::new(), Coord::new()];
    let mut c: Vec<[u32; 3]> = Vec::with_capacity(k);
    for p in prods { c.push([co[0].add(p[0]), co[1].add(p[1]), co[2].add(p[2])]); }
    let dims = [co[0].basis.len(), co[1].basis.len(), co[2].basis.len()];
    let mut dirs = Vec::new();
    for d in 0..3 {
        let (r, cidx) = match d { 0 => (1usize, 2usize), 1 => (0, 2), _ => (0, 1) };
        let (nr, nc) = (dims[r], dims[cidx]);
        if nr * nc > 128 || dims[d] > 32 { continue; }
        let kr: Vec<u128> = c.iter().map(|x| kron_small(x[r], x[cidx], nc)).collect();
        let mut slices: Vec<u128> = Vec::with_capacity(dims[d]);
        for i in 0..dims[d] {
            let mut sm: u128 = 0;
            for t in 0..k { if (c[t][d] >> i) & 1 == 1 { sm ^= kr[t]; } }
            slices.push(sm);
        }
        let ech = echelon128(&slices);
        dirs.push(Dir { d, r, c: cidx, nr, nc, kr, slices, ech });
    }
    (co, dims, dirs)
}

/// the products of the decomposition read off a space W (spanned by rank-one elements) in direction `dir`
fn build_products(dir: &Dir, co: &[Coord; 3], w: &[u128]) -> Vec<Prod> {
    let mut orig = dir.kr.clone();
    orig.sort_unstable();
    let basis = rank1_basis(w, dir.nr, dir.nc, &orig);
    let mut tr = Coord128::new();
    for &b in &basis { assert!(tr.add(b).is_none()); }
    let mut lam: Vec<u32> = vec![0; basis.len()];
    for (s, &x) in dir.slices.iter().enumerate() {
        let mask = tr.add(x).expect("slice outside W");
        for i in 0..basis.len() { if (mask >> i) & 1 == 1 { lam[i] |= 1 << s; } }
    }
    let mut out = Vec::with_capacity(basis.len());
    for i in 0..basis.len() {
        if lam[i] == 0 { continue; } // a basis element no slice uses: not a term of R
        let (x, y) = rank1_factors(basis[i], dir.nr, dir.nc);
        let mut p: Prod = [0; 3];
        p[dir.r] = co[dir.r].ambient(x);
        p[dir.c] = co[dir.c].ambient(y);
        p[dir.d] = co[dir.d].ambient(lam[i]);
        out.push(p);
    }
    out
}

/// the ambient tensor of a sum of products, as a bit vector over (a-bit, b-bit, c-bit) index triples
fn tensor_sum(ps: &[Prod], n: [usize; 3]) -> Vec<u64> {
    let (wa, wb, wc) = (n[0] * n[1], n[1] * n[2], n[0] * n[2]);
    let mut t = vec![0u64; (wa * wb * wc + 63) / 64];
    for p in ps {
        for i in 0..wa { if (p[0] >> i) & 1 == 0 { continue; }
            for j in 0..wb { if (p[1] >> j) & 1 == 0 { continue; }
                for l in 0..wc { if (p[2] >> l) & 1 == 1 { let b = (i * wb + j) * wc + l; t[b / 64] ^= 1u64 << (b % 64); } }
            }
        }
    }
    t
}

fn fmt_prods(ps: &[Prod], n: [usize; 3]) -> String {
    let (wa, wb, wc) = (n[0] * n[1], n[1] * n[2], n[0] * n[2]);
    let bits = |v: u32, w: usize| -> String { (0..w).map(|i| if (v >> i) & 1 == 1 { '1' } else { '0' }).collect() };
    ps.iter().map(|p| format!("{}/{}/{}", bits(p[0], wa), bits(p[1], wb), bits(p[2], wc))).collect::<Vec<_>>().join(",")
}

enum Verdict { No, Yes(Vec<Prod>, bool), Open }

/// Decide a candidate.  target = k-1 (reduce) or k (alt).  Yes carries the new products (fewer than k, or k
/// different ones) and whether their tensor equals the dropped products'.  Open: delta beyond maxdelta.
fn decide(prods: &[Prod], target: usize, maxdelta: usize, n: [usize; 3]) -> Verdict {
    let k = prods.len();
    let (co, _dims, dirs) = directions(prods);
    if dirs.is_empty() { return Verdict::Open; }
    let finish = |dir: &Dir, w: &[u128]| -> Verdict {
        let ps = build_products(dir, &co, w);
        let ok = tensor_sum(prods, n) == tensor_sum(&ps, n);
        Verdict::Yes(ps, ok)
    };
    if let Some(dir) = dirs.iter().find(|x| x.ech.len() == target) {
        let sp = analyze(dir.ech.clone(), dir.nr, dir.nc);
        let yes = if target == k { sp.r1.len() > k } else { sp.spanned };
        return if yes { finish(dir, &dir.ech) } else { Verdict::No };
    }
    let dir = dirs.iter().max_by_key(|x| x.ech.len()).unwrap();
    let m = dir.ech.len();
    if m > target { return Verdict::No; }
    let delta = target - m;
    if delta > maxdelta { return Verdict::Open; }
    let u = echelon128(&dir.kr);
    let sp = analyze(dir.ech.clone(), dir.nr, dir.nc);
    let mut found: Option<Vec<u128>> = None;
    {
        let mut visit = |w: &[u128]| -> bool {
            if target == k && same_space(w, &u) { return false; }
            found = Some(w.to_vec());
            true
        };
        search_w(&sp, dir.nr, dir.nc, delta, &mut visit);
    }
    if found.is_none() && target == k {
        let su = analyze(u.clone(), dir.nr, dir.nc);
        if su.r1.len() > k { found = Some(u.clone()); }
    }
    match found { None => Verdict::No, Some(w) => finish(dir, &w) }
}

struct Walk<'a> {
    prods: &'a [Prod],
    krons: &'a [[Wide; 3]], // per product: a(x)b, a(x)c, b(x)c
    k: usize,
    both: bool,
    decide: bool,
    maxdelta: usize,
    maxdelta_alt: usize,
    n: [usize; 3],
    chosen: Vec<usize>,
    out: Vec<String>,
    visited: u64,
    counts: [u64; 6], // R candidates, A candidates, refuted, reducible, unique, alternatives (decide mode)
}

fn line_plain(tag: &str, k: usize, bases: &[Basis; 3], idx: &[String]) -> String {
    format!("{} k={} dims={},{},{} idx={}", tag, k, bases[0].dim(), bases[1].dim(), bases[2].dim(), idx.join(","))
}

fn yes_line(head: &str, ps: &[Prod], ok: bool, n: [usize; 3]) -> String {
    format!("{} new={} verified={}", head, fmt_prods(ps, n), if ok { 1 } else { 0 })
}

impl<'a> Walk<'a> {
    fn dfs(&mut self, start: usize, bases: &[Basis; 3], wb: &[WBasis; 3], dep: [bool; 3], kdep: [bool; 3]) {
        if self.chosen.len() == self.k {
            self.visited += 1;
            let ndep = dep.iter().filter(|&&d| d).count();
            // flattening rank of slot c drops when the c-factors or the a(x)b products are dependent, etc.
            let flat = [dep[0] || kdep[2], dep[1] || kdep[1], dep[2] || kdep[0]];
            let reducible = flat.iter().all(|&d| d);
            if reducible || (self.both && ndep >= 2) {
                let tag = if reducible { "R" } else { "A" };
                if reducible { self.counts[0] += 1; } else { self.counts[1] += 1; }
                let idx: Vec<String> = self.chosen.iter().map(|i| i.to_string()).collect();
                if self.decide {
                    let ps: Vec<Prod> = self.chosen.iter().map(|&i| self.prods[i]).collect();
                    let line = |t: &str| format!("{} k={} dims={},{},{} idx={}", t, self.k, bases[0].dim(), bases[1].dim(), bases[2].dim(), idx.join(","));
                    let mut reduced = false;
                    if reducible {
                        match decide(&ps, self.k - 1, self.maxdelta, self.n) {
                            Verdict::No => self.counts[2] += 1,
                            Verdict::Yes(np, ok) => { self.counts[3] += 1; reduced = true; self.out.push(yes_line(&line("RED"), &np, ok, self.n)); }
                            Verdict::Open => self.out.push(line("R")),
                        }
                    }
                    if self.both && ndep >= 2 && !reduced {
                        match decide(&ps, self.k, self.maxdelta_alt, self.n) {
                            Verdict::No => self.counts[4] += 1,
                            Verdict::Yes(np, ok) => {
                                if np.len() < self.k { self.counts[3] += 1; self.out.push(yes_line(&line("RED"), &np, ok, self.n)); }
                                else { self.counts[5] += 1; self.out.push(yes_line(&line("ALT"), &np, ok, self.n)); }
                            }
                            Verdict::Open => self.out.push(line("A")),
                        }
                    }
                } else {
                    self.out.push(line_plain(tag, self.k, bases, &idx));
                }
            }
            return;
        }
        let need = self.k - self.chosen.len();
        for i in start..=(self.prods.len() - need) {
            let mut nb = bases.clone();
            let mut nd = dep;
            for s in 0..3 {
                let r = nb[s].reduce(self.prods[i][s]);
                if r == 0 { nd[s] = true; } else { nb[s].insert(r); }
            }
            let mut nwb = wb.clone();
            let mut nkd = kdep;
            for s in 0..3 {
                let r = nwb[s].reduce(self.krons[i][s]);
                if r == [0; 4] { nkd[s] = true; } else { nwb[s].insert(r); }
            }
            self.chosen.push(i);
            self.dfs(i + 1, &nb, &nwb, nd, nkd);
            self.chosen.pop();
        }
    }
}

fn parse_idx(line: &str) -> Option<Vec<usize>> {
    let p = line.find("idx=")?;
    let rest = &line[p + 4..];
    let end = rest.find(|ch: char| !(ch.is_ascii_digit() || ch == ',')).unwrap_or(rest.len());
    rest[..end].split(',').map(|s| s.parse().ok()).collect()
}

/// decide the candidates of a file (R / A lines); returns the output lines and counts per k
fn decide_lines(prods: &[Prod], lines: &[String], mode: &str, threads: usize, maxdelta: usize, maxdelta_alt: usize, n: [usize; 3]) -> Vec<String> {
    let next = AtomicUsize::new(0);
    let results: Mutex<Vec<(usize, Vec<String>, std::collections::BTreeMap<(usize, &'static str), u64>)>> = Mutex::new(Vec::new());
    std::thread::scope(|sc| {
        for _ in 0..threads {
            sc.spawn(|| {
                let mut out = Vec::new();
                let mut counts: std::collections::BTreeMap<(usize, &'static str), u64> = std::collections::BTreeMap::new();
                let mut first = usize::MAX;
                loop {
                    let i = next.fetch_add(1, Ordering::Relaxed);
                    if i >= lines.len() { break; }
                    if first == usize::MAX { first = i; }
                    let line = &lines[i];
                    let idx = match parse_idx(line) { Some(v) => v, None => continue };
                    let k = idx.len();
                    let ps: Vec<Prod> = idx.iter().map(|&j| prods[j]).collect();
                    let (_co, dims, _dirs) = directions(&ps);
                    let head = |t: &str| format!("{} k={} dims={},{},{} idx={}", t, k, dims[0], dims[1], dims[2], idx.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","));
                    let is_r = line.starts_with('R');
                    let mut reduced = false;
                    if (mode == "reduce" || mode == "both") && is_r {
                        match decide(&ps, k - 1, maxdelta, n) {
                            Verdict::No => *counts.entry((k, "refuted")).or_insert(0) += 1,
                            Verdict::Yes(np, ok) => { *counts.entry((k, "REDUCIBLE")).or_insert(0) += 1; reduced = true; out.push((i, yes_line(&head("RED"), &np, ok, n))); }
                            Verdict::Open => { *counts.entry((k, "reduce-open")).or_insert(0) += 1; out.push((i, head("R"))); }
                        }
                    }
                    if (mode == "alt" || mode == "both") && !reduced {
                        match decide(&ps, k, maxdelta_alt, n) {
                            Verdict::No => *counts.entry((k, "unique")).or_insert(0) += 1,
                            Verdict::Yes(np, ok) => {
                                if np.len() < k { *counts.entry((k, "REDUCIBLE")).or_insert(0) += 1; out.push((i, yes_line(&head("RED"), &np, ok, n))); }
                                else { *counts.entry((k, "ALTERNATIVES")).or_insert(0) += 1; out.push((i, yes_line(&head("ALT"), &np, ok, n))); }
                            }
                            Verdict::Open => { *counts.entry((k, "alt-open")).or_insert(0) += 1; out.push((i, head("A"))); }
                        }
                    }
                }
                let mut o: Vec<(usize, String)> = out;
                o.sort_by_key(|x| x.0);
                results.lock().unwrap().push((first, o.into_iter().map(|x| x.1).collect(), counts));
            });
        }
    });
    let mut res = results.into_inner().unwrap();
    res.sort_by_key(|x| x.0);
    let mut tot: std::collections::BTreeMap<(usize, &'static str), u64> = std::collections::BTreeMap::new();
    for x in &res { for (key, v) in &x.2 { *tot.entry(*key).or_insert(0) += v; } }
    let mut all: Vec<String> = Vec::new();
    for x in res { all.extend(x.1); }
    let ks: std::collections::BTreeSet<usize> = tot.keys().map(|x| x.0).collect();
    for k in ks {
        let parts: Vec<String> = tot.iter().filter(|(key, _)| key.0 == k).map(|(key, v)| format!("{} {}", v, key.1)).collect();
        println!("c k={k}: {}", parts.join(", "));
    }
    all
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() < 4 {
        eprintln!("usage: kres N1 N2 N3 scheme.bits --kmin K --kmax K [--threads T] [--out FILE] [--both] [--decide]\n       kres N1 N2 N3 scheme.bits --lines FILE [--mode reduce|alt|both]\n       kres N1 N2 N3 scheme.bits --subset i,j,...");
        std::process::exit(2);
    }
    let (n1, n2, n3): (usize, usize, usize) = (args[0].parse().unwrap(), args[1].parse().unwrap(), args[2].parse().unwrap());
    let n = [n1, n2, n3];
    let prods = load(&args[3], n1, n2, n3);
    let threads: usize = arg_val(&args, "--threads").unwrap_or(12);
    let maxdelta: usize = arg_val(&args, "--maxdelta").unwrap_or(2);
    let maxdelta_alt: usize = arg_val(&args, "--maxdelta-alt").unwrap_or(1);
    let out_path: Option<String> = arg_val(&args, "--out");
    let r = prods.len();
    let t0 = std::time::Instant::now();
    if let Some(sub) = arg_val::<String>(&args, "--subset") {
        let idx: Vec<usize> = sub.split(',').map(|s| s.parse().unwrap()).collect();
        let ps: Vec<Prod> = idx.iter().map(|&j| prods[j]).collect();
        let k = ps.len();
        let (_co, dims, dirs) = directions(&ps);
        println!("subset k={k} idx={sub} factor-span dims {},{},{}", dims[0], dims[1], dims[2]);
        for d in &dirs { println!("  direction {} (slices over slots {} x {}, {}x{} matrices): flattening rank {}, original space dim {}", d.d, d.r, d.c, d.nr, d.nc, d.ech.len(), echelon128(&d.kr).len()); }
        for (name, target, md) in [("reduce", k - 1, maxdelta), ("alt", k, maxdelta_alt)] {
            let best = dirs.iter().map(|x| x.ech.len()).max().unwrap_or(0);
            let t1 = std::time::Instant::now();
            let v = decide(&ps, target, md, n);
            let path = if dirs.iter().any(|x| x.ech.len() == target) { "exact (a direction has flattening rank == target)".to_string() } else { format!("deficient, delta = {}", target as i64 - best as i64) };
            match v {
                Verdict::No => println!("  {name}: NO ({path}) {:.3} s", t1.elapsed().as_secs_f64()),
                Verdict::Open => println!("  {name}: OPEN ({path}; beyond maxdelta) {:.3} s", t1.elapsed().as_secs_f64()),
                Verdict::Yes(np, ok) => println!("  {name}: YES, {} products, verified={} ({path}) {:.3} s\n    new={}", np.len(), ok as u8, t1.elapsed().as_secs_f64(), fmt_prods(&np, n)),
            }
        }
        return;
    }
    if let Some(lf) = arg_val::<String>(&args, "--lines") {
        let mode: String = arg_val(&args, "--mode").unwrap_or_else(|| "reduce".to_string());
        let txt = std::fs::read_to_string(&lf).expect("read lines");
        let lines: Vec<String> = txt.lines().filter(|l| l.starts_with("R ") || l.starts_with("A ")).map(|l| l.to_string()).collect();
        println!("c kres --lines: <{n1},{n2},{n3}> rank {r} from {}; {} candidate lines from {lf}; mode {mode}; maxdelta {maxdelta} / alt {maxdelta_alt}", args[3], lines.len());
        let all = decide_lines(&prods, &lines, &mode, threads, maxdelta, maxdelta_alt, n);
        println!("c {:.1} s", t0.elapsed().as_secs_f64());
        if let Some(p) = out_path {
            let mut f = std::fs::File::create(&p).unwrap();
            for l in &all { writeln!(f, "{l}").unwrap(); }
            println!("c wrote {} lines to {p}", all.len());
        } else {
            for l in &all { println!("{l}"); }
        }
        return;
    }
    let kmin: usize = arg_val(&args, "--kmin").unwrap_or(3);
    let kmax: usize = arg_val(&args, "--kmax").unwrap_or(8);
    let both = args.iter().any(|a| a == "--both");
    let decide_flag = args.iter().any(|a| a == "--decide");
    let (wb_, wc_) = (n2 * n3, n1 * n3);
    let krons: Vec<[Wide; 3]> = prods.iter().map(|p| [kron(p[0], p[1], wb_), kron(p[0], p[2], wc_), kron(p[1], p[2], wc_)]).collect();
    // whole-scheme span dimensions, for the record
    let mut full = [Basis::new(), Basis::new(), Basis::new()];
    for p in &prods { for s in 0..3 { let x = full[s].reduce(p[s]); if x != 0 { full[s].insert(x); } } }
    println!("c kres: <{n1},{n2},{n3}> rank {r} from {}; factor span dims {},{},{}; k = {kmin}..{kmax}; {} candidates{}",
        args[3], full[0].dim(), full[1].dim(), full[2].dim(), if both { "R and A" } else { "R only" },
        if decide_flag { format!("; decided, maxdelta {maxdelta} / alt {maxdelta_alt}") } else { String::new() });
    let mut all: Vec<String> = Vec::new();
    for k in kmin..=kmax {
        let t0 = std::time::Instant::now();
        let next = AtomicUsize::new(0);
        let results: Mutex<Vec<(usize, Vec<String>, u64, [u64; 6])>> = Mutex::new(Vec::new());
        std::thread::scope(|sc| {
            for _ in 0..threads {
                sc.spawn(|| {
                    loop {
                        let i0 = next.fetch_add(1, Ordering::Relaxed);
                        if i0 + k > r { break; }
                        let mut w = Walk { prods: &prods, krons: &krons, k, both, decide: decide_flag, maxdelta, maxdelta_alt, n, chosen: vec![i0], out: Vec::new(), visited: 0, counts: [0; 6] };
                        let mut b = [Basis::new(), Basis::new(), Basis::new()];
                        for s in 0..3 { b[s].insert(prods[i0][s]); }
                        let mut wbs = [WBasis::new(), WBasis::new(), WBasis::new()];
                        for s in 0..3 { wbs[s].insert(krons[i0][s]); }
                        w.dfs(i0 + 1, &b, &wbs, [false; 3], [false; 3]);
                        results.lock().unwrap().push((i0, w.out, w.visited, w.counts));
                    }
                });
            }
        });
        let mut res = results.into_inner().unwrap();
        res.sort_by_key(|x| x.0);
        let visited: u64 = res.iter().map(|x| x.2).sum();
        let mut tot = [0u64; 6];
        for x in &res { for j in 0..6 { tot[j] += x.3[j]; } }
        let mut lines: Vec<String> = res.into_iter().flat_map(|x| x.1).collect();
        if decide_flag {
            let und_r = lines.iter().filter(|l| l.starts_with("R ")).count();
            let und_a = lines.iter().filter(|l| l.starts_with("A ")).count();
            println!("c k={k}: {visited} subsets; reduce: {} candidates, {} refuted, {} REDUCIBLE, {} open; alt: {} candidates (+ the reduce candidates), {} unique, {} with ALTERNATIVES, {} open; {:.1} s",
                tot[0], tot[2], tot[3], und_r, tot[1], tot[4], tot[5], und_a, t0.elapsed().as_secs_f64());
        } else {
            let nr = lines.iter().filter(|l| l.starts_with('R')).count();
            let na = lines.len() - nr;
            println!("c k={k}: {visited} subsets, {nr} reduction candidates (all three flattening ranks below k), {na} alternative candidates (two dependent slots), {:.1} s",
                t0.elapsed().as_secs_f64());
        }
        all.append(&mut lines);
    }
    if let Some(p) = out_path {
        let mut f = std::fs::File::create(&p).unwrap();
        for l in &all { writeln!(f, "{l}").unwrap(); }
        println!("c wrote {} candidates to {p}", all.len());
    } else {
        for l in &all { println!("{l}"); }
    }
}
