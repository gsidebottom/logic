//! symflip3: the flip graph over F3 for rectangular formats, with an optional symmetry imposed.
//!
//! Why F3: a scheme over Q whose denominators are odd reduces mod 2, and the F2 searches (flip,
//! kres8, symflip) see its image; a scheme that needs halves does not, but reduces mod 3.  This is
//! symflip's walk over F3, so that it covers those.
//!
//! A summand is c * a (x) b (x) c with the three factors normalized (first nonzero entry +1) and a
//! coefficient c = +-1; a scheme is a set of summands with distinct factor triples.  Factors are
//! pairs of bit masks (entries +1, entries -1).  Moves, lambda = +-1:
//!   flip    s = (a, b, c), t = (a, b', c') share a factor:  s -> (a, b + lambda b', c),
//!           t -> (a, b', c' - lambda c)
//!   merge   s, t share two factors: one summand (a, b, c + c'), or none
//!   plus    s = (a, b, c) -> (a, b, c - v) + (a, b, v) with v a factor of another summand t, and the new
//!           summand flipped at once with t (rank + 1)
//! With a group G (index permutations, --gen as in symflip) every move is the identity
//! old = new between small sets of summands summed over G: sum_g g(old) = sum_g g(new).  The left
//! side is a multiple k of the scheme's own summands when their stabilizers agree, and then the
//! scheme loses them and gains k times the right side, equal summands combined mod 3; otherwise the
//! move is refused.  Orbits collapsing to fixed summands, and orbits cancelling, are cases of the
//! same rule.  The walk, the pool and the checks are symflip's: every scheme at a new low is
//! verified against the tensor mod 3 and against the group.
//!
//!   symflip3 N1 N2 N3 [--gen "S;T;R"]... [--start FILE.trits] [--minutes M] [--threads T] [--seed S]
//!            [--stall N] [--plus P] [--plus-max K] [--plus-every N] [--margin K] [--save-at R] [--out DIR]
//! .trits: one summand per line, three strings of digits 0, 1, 2 (2 = -1): the entries of its A, B, C
//! factors, row-major (matmul/r346/sym/to_trits.py writes them from a catalog scheme).

use std::collections::HashSet;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::Instant;

type V = (u32, u32);                                  // entries +1, entries -1
type F = [V; 3];
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Term { f: F, c: u8 }                           // c in {1, 2}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: usize) -> usize { (self.next() % n as u64) as usize }
    fn unit(&mut self) -> f64 { (self.next() >> 11) as f64 / 9007199254740992.0 }
}

#[inline(always)]
fn vadd(a: V, b: V) -> V {
    ((a.0 & !b.0 & !b.1) | (b.0 & !a.0 & !a.1) | (a.1 & b.1), (a.1 & !b.0 & !b.1) | (b.1 & !a.0 & !a.1) | (a.0 & b.0))
}
#[inline(always)]
fn vneg(a: V) -> V { (a.1, a.0) }
#[inline(always)]
fn vmul(a: V, c: u8) -> V { if c == 1 { a } else { vneg(a) } }
/// a term from raw factors and a coefficient: None if a factor is zero
fn mk(mut f: F, mut c: u8) -> Option<Term> {
    for q in 0..3 {
        let nz = f[q].0 | f[q].1;
        if nz == 0 { return None; }
        if (f[q].1 >> nz.trailing_zeros()) & 1 == 1 { f[q] = vneg(f[q]); c = 3 - c; }
    }
    Some(Term { f, c })
}

/// a group element: for each slot, the image of every basis entry
#[derive(Clone, PartialEq, Eq, Hash)]
struct Elem { p: [Vec<V>; 3] }
fn act(v: V, img: &[V]) -> V {
    let mut out = (0u32, 0u32);
    let mut m = v.0;
    while m != 0 { out = vadd(out, img[m.trailing_zeros() as usize]); m &= m - 1; }
    let mut m = v.1;
    while m != 0 { out = vadd(out, vneg(img[m.trailing_zeros() as usize])); m &= m - 1; }
    out
}
fn apply(g: &Elem, t: &Term) -> Term { mk([act(t.f[0], &g.p[0]), act(t.f[1], &g.p[1]), act(t.f[2], &g.p[2])], t.c).expect("a group element is invertible") }
fn elem_perm(n: [usize; 3], s: &[usize], t: &[usize], r: &[usize]) -> Elem {
    let img = |n1: usize, n2: usize, p1: &[usize], p2: &[usize]| -> Vec<V> { (0..n1 * n2).map(|b| (1u32 << (p1[b / n2] * n2 + p2[b % n2]), 0u32)).collect() };
    Elem { p: [img(n[0], n[1], s, t), img(n[1], n[2], t, r), img(n[0], n[2], s, r)] }
}
fn compose(a: &Elem, b: &Elem) -> Elem {       // a after b
    Elem { p: [b.p[0].iter().map(|&x| act(x, &a.p[0])).collect(), b.p[1].iter().map(|&x| act(x, &a.p[1])).collect(), b.p[2].iter().map(|&x| act(x, &a.p[2])).collect()] }
}
fn closure(gens: &[Elem], id: Elem) -> Vec<Elem> {
    let mut seen: HashSet<Elem> = HashSet::new();
    let mut out = vec![id.clone()];
    seen.insert(id);
    let mut i = 0;
    while i < out.len() {
        for g in gens { let h = compose(g, &out[i]); if seen.insert(h.clone()) { out.push(h); } }
        i += 1;
        assert!(out.len() <= 5000, "the group is too large");
    }
    out
}

fn find(s: &[Term], f: &F) -> Option<usize> { s.iter().position(|x| x.f == *f) }
fn accumulate(m: &mut Vec<(F, u8)>, t: &Term, k: u8) {
    let c = (t.c * k) % 3;
    match m.iter_mut().find(|x| x.0 == t.f) { Some(x) => x.1 = (x.1 + c) % 3, None => m.push((t.f, c)) }
}

/// the move old -> new (equal sums) summed over the group; the factor triples it wrote go to `added`.  Refused
/// if the rank would change by more than max_delta: a flip of a summand with its own image is an identity too,
/// but one with twice the summands on the right.
fn replace(s: &mut Vec<Term>, grp: &[Elem], old: &[Term], new: &[Term], added: &mut Vec<F>, max_delta: isize) -> bool {
    let (mut mo, mut mn): (Vec<(F, u8)>, Vec<(F, u8)>) = (Vec::new(), Vec::new());
    if grp.len() == 1 { for t in old { accumulate(&mut mo, t, 1); } } else { for g in grp { for t in old { accumulate(&mut mo, &apply(g, t), 1); } } }
    // the scheme's summands on the support must be k times the orbit sum
    let mut k = 0u8;
    for (f, c) in &mo {
        if *c == 0 { DBG[2].fetch_add(1, Ordering::Relaxed); return false; }
        let Some(i) = find(s, f) else { DBG[3].fetch_add(1, Ordering::Relaxed); return false };
        let need = (s[i].c * *c) % 3;              // s.c / c, and 1/c = c in F3
        if k == 0 { k = need; } else if k != need { DBG[4].fetch_add(1, Ordering::Relaxed); return false; }
    }
    if grp.len() == 1 { for t in new { accumulate(&mut mn, t, k); } } else { for g in grp { for t in new { accumulate(&mut mn, &apply(g, t), k); } } }
    let mut delta = -(mo.len() as isize);
    for (f, c) in &mn {
        if *c == 0 { continue; }
        if mo.iter().any(|x| x.0 == *f) { delta += 1; continue; }
        match find(s, f) { Some(i) => if (s[i].c + *c) % 3 == 0 { delta -= 1; }, None => delta += 1 }
    }
    if delta > max_delta { DBG[5].fetch_add(1, Ordering::Relaxed); return false; }
    for (f, _) in &mo { let i = find(s, f).unwrap(); s.swap_remove(i); }
    for (f, c) in mn {
        if c == 0 { continue; }
        match find(s, &f) {
            Some(i) => { let nc = (s[i].c + c) % 3; if nc == 0 { s.swap_remove(i); } else { s[i].c = nc; added.push(f); } }
            None => { s.push(Term { f, c }); added.push(f); }
        }
    }
    true
}

/// the flip of s and t, which share slot x: slot y of s gains lambda t, slot z of t loses lambda s
fn flip_terms(s: &Term, t: &Term, y: usize, z: usize, lam: u8) -> Vec<Term> {
    let (mut fs, mut ft) = (s.f, t.f);
    fs[y] = vadd(s.f[y], vmul(t.f[y], lam));
    ft[z] = vadd(t.f[z], vmul(s.f[z], (3 - lam) * s.c * t.c % 3));       // - lambda c_s / c_t
    [mk(fs, s.c), mk(ft, t.c)].into_iter().flatten().collect()
}

/// merges while there are any at the summands in `added`; true if something merged
fn reduce(s: &mut Vec<Term>, grp: &[Elem], added: &mut Vec<F>) -> bool {
    let mut any = false;
    while let Some(f) = added.pop() {
        let Some(p) = find(s, &f) else { continue };
        for q in 0..s.len() {
            if q == p { continue; }
            let same = [s[p].f[0] == s[q].f[0], s[p].f[1] == s[q].f[1], s[p].f[2] == s[q].f[2]];
            if same.iter().filter(|x| **x).count() != 2 { continue; }
            let z = same.iter().position(|x| !*x).unwrap();
            let (a, b) = (s[p], s[q]);
            let mut fm = a.f;
            fm[z] = vadd(vmul(a.f[z], a.c), vmul(b.f[z], b.c));
            let new: Vec<Term> = mk(fm, 1).into_iter().collect();
            DBG[0].fetch_add(1, Ordering::Relaxed);
            if replace(s, grp, &[a, b], &new, added, -1) { any = true; DBG[1].fetch_add(1, Ordering::Relaxed); break; }
        }
    }
    any
}

/// a plus transition: s split toward a factor of t and the new summand flipped with t; true if done
fn plus_move(s: &mut Vec<Term>, grp: &[Elem], rng: &mut Rng, added: &mut Vec<F>) -> bool {
    for _ in 0..50 {
        let (a, b, z) = (rng.below(s.len()), rng.below(s.len()), rng.below(3));
        if a == b || s[a].f[z] == s[b].f[z] { continue; }
        let (sa, tb) = (s[a], s[b]);
        let v = tb.f[z];
        let mut f1 = sa.f;
        f1[z] = vadd(sa.f[z], vneg(v));
        let Some(s1) = mk(f1, sa.c) else { continue };
        let mut fc = sa.f;
        fc[z] = v;
        let child = Term { f: fc, c: sa.c };
        let (y1, z1) = if rng.next() & 1 == 0 { ((z + 1) % 3, (z + 2) % 3) } else { ((z + 2) % 3, (z + 1) % 3) };
        let mut new = flip_terms(&child, &tb, y1, z1, 1 + (rng.next() & 1) as u8);
        new.push(s1);
        if replace(s, grp, &[sa, tb], &new, added, isize::MAX) { return true; }
    }
    false
}

fn tensor_ok(s: &[Term], n: [usize; 3]) -> bool {
    let (nb, nc) = (n[1] * n[2], n[0] * n[2]);
    let mut t = vec![0u8; n[0] * n[1] * nb * nc];
    let ent = |v: V, i: usize| -> u8 { if (v.0 >> i) & 1 == 1 { 1 } else if (v.1 >> i) & 1 == 1 { 2 } else { 0 } };
    for x in s {
        for ai in 0..n[0] * n[1] { let a = ent(x.f[0], ai); if a == 0 { continue; }
            for bi in 0..nb { let b = ent(x.f[1], bi); if b == 0 { continue; }
                for ci in 0..nc { let c = ent(x.f[2], ci); if c == 0 { continue; }
                    let k = (ai * nb + bi) * nc + ci;
                    t[k] = (t[k] + x.c * a * b * c) % 3;
                } } }
    }
    for i in 0..n[0] { for j in 0..n[1] { for k in 0..n[2] { let q = ((i * n[1] + j) * nb + j * n[2] + k) * nc + i * n[2] + k; t[q] = (t[q] + 2) % 3; } } }
    t.iter().all(|x| *x == 0)
}
fn invariant(s: &[Term], grp: &[Elem]) -> bool { grp.iter().all(|g| s.iter().all(|t| { let u = apply(g, t); find(s, &u.f).map_or(false, |i| s[i].c == u.c) })) }
fn fixed(s: &[Term], grp: &[Elem]) -> usize { s.iter().filter(|t| grp.iter().all(|g| apply(g, t) == **t)).count() }
fn standard(n: [usize; 3]) -> Vec<Term> {
    let mut s = Vec::new();
    for i in 0..n[0] { for j in 0..n[1] { for k in 0..n[2] { s.push(Term { f: [(1u32 << (i * n[1] + j), 0), (1u32 << (j * n[2] + k), 0), (1u32 << (i * n[2] + k), 0)], c: 1 }); } } }
    s
}
fn write_trits(s: &[Term], n: [usize; 3], path: &str) {
    let sz = [n[0] * n[1], n[1] * n[2], n[0] * n[2]];
    let mut out = String::new();
    for t in s {
        for q in 0..3 {
            let v = if q == 2 { vmul(t.f[q], t.c) } else { t.f[q] };
            for k in 0..sz[q] { out.push(if (v.0 >> k) & 1 == 1 { '1' } else if (v.1 >> k) & 1 == 1 { '2' } else { '0' }); }
            out.push(if q == 2 { '\n' } else { ' ' });
        }
    }
    std::fs::write(path, out).expect("write");
}
fn read_trits(path: &str, n: [usize; 3]) -> Vec<Term> {
    let sz = [n[0] * n[1], n[1] * n[2], n[0] * n[2]];
    let mut s: Vec<Term> = Vec::new();
    for ln in std::fs::read_to_string(path).expect("start file").lines() {
        let w: Vec<&str> = ln.split_whitespace().collect();
        if w.is_empty() || w[0].starts_with('#') { continue; }
        assert!(w.len() == 3 && (0..3).all(|q| w[q].len() == sz[q]), "not a trits file of this format");
        let mut f = [(0u32, 0u32); 3];
        for q in 0..3 { for (k, ch) in w[q].bytes().enumerate() { match ch { b'1' => f[q].0 |= 1 << k, b'2' => f[q].1 |= 1 << k, _ => {} } } }
        if let Some(t) = mk(f, 1) {
            match find(&s, &t.f) { Some(i) => { let c = (s[i].c + t.c) % 3; if c == 0 { s.swap_remove(i); } else { s[i].c = c; } } None => s.push(t) }
        }
    }
    s
}

static DBG: [AtomicU64; 6] = [AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0)];
struct Pool { rank: usize, members: Vec<Vec<Term>>, seen: HashSet<Vec<Term>>, written: usize }

fn main() {
    let a: Vec<String> = std::env::args().skip(1).collect();
    if a.len() < 3 { eprintln!("usage: symflip3 N1 N2 N3 [--gen \"S;T;R\"]... [--start FILE.trits] [--minutes M] [--threads T] [--seed S] [--stall N] [--plus P] [--plus-max K] [--plus-every N] [--margin K] [--save-at R] [--out DIR]"); std::process::exit(2); }
    let n = [a[0].parse::<usize>().unwrap(), a[1].parse::<usize>().unwrap(), a[2].parse::<usize>().unwrap()];
    assert!(n[0] * n[1] <= 32 && n[1] * n[2] <= 32 && n[0] * n[2] <= 32, "a factor does not fit 32 entries");
    let opt = |k: &str, d: f64| -> f64 { a.iter().position(|x| x == k).map(|i| a[i + 1].parse().unwrap()).unwrap_or(d) };
    let (minutes, threads, seed, stall, plus) = (opt("--minutes", 5.0), opt("--threads", 10.0) as usize, opt("--seed", 1.0) as u64, opt("--stall", 20000.0) as u64, opt("--plus", 0.1));
    let (plus_max, plus_every, margin) = (opt("--plus-max", 2.0) as usize, opt("--plus-every", 0.0) as u64, opt("--margin", -1.0));
    let out = a.iter().position(|x| x == "--out").map(|i| a[i + 1].clone());
    let start = match a.iter().position(|x| x == "--start") { Some(i) => read_trits(&a[i + 1], n), None => standard(n) };
    assert!(tensor_ok(&start, n), "the start is not a scheme mod 3");
    let ident = |k: usize| -> Vec<usize> { (0..k).collect() };
    let id = elem_perm(n, &ident(n[0]), &ident(n[1]), &ident(n[2]));
    let perm = |s: &str| -> Vec<usize> { s.split(',').map(|x| x.trim().parse().unwrap()).collect() };
    let mut gens = Vec::new();
    for (i, x) in a.iter().enumerate() { if x == "--gen" {
        let p: Vec<&str> = a[i + 1].split(';').collect();
        let (s, t, r) = (perm(p[0]), perm(p[1]), perm(p[2]));
        assert!(s.len() == n[0] && t.len() == n[1] && r.len() == n[2], "a generator's permutations have the wrong lengths");
        gens.push(elem_perm(n, &s, &t, &r));
    } }
    let grp = closure(&gens, id);
    assert!(invariant(&start, &grp), "the start is not invariant under the group");
    let margin = if margin < 0.0 { 2 * grp.len() + 2 } else { margin as usize };
    let save_at = opt("--save-at", (start.len() as f64) - 1.0) as usize;
    println!("# symflip3 <{}x{}x{}> over F3: group of order {}, start of rank {} ({} summands fixed by the group), {minutes} min, {threads} threads, stall {stall}, plus {plus} (every {plus_every} flips, margin {margin}), save at {save_at}",
             n[0], n[1], n[2], grp.len(), start.len(), fixed(&start, &grp));
    let t0 = Instant::now();
    let pool = Mutex::new(Pool { rank: start.len(), members: vec![start.clone()], seen: HashSet::new(), written: 0 });
    let (flips_total, walks_total, plus_total) = (AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0));
    std::thread::scope(|sc| {
        for th in 0..threads {
            let (grp, pool, out, flips_total, walks_total, plus_total) = (&grp, &pool, &out, &flips_total, &walks_total, &plus_total);
            sc.spawn(move || {
                let mut rng = Rng(seed.wrapping_mul(7919).wrapping_add(th as u64 * 104729 + 1));
                let mut added: Vec<F> = Vec::new();
                let (mut flips, mut walks, mut pluses) = (0u64, 0u64, 0u64);
                let offer = |s: &Vec<Term>, th: usize| {
                    let mut p = pool.lock().unwrap();
                    if s.len() > p.rank { return; }
                    let mut key = s.clone(); key.sort();
                    if s.len() < p.rank {
                        assert!(tensor_ok(s, n) && invariant(s, grp), "a move broke the scheme or its symmetry");
                        p.rank = s.len(); p.members.clear(); p.seen.clear(); p.written = 0;
                        println!("[thread {th}] rank {} ({} fixed summands) after {:.0} s", s.len(), fixed(s, grp), t0.elapsed().as_secs_f64());
                    }
                    if !p.seen.insert(key) { return; }
                    if p.seen.len() > 200000 { p.seen.clear(); }
                    if p.members.len() < 500 { p.members.push(s.clone()); } else { let k = (s[0].f[0].0 as usize ^ p.seen.len()) % 500; p.members[k] = s.clone(); }
                    if s.len() <= save_at && p.written < 20 {
                        if let Some(dir) = out {
                            assert!(tensor_ok(s, n) && invariant(s, grp), "a move broke the scheme or its symmetry");
                            p.written += 1;
                            std::fs::create_dir_all(dir).ok();
                            write_trits(s, n, &format!("{dir}/f3sym{}_{}x{}x{}_r{}_{}.trits", grp.len(), n[0], n[1], n[2], s.len(), p.written));
                        }
                    }
                };
                while t0.elapsed().as_secs_f64() < minutes * 60.0 {
                    let (mut s, base) = { let p = pool.lock().unwrap(); (p.members[rng.below(p.members.len())].clone(), p.rank) };
                    added.clear();
                    let stuck = !(0..s.len()).any(|p| (p + 1..s.len()).any(|q| s[p].f[0] == s[q].f[0] || s[p].f[1] == s[q].f[1] || s[p].f[2] == s[q].f[2]));
                    if stuck || rng.unit() < plus {
                        for _ in 0..1 + rng.below(plus_max) { plus_move(&mut s, grp, &mut rng, &mut added); }
                        reduce(&mut s, grp, &mut added);
                    }
                    let cap = s.len().max(base) + margin;
                    let (mut since, mut dry, mut lowest) = (0u64, 0u64, s.len());
                    walks += 1;
                    while since < stall {
                        let (si, x) = (rng.below(s.len()), rng.below(3));
                        let (mut ti, mut cnt) = (usize::MAX, 0usize);
                        for j in 0..s.len() { if j != si && s[j].f[x] == s[si].f[x] { cnt += 1; if rng.below(cnt) == 0 { ti = j; } } }
                        let (y, z) = if rng.next() & 1 == 0 { ((x + 1) % 3, (x + 2) % 3) } else { ((x + 2) % 3, (x + 1) % 3) };
                        let done = ti != usize::MAX && {
                            let (ts, tt) = (s[si], s[ti]);
                            let new = flip_terms(&ts, &tt, y, z, 1 + (rng.next() & 1) as u8);
                            replace(&mut s, grp, &[ts, tt], &new, &mut added, 0)
                        };
                        if !done {
                            dry += 1;
                            if dry < 500 { continue; }
                            dry = 0;
                            if s.len() + grp.len() > cap || !plus_move(&mut s, grp, &mut rng, &mut added) { break; }
                            pluses += 1; since += 1;
                        } else {
                            dry = 0; flips += 1; since += 1;
                            if plus_every > 0 && since % plus_every == 0 && s.len() + grp.len() <= cap && plus_move(&mut s, grp, &mut rng, &mut added) { pluses += 1; }
                        }
                        let before = s.len();
                        reduce(&mut s, grp, &mut added);
                        if s.len() < before || s.len() < lowest {
                            if s.len() < lowest { lowest = s.len(); since = 0; }
                            if s.len() <= base { offer(&s, th); }
                        }
                    }
                    offer(&s, th);
                }
                flips_total.fetch_add(flips, Ordering::Relaxed);
                walks_total.fetch_add(walks, Ordering::Relaxed);
                plus_total.fetch_add(pluses, Ordering::Relaxed);
            });
        }
    });
    eprintln!("# debug: merges tried {} done {}; refused: zero coefficient {}, not in scheme {}, k mismatch {}, rank growth {}", DBG[0].load(Ordering::Relaxed), DBG[1].load(Ordering::Relaxed), DBG[2].load(Ordering::Relaxed), DBG[3].load(Ordering::Relaxed), DBG[4].load(Ordering::Relaxed), DBG[5].load(Ordering::Relaxed));
    let p = pool.lock().unwrap();
    println!("# done: lowest rank {} ({} schemes in the pool), {:.1} M flips and {:.2} M plus transitions in {} walks, {:.0} s", p.rank, p.members.len(),
             flips_total.load(Ordering::Relaxed) as f64 / 1e6, plus_total.load(Ordering::Relaxed) as f64 / 1e6, walks_total.load(Ordering::Relaxed), t0.elapsed().as_secs_f64());
}
