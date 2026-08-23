//! subgame — step 1 of the automated substitution method over F_2:
//! the exact kill-one-product game on <n,n,n>.
//!
//! A rank-r decomposition sum_i a_i (x) b_i (x) c_i of a tensor T can be
//! cut by one product: quotient one side by that product's vector (say
//! C by c_1); the image (id (x) id (x) q)(T) has rank <= r - 1. The
//! adversary controls the vector, the prover the side, so
//!
//!   val(T) = max( flattening ranks of T,
//!                 max_{side, phi} ( 1 + min_{v in supp, phi.v = 1} val(T / v) ) )
//!   (kill only for T != 0; supp = the side's support subspace, in which a
//!   minimal decomposition's vectors lie and which they span, so the
//!   prover may force the kill outside any hyperplane ker phi not
//!   containing supp — the refined substitution method)
//!
//! is a lower bound on R(T). A state is the triple of killed subspaces
//! (U, V, X), canonical as RREF bases, so the game on <2,2,2> has at most
//! 67^3 states and is exhausted exactly with memoization. The certificate
//! is the memo DAG (side choice, all adversary children, leaf facts);
//! matmul/r22/subgame_verify.py replays it independently.
//!
//!   subgame --n 2 [--cert FILE]
use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;
use std::time::Instant;

type V = u16; // vector in F_2^d, d <= 9

/// reduced row echelon basis (unique per subspace), rows sorted descending
fn rref(rows: &[V]) -> Vec<V> {
    let mut out: Vec<V> = Vec::new();
    for &r in rows {
        let mut v = r;
        for &o in &out {
            let p = 15 - o.leading_zeros();
            if v >> p & 1 == 1 {
                v ^= o;
            }
        }
        if v != 0 {
            let p = 15 - v.leading_zeros();
            for o in out.iter_mut() {
                if *o >> p & 1 == 1 {
                    *o ^= v;
                }
            }
            out.push(v);
        }
    }
    out.sort_unstable_by(|a, b| b.cmp(a));
    out
}

/// basis of the annihilator {phi : phi . u = 0 for all u in U} in F_2^d,
/// plus the free columns f_i: e_i = 1 << f_i is the dual basis (phi_j . e_i
/// = [i = j]), so coordinates y over the annihilator basis map back to the
/// vector sum_i y_i e_i of A (modulo U).
fn annihilator_free(u: &[V], d: usize) -> (Vec<V>, Vec<usize>) {
    let r = rref(u);
    let pivots: Vec<usize> = r.iter().map(|&row| (15 - row.leading_zeros()) as usize).collect();
    let mut basis = Vec::new();
    let mut free = Vec::new();
    for f in 0..d {
        if pivots.contains(&f) {
            continue;
        }
        let mut phi: V = 1 << f;
        for (row, &p) in r.iter().zip(&pivots) {
            if row >> f & 1 == 1 {
                phi |= 1 << p;
            }
        }
        basis.push(phi);
        free.push(f);
    }
    (basis, free)
}
fn annihilator(u: &[V], d: usize) -> Vec<V> {
    annihilator_free(u, d).0
}

/// tensor with dims (da, db, dc): t[a][b] = bitmask over c
#[derive(Clone)]
struct Tensor {
    da: usize,
    db: usize,
    dc: usize,
    t: Vec<Vec<u32>>,
}

fn matmul_tensor(n: usize) -> Tensor {
    let d = n * n;
    let mut t = vec![vec![0u32; d]; d];
    for a in 0..n {
        for b in 0..n {
            for c in 0..n {
                for dd in 0..n {
                    for p in 0..n {
                        for q in 0..n {
                            if b == c && a == p && dd == q {
                                t[a * n + b][c * n + dd] |= 1 << (p * n + q);
                            }
                        }
                    }
                }
            }
        }
    }
    Tensor { da: d, db: d, dc: d, t }
}

fn parity(x: u32) -> u32 {
    x.count_ones() & 1
}

/// T / (U, V, X): contract with annihilator bases
fn quotient(t0: &Tensor, u: &[V], v: &[V], x: &[V]) -> Tensor {
    let (phi, psi, chi) = (annihilator(u, t0.da), annihilator(v, t0.db), annihilator(x, t0.dc));
    // contract c
    let mut s1 = vec![vec![0u32; t0.db]; t0.da];
    for a in 0..t0.da {
        for b in 0..t0.db {
            let mut row = 0u32;
            for (k, &ck) in chi.iter().enumerate() {
                if parity(t0.t[a][b] & ck as u32) == 1 {
                    row |= 1 << k;
                }
            }
            s1[a][b] = row;
        }
    }
    // contract b
    let mut s2 = vec![vec![0u32; psi.len()]; t0.da];
    for a in 0..t0.da {
        for (j, &pj) in psi.iter().enumerate() {
            let mut row = 0u32;
            for b in 0..t0.db {
                if pj >> b & 1 == 1 {
                    row ^= s1[a][b];
                }
            }
            s2[a][j] = row;
        }
    }
    // contract a
    let mut t = vec![vec![0u32; psi.len()]; phi.len()];
    for (i, &fi) in phi.iter().enumerate() {
        for j in 0..psi.len() {
            let mut row = 0u32;
            for a in 0..t0.da {
                if fi >> a & 1 == 1 {
                    row ^= s2[a][j];
                }
            }
            t[i][j] = row;
        }
    }
    Tensor { da: phi.len(), db: psi.len(), dc: chi.len(), t }
}

fn rank_u128(rows: &mut Vec<u128>) -> usize {
    let mut rk = 0;
    let mut col = 127i32;
    while col >= 0 && rk < rows.len() {
        if let Some(p) = (rk..rows.len()).find(|&i| rows[i] >> col & 1 == 1) {
            rows.swap(rk, p);
            for i in 0..rows.len() {
                if i != rk && rows[i] >> col & 1 == 1 {
                    rows[i] ^= rows[rk];
                }
            }
            rk += 1;
        }
        col -= 1;
    }
    rk
}

/// the three flattening ranks (A -> B(x)C, B -> A(x)C, C -> A(x)B)
fn flattenings(t: &Tensor) -> [usize; 3] {
    let mut ra: Vec<u128> = (0..t.da)
        .map(|a| (0..t.db).fold(0u128, |acc, b| acc | ((t.t[a][b] as u128) << (b * t.dc))))
        .collect();
    let mut rb: Vec<u128> = (0..t.db)
        .map(|b| (0..t.da).fold(0u128, |acc, a| acc | ((t.t[a][b] as u128) << (a * t.dc))))
        .collect();
    let mut rc: Vec<u128> = (0..t.dc)
        .map(|c| {
            let mut v = 0u128;
            for a in 0..t.da {
                for b in 0..t.db {
                    if t.t[a][b] >> c & 1 == 1 {
                        v |= 1u128 << (a * t.db + b);
                    }
                }
            }
            v
        })
        .collect();
    [rank_u128(&mut ra), rank_u128(&mut rb), rank_u128(&mut rc)]
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct State {
    u: Vec<V>,
    v: Vec<V>,
    x: Vec<V>,
}

#[derive(Clone)]
struct Node {
    value: u32,
    choice: u8, // 0 = leaf, 1/2/3 = kill on A/B/C
    phi: V,     // the prover's functional (in the original space; kills must satisfy phi . v = 1)
    leaf: [usize; 3],
    dims: (usize, usize, usize),
}

/// support of the quotient tensor on one side, as a subspace of the ORIGINAL
/// space containing the killed subspace: U + span{ sum_i y_i e_i : y in the
/// column space of that side's flattening }
fn support(t: &Tensor, side: u8, killed: &[V], d: usize) -> Vec<V> {
    let (_, free) = annihilator_free(killed, d);
    let cols: Vec<u32> = match side {
        1 => {
            let mut c = Vec::new();
            for b in 0..t.db {
                for k in 0..t.dc {
                    let mut y = 0u32;
                    for i in 0..t.da {
                        if t.t[i][b] >> k & 1 == 1 {
                            y |= 1 << i;
                        }
                    }
                    c.push(y);
                }
            }
            c
        }
        2 => {
            let mut c = Vec::new();
            for i in 0..t.da {
                for k in 0..t.dc {
                    let mut y = 0u32;
                    for j in 0..t.db {
                        if t.t[i][j] >> k & 1 == 1 {
                            y |= 1 << j;
                        }
                    }
                    c.push(y);
                }
            }
            c
        }
        _ => {
            let mut c = Vec::new();
            for i in 0..t.da {
                for j in 0..t.db {
                    c.push(t.t[i][j]);
                }
            }
            c
        }
    };
    let mut rows: Vec<V> = killed.to_vec();
    for y in cols {
        let mut v: V = 0;
        for (i, &f) in free.iter().enumerate() {
            if y >> i & 1 == 1 {
                v |= 1 << f;
            }
        }
        rows.push(v);
    }
    rref(&rows)
}

fn dot(a: V, b: V) -> u32 {
    (a & b).count_ones() & 1
}

/// all elements of a subspace given by a basis
fn elements(basis: &[V]) -> Vec<V> {
    let mut out = Vec::with_capacity(1 << basis.len());
    for code in 0..(1u32 << basis.len()) {
        let mut v: V = 0;
        for (i, &b) in basis.iter().enumerate() {
            if code >> i & 1 == 1 {
                v ^= b;
            }
        }
        out.push(v);
    }
    out
}

struct Game {
    t0: Tensor,
    d: usize,
    memo: HashMap<State, Node>,
}

impl Game {
    fn val(&mut self, s: &State) -> u32 {
        if let Some(n) = self.memo.get(s) {
            return n.value;
        }
        let t = quotient(&self.t0, &s.u, &s.v, &s.x);
        let leaf = flattenings(&t);
        let mut best = *leaf.iter().max().unwrap() as u32;
        let mut choice = 0u8;
        let mut best_phi: V = 0;
        let dims = (t.da, t.db, t.dc);
        // a kill move needs a product to kill: only for a NONZERO tensor
        let nonzero = best > 0;
        for side in 1..=3u8 {
            if !nonzero {
                break;
            }
            let cur = match side {
                1 => &s.u,
                2 => &s.v,
                _ => &s.x,
            };
            if cur.len() >= self.d {
                continue; // side exhausted
            }
            // refined substitution: the killed vector lies in the support S
            // (minimal decompositions live in S (x) ...), and the product
            // vectors SPAN S, so for any functional phi in U^perp that does
            // not vanish on S the adversary must kill some v in S with
            // phi . v = 1. Prover maximizes over phi, adversary minimizes over v.
            let supp = support(&t, side, cur, self.d);
            let supp_el = elements(&supp);
            let (ann, _) = annihilator_free(cur, self.d);
            for phi in elements(&ann).into_iter().filter(|&p| p != 0) {
                if !supp.iter().any(|&sv| dot(phi, sv) == 1) {
                    continue; // phi vanishes on the support: no product forced
                }
                let mut seen = HashSet::new();
                let mut worst = u32::MAX;
                for &v in &supp_el {
                    if dot(phi, v) != 1 {
                        continue;
                    }
                    let mut rows = cur.clone();
                    rows.push(v);
                    let e = rref(&rows);
                    if e.len() == cur.len() || !seen.insert(e.clone()) {
                        continue;
                    }
                    let child = match side {
                        1 => State { u: e, v: s.v.clone(), x: s.x.clone() },
                        2 => State { u: s.u.clone(), v: e, x: s.x.clone() },
                        _ => State { u: s.u.clone(), v: s.v.clone(), x: e },
                    };
                    let cv = self.val(&child);
                    worst = worst.min(cv);
                    if 1 + worst <= best {
                        break; // cannot beat current best
                    }
                }
                if worst != u32::MAX && 1 + worst > best {
                    best = 1 + worst;
                    choice = side;
                    best_phi = phi;
                }
            }
        }
        self.memo.insert(s.clone(), Node { value: best, choice, phi: best_phi, leaf, dims });
        best
    }
}

fn key(s: &State) -> String {
    let f = |v: &[V]| v.iter().map(|x| format!("{x:x}")).collect::<Vec<_>>().join(",");
    format!("{}|{}|{}", f(&s.u), f(&s.v), f(&s.x))
}

/// emit the certificate DAG reachable from the root following the chosen
/// side at prover nodes and ALL children at adversary nodes
fn certificate(g: &Game, n: usize, root: &State) -> String {
    let mut out = String::new();
    let mut seen = HashSet::new();
    let mut stack = vec![root.clone()];
    let mut lines = Vec::new();
    while let Some(s) = stack.pop() {
        if !seen.insert(key(&s)) {
            continue;
        }
        let node = &g.memo[&s];
        let mut line = String::new();
        write!(
            line,
            "{{\"key\":\"{}\",\"dims\":[{},{},{}],\"value\":{},\"choice\":{},\"phi\":{},\"leaf\":[{},{},{}]",
            key(&s), node.dims.0, node.dims.1, node.dims.2, node.value, node.choice, node.phi, node.leaf[0], node.leaf[1], node.leaf[2]
        )
        .unwrap();
        if node.choice != 0 {
            let cur = match node.choice {
                1 => &s.u,
                2 => &s.v,
                _ => &s.x,
            };
            let t = quotient(&g.t0, &s.u, &s.v, &s.x);
            let supp = support(&t, node.choice, cur, g.d);
            let mut exts = Vec::new();
            let mut seen = HashSet::new();
            for v in elements(&supp) {
                if dot(node.phi, v) != 1 {
                    continue;
                }
                let mut rows = cur.clone();
                rows.push(v);
                let e = rref(&rows);
                if e.len() == cur.len() || !seen.insert(e.clone()) {
                    continue;
                }
                exts.push(e);
            }
            let mut ks = Vec::new();
            for e in exts {
                let child = match node.choice {
                    1 => State { u: e, v: s.v.clone(), x: s.x.clone() },
                    2 => State { u: s.u.clone(), v: e, x: s.x.clone() },
                    _ => State { u: s.u.clone(), v: s.v.clone(), x: e },
                };
                ks.push(format!("\"{}\"", key(&child)));
                stack.push(child);
            }
            write!(line, ",\"children\":[{}]", ks.join(",")).unwrap();
        }
        line.push('}');
        lines.push(line);
    }
    writeln!(out, "{{\"n\":{n},\"root\":\"{}\",\"nodes\":[", key(root)).unwrap();
    out.push_str(&lines.join(",\n"));
    out.push_str("\n]}\n");
    out
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let get = |k: &str| args.iter().position(|a| a == k).and_then(|i| args.get(i + 1).cloned());
    let n: usize = get("--n").and_then(|v| v.parse().ok()).unwrap_or(2);
    let cert = get("--cert");
    let t0 = matmul_tensor(n);
    let d = n * n;
    let t = Instant::now();
    let mut g = Game { t0, d, memo: HashMap::new() };
    let root = State { u: vec![], v: vec![], x: vec![] };
    let value = g.val(&root);
    let node = g.memo[&root].clone();
    println!(
        "subgame <{n},{n},{n}> over F_2: game value = {value} (root choice: {}, root flattenings {:?}); {} states memoized in {:.2}s",
        ["leaf", "kill on A", "kill on B", "kill on C"][node.choice as usize],
        node.leaf,
        g.memo.len(),
        t.elapsed().as_secs_f64()
    );
    println!("=> rank_F2(<{n},{n},{n}>) >= {value} by the substitution game");
    if let Some(path) = cert {
        let c = certificate(&g, n, &root);
        std::fs::write(&path, &c).expect("write cert");
        println!("certificate: {} ({} bytes)", path, c.len());
    }
}
