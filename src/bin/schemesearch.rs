// CDCL(T) prototype, stage 1: product-level exhaustive scheme search for
// 2x2 matrix multiplication over F_2 with a residual-rank theory propagator.
//
// Thesis (2026-08-26 discussion): plain CNF CDCL dies on Brent equations
// because resolution cannot express rank/dimension arguments; a search that
// decides whole PRODUCTS (rank-one tensors) and prunes with rank lower
// bounds on the residual tensor imports exactly the reasoning CDCL lacks.
// Stage 1 measures that claim at the smallest certified instance:
//   rank 6: must EXHAUST (UNSAT)  — matches our hydra_satsuma dsr-trim result
//   rank 7: must find a scheme    — matches Strassen (orbit)
// The XOR/GE box of the full architecture is implicit here: the residual IS
// the XOR of T with the chosen products; parity reasoning is native.
//
// State: residual R = T xor (chosen product masks), tensor as 64 bits
// (a,b,c) in 4x4x4, bit index a*16 + b*4 + c, A=(i,j) a=2i+j, B=(j,k)
// b=2j+k, C=(k,i) c=2k+i (trace convention, matching matmul/brent.py).
//
// Search: strictly decreasing product ids (canonical sequence per product
// SET; duplicate products cancel over F_2 so sets suffice), first product
// restricted to alpha-canonical representatives (alpha in {E11, I} — the two
// GL2xGL2 orbits of nonzero 2x2 matrices; the sandwich group acts on alpha
// through (P,Q) alone, so this is a sound WLOG cut of 15 -> 2).
//
// Propagator: prune when any of the three flattening ranks of R exceeds the
// remaining product budget (rank(R) >= flatten rank; each product lowers
// rank by at most 1).

use std::time::Instant;

const D: usize = 4; // 2x2 => 4-dim sides

fn build_t() -> u64 {
    let mut t = 0u64;
    for i in 0..2u64 {
        for j in 0..2u64 {
            for k in 0..2u64 {
                let a = 2 * i + j;
                let b = 2 * j + k;
                let c = 2 * k + i;
                t |= 1u64 << (a * 16 + b * 4 + c);
            }
        }
    }
    t
}

fn product_mask(alpha: u32, beta: u32, gamma: u32) -> u64 {
    let mut m = 0u64;
    for a in 0..D {
        if alpha >> a & 1 == 0 {
            continue;
        }
        for b in 0..D {
            if beta >> b & 1 == 0 {
                continue;
            }
            for c in 0..D {
                if gamma >> c & 1 == 1 {
                    m |= 1u64 << (a * 16 + b * 4 + c);
                }
            }
        }
    }
    m
}

/// 1-ply substitution lower bound: 1 + min over one killed direction of the
/// restricted residual's flatten bound (max over the three sides' best pivot).
/// Sound: substitution lemma, kill an active variable on the chosen side.
fn slice(r: u64, side: usize, p: usize) -> u64 {
    // mask of the p-th coordinate slice on the given side
    match side {
        0 => r & (0xFFFFu64 << (p * 16)),
        1 => {
            let mut m = 0u64;
            for a in 0..4 {
                m |= r & (0xFu64 << (a * 16 + p * 4));
            }
            m
        }
        _ => {
            let mut m = 0u64;
            for ab in 0..16 {
                m |= r & (1u64 << (ab * 4 + p));
            }
            m
        }
    }
}

fn shift_slice(m: u64, side: usize, from: usize, to: usize) -> u64 {
    // move a from-slice mask onto the to-slice positions (same side)
    let d = |a: usize, b: usize| a as i32 - b as i32;
    let sh = match side {
        0 => d(to, from) * 16,
        1 => d(to, from) * 4,
        _ => d(to, from),
    };
    if sh >= 0 { m << sh } else { m >> -sh }
}

/// Sound 1-ply substitution bound: rank(R) >= 1 + max over (side, pivot p
/// with active slice) of min over ALL 2^3 foldings lambda of the flatten
/// bound of R with slice_i ^= lambda_i * slice_p folded in and slice_p
/// deleted (substitution lemma with the adversary's full lambda range).
fn sub_bound(r: u64) -> u32 {
    if r == 0 {
        return 0;
    }
    let mut best = *flatten_ranks(r).iter().max().unwrap();
    for side in 0..3usize {
        for p in 0..4usize {
            let sp = slice(r, side, p);
            if sp == 0 {
                continue; // inactive: no credit for killing it
            }
            let others: Vec<usize> = (0..4).filter(|&i| i != p).collect();
            let base = r & !slice(r, side, p);
            let mut worst = u32::MAX;
            for lam in 0..8u32 {
                let mut m = base;
                for (bi, &i) in others.iter().enumerate() {
                    if lam >> bi & 1 == 1 {
                        m ^= shift_slice(sp, side, p, i);
                    }
                }
                worst = worst.min(*flatten_ranks(m).iter().max().unwrap());
                if worst + 1 <= best {
                    break; // cannot improve best
                }
            }
            best = best.max(1 + worst);
        }
    }
    best
}

fn rank4(rows: [u16; 4]) -> u32 {
    let mut rows = rows;
    let mut rk = 0;
    for c in (0..16).rev() {
        if let Some(p) = (rk..4).find(|&i| rows[i] >> c & 1 == 1) {
            rows.swap(rk, p);
            for i in 0..4 {
                if i != rk && rows[i] >> c & 1 == 1 {
                    rows[i] ^= rows[rk];
                }
            }
            rk += 1;
        }
    }
    rk as u32
}

/// flattening ranks of the residual on the three axes
fn flatten_ranks(r: u64) -> [u32; 3] {
    let mut fa = [0u16; 4];
    let mut fb = [0u16; 4];
    let mut fc = [0u16; 4];
    for a in 0..4 {
        fa[a] = ((r >> (a * 16)) & 0xFFFF) as u16;
    }
    for bit in 0..64u32 {
        if r >> bit & 1 == 0 {
            continue;
        }
        let (a, b, c) = ((bit / 16) as usize, (bit / 4 % 4) as usize, (bit % 4) as usize);
        fb[b] |= 1 << (a * 4 + c);
        fc[c] |= 1 << (a * 4 + b);
    }
    [rank4(fa), rank4(fb), rank4(fc)]
}

struct Search {
    products: Vec<(u64, u32, u32, u32)>, // (mask, alpha, beta, gamma), id = index
    suffix_or: Vec<u64>, // suffix_or[i] = OR of masks of ids 0..i (exclusive)
    sub_probe: bool,     // 1-ply substitution probe on top of flattenings
    nodes: u64,
    prune_flat: u64,
    prune_cover: u64,
    prune_sub: u64,
    cap: f64,
    start: Instant,
    capped: bool,
    witness: Option<Vec<(u32, u32, u32)>>,
}

impl Search {
    fn dfs(&mut self, r: u64, remaining: u32, max_id: usize, chosen: &mut Vec<usize>) -> bool {
        if r == 0 {
            self.witness = Some(chosen.iter().map(|&i| {
                let p = self.products[i];
                (p.1, p.2, p.3)
            }).collect());
            return true;
        }
        if remaining == 0 {
            return false;
        }
        self.nodes += 1;
        if self.nodes % (1 << 22) == 0 && self.start.elapsed().as_secs_f64() > self.cap {
            self.capped = true;
            return false;
        }
        // coverage prune: a residual bit no remaining product can touch is fatal
        if r & !self.suffix_or[max_id] != 0 {
            self.prune_cover += 1;
            return false;
        }
        let fr = flatten_ranks(r);
        if fr.iter().any(|&f| f > remaining) {
            self.prune_flat += 1;
            return false;
        }
        if self.sub_probe && sub_bound(r) > remaining {
            self.prune_sub += 1;
            return false;
        }
        for id in (0..max_id).rev() {
            let m = self.products[id].0;
            chosen.push(id);
            if self.dfs(r ^ m, remaining - 1, id, chosen) {
                return true;
            }
            chosen.pop();
            if self.capped {
                return false;
            }
        }
        false
    }
}

/// independent witness check: rebuild the tensor entrywise from the triples
fn verify_witness(w: &[(u32, u32, u32)], t: u64) -> bool {
    let mut acc = 0u64;
    for a in 0..D {
        for b in 0..D {
            for c in 0..D {
                let mut bit = 0u64;
                for &(al, be, ga) in w {
                    bit ^= ((al as u64 >> a) & (be as u64 >> b) & (ga as u64 >> c)) & 1;
                }
                acc |= bit << (a * 16 + b * 4 + c);
            }
        }
    }
    acc == t
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let get = |k: &str| args.iter().position(|a| a == k).and_then(|i| args.get(i + 1).cloned());
    let r: u32 = get("--r").and_then(|v| v.parse().ok()).unwrap_or(6);
    let cap: f64 = get("--time").and_then(|v| v.parse().ok()).unwrap_or(600.0);
    let no_first_canon = args.iter().any(|a| a == "--no-first-canon");

    let t = build_t();
    // product list, id order = packed (alpha,beta,gamma); ids descending in DFS
    let mut products = Vec::new();
    for alpha in 1..16u32 {
        for beta in 1..16u32 {
            for gamma in 1..16u32 {
                products.push((product_mask(alpha, beta, gamma), alpha, beta, gamma));
            }
        }
    }
    let n_all = products.len();

    // NOTE: an earlier alpha-canonical first-product cut was UNSOUND (the
    // sandwich normalizes SOME product's alpha, not the highest-id one) and
    // produced a false UNSAT at r=7 — caught by the known-value gate.
    // Full first range until an SMS-style set-prefix canon replaces it.
    let _ = no_first_canon;
    let first_ids: Vec<usize> = (0..n_all).collect();

    let mut suffix_or = vec![0u64; n_all + 1];
    for i in 0..n_all {
        suffix_or[i + 1] = suffix_or[i] | products[i].0;
    }
    let mut s = Search {
        products,
        suffix_or,
        sub_probe: args.iter().any(|a| a == "--sub-probe"),
        nodes: 0,
        prune_flat: 0,
        prune_cover: 0,
        prune_sub: 0,
        cap,
        start: Instant::now(),
        capped: false,
        witness: None,
    };

    // top level: first product from the canonical list, rest strictly below it
    let mut found = false;
    for &fid in first_ids.iter().rev() {
        let m = s.products[fid].0;
        let mut chosen = vec![fid];
        if s.dfs(t ^ m, r - 1, fid, &mut chosen) {
            found = true;
            break;
        }
        if s.capped {
            break;
        }
    }

    let el = s.start.elapsed().as_secs_f64();
    if found {
        let w = s.witness.unwrap();
        let ok = verify_witness(&w, t);
        println!(
            "r={r}: SAT — scheme found, independent verify {}  ({} nodes, {:.2}s)",
            if ok { "OK" } else { "FAILED" },
            s.nodes,
            el
        );
        for (i, (a, b, g)) in w.iter().enumerate() {
            println!("  p{}: alpha={a:04b} beta={b:04b} gamma={g:04b}", i + 1);
        }
        assert!(ok, "witness failed independent verification");
    } else if s.capped {
        println!(
            "r={r}: CAP ({} nodes, {:.2}s, prunes flat {} cover {} sub {})",
            s.nodes, el, s.prune_flat, s.prune_cover, s.prune_sub
        );
    } else {
        println!(
            "r={r}: UNSAT — exhausted ({} nodes, {:.2}s, prunes flat {} cover {} sub {})",
            s.nodes, el, s.prune_flat, s.prune_cover, s.prune_sub
        );
    }
}
