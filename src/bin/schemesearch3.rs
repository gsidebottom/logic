// CDCL(T) prototype, stage 2: 3x3 scaling probe. Product-level UNSAT ladder
// for <3,3,3> over F_2 with lazy product enumeration (511^3 products — no
// materialized list) and residual-rank theory pruning.
//
// Measurement: the r-ceiling — the largest r whose ladder EXHAUSTS (UNSAT)
// within budget. Every r <= 19 is known UNSAT (Wang's verified certificate:
// rank >= 20), so each rung is a free gate and each exhaustion reproduces
// rank >= r+1 independently. Flattening alone refutes r <= 8 at the root.
//
// Tensor: 729 bits in [u64; 12], bit(a,b,c) = a*81 + b*9 + c, with
// A=(i,j) a=3i+j, B=(j,k) b=3j+k, C=(k,i) c=3k+i (trace convention).
//
// Symmetry (sound, over-counting form): the sandwich group acts on alpha
// through (P,Q) alone, so every scheme has an image in which SOME product's
// alpha is one of the three rank representatives {E11, E11+E22, I}. The
// search enumerates that product first (alpha restricted to the reps, beta
// and gamma free), then the remaining r-1 products over the FULL space in
// strictly decreasing id order, excluding the first. Schemes are enumerated
// at most r times each — redundancy costs time, never completeness. No
// id-order constraint ties the first product to the rest (the stage-1
// unsound-cut lesson).
//
// Propagators: per-node flattening-rank prune (three 9x81 F2 ranks) and an
// optional sound 1-ply substitution probe (--sub-probe): for each side, fold
// the LAST active pivot over its full 2^8 lambda range and take
// 1 + min lambda flatten; depth-gated (--probe-min-remaining) because each
// probe costs ~768 flatten evaluations.

use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::time::Instant;

const W: usize = 12; // 729 bits
type T3 = [u64; W];

fn bit(a: usize, b: usize, c: usize) -> usize {
    a * 81 + b * 9 + c
}

fn set(t: &mut T3, i: usize) {
    t[i / 64] |= 1u64 << (i % 64);
}

fn get(t: &T3, i: usize) -> bool {
    t[i / 64] >> (i % 64) & 1 == 1
}

fn xor(t: &mut T3, o: &T3) {
    for i in 0..W {
        t[i] ^= o[i];
    }
}

fn is_zero(t: &T3) -> bool {
    t.iter().all(|&w| w == 0)
}

fn build_t3() -> T3 {
    let mut t = [0u64; W];
    for i in 0..3 {
        for j in 0..3 {
            for k in 0..3 {
                set(&mut t, bit(3 * i + j, 3 * j + k, 3 * k + i));
            }
        }
    }
    t
}

fn product_mask(alpha: u32, beta: u32, gamma: u32) -> T3 {
    let mut m = [0u64; W];
    for a in 0..9 {
        if alpha >> a & 1 == 0 {
            continue;
        }
        for b in 0..9 {
            if beta >> b & 1 == 0 {
                continue;
            }
            // gamma occupies 9 consecutive bits at offset a*81 + b*9
            let off = a * 81 + b * 9;
            let (w, s) = (off / 64, off % 64);
            m[w] |= (gamma as u64) << s;
            if s > 55 {
                m[w + 1] |= (gamma as u64) >> (64 - s);
            }
        }
    }
    m
}

fn rank9(rows: &mut [u128; 9]) -> u32 {
    let mut rk = 0usize;
    for c in (0..81).rev() {
        if let Some(p) = (rk..9).find(|&i| rows[i] >> c & 1 == 1) {
            rows.swap(rk, p);
            for i in 0..9 {
                if i != rk && rows[i] >> c & 1 == 1 {
                    rows[i] ^= rows[rk];
                }
            }
            rk += 1;
            if rk == 9 {
                break;
            }
        }
    }
    rk as u32
}

fn extract81(t: &T3, off: usize) -> u128 {
    // 81 bits starting at bit offset `off`
    let mut v = 0u128;
    for i in 0..2 {
        let w = (off + i * 64) / 64;
        let s = (off) % 64;
        let _ = s;
        let _ = w;
        let _ = i;
        break;
    }
    // simple loop (correctness first; optimize later)
    for b in 0..81 {
        if get(t, off + b) {
            v |= 1u128 << b;
        }
    }
    v
}

fn flatten_ranks(t: &T3) -> [u32; 3] {
    let mut fa = [0u128; 9];
    let mut fb = [0u128; 9];
    let mut fc = [0u128; 9];
    for a in 0..9 {
        fa[a] = extract81(t, a * 81);
    }
    for a in 0..9 {
        for b in 0..9 {
            for c in 0..9 {
                if get(t, bit(a, b, c)) {
                    fb[b] |= 1u128 << (a * 9 + c);
                    fc[c] |= 1u128 << (a * 9 + b);
                }
            }
        }
    }
    [rank9(&mut fa), rank9(&mut fb), rank9(&mut fc)]
}

fn max_flatten(t: &T3) -> u32 {
    *flatten_ranks(t).iter().max().unwrap()
}

/// slice mask of coordinate p on a side (0=A, 1=B, 2=C)
fn side_slice(t: &T3, side: usize, p: usize) -> T3 {
    let mut m = [0u64; W];
    for a in 0..9 {
        for b in 0..9 {
            for c in 0..9 {
                let on = match side {
                    0 => a == p,
                    1 => b == p,
                    _ => c == p,
                };
                if on && get(t, bit(a, b, c)) {
                    set(&mut m, bit(a, b, c));
                }
            }
        }
    }
    m
}

/// move a p-slice mask to coordinate q on the same side
fn shift_slice(m: &T3, side: usize, p: usize, q: usize) -> T3 {
    let mut out = [0u64; W];
    for a in 0..9 {
        for b in 0..9 {
            for c in 0..9 {
                if !get(m, bit(a, b, c)) {
                    continue;
                }
                let (na, nb, nc) = match side {
                    0 => (q, b, c),
                    1 => (a, q, c),
                    _ => (a, b, q),
                };
                debug_assert!(match side {
                    0 => a == p,
                    1 => b == p,
                    _ => c == p,
                });
                set(&mut out, bit(na, nb, nc));
            }
        }
    }
    out
}

/// Sound 1-ply substitution bound: for each side, take the LAST active pivot
/// p and fold it over ALL 2^8 lambda vectors onto the other coordinates;
/// rank >= 1 + min over lambda of flatten(folded). Max over sides.
fn sub_bound(t: &T3, best_so_far: u32, target: u32) -> u32 {
    let mut best = best_so_far;
    for side in 0..3usize {
        let p = match (0..9).rev().find(|&p| !is_zero(&side_slice(t, side, p))) {
            Some(p) => p,
            None => continue,
        };
        let sp = side_slice(t, side, p);
        let mut base = *t;
        xor(&mut base, &sp); // delete the p-slice
        let others: Vec<usize> = (0..9).filter(|&i| i != p).collect();
        let shifted: Vec<T3> = others.iter().map(|&q| shift_slice(&sp, side, p, q)).collect();
        let mut worst = u32::MAX;
        for lam in 0..256u32 {
            let mut m = base;
            for (bi, sh) in shifted.iter().enumerate() {
                if lam >> bi & 1 == 1 {
                    xor(&mut m, sh);
                }
            }
            worst = worst.min(max_flatten(&m));
            if 1 + worst <= best {
                break;
            }
        }
        if worst != u32::MAX {
            best = best.max(1 + worst);
        }
        if best >= target {
            return best; // enough to prune
        }
    }
    best
}

struct Shared {
    capped: AtomicBool,
    found: AtomicBool,
    nodes: AtomicU64,
    prune_flat: AtomicU64,
    prune_sub: AtomicU64,
    work: AtomicUsize,
}

struct Search<'a> {
    nodes: u64,
    prune_flat: u64,
    prune_sub: u64,
    sub_probe: bool,
    probe_min_remaining: u32,
    cap: f64,
    start: Instant,
    capped: bool,
    shared: &'a Shared,
}

impl<'a> Search<'a> {
    /// descending lazy iteration over (alpha, beta, gamma), all >= 1,
    /// strictly below `max` (lex on the packed triple), excluding `skip`
    fn dfs(&mut self, r: &T3, remaining: u32, max: u32, skip: u32) -> bool {
        if is_zero(r) {
            return true; // SAT: scheme completed (not expected on this ladder)
        }
        if remaining == 0 {
            return false;
        }
        self.nodes += 1;
        if self.nodes % (1 << 16) == 0 {
            if self.start.elapsed().as_secs_f64() > self.cap {
                self.capped = true;
                self.shared.capped.store(true, Ordering::Relaxed);
            }
            if self.shared.capped.load(Ordering::Relaxed)
                || self.shared.found.load(Ordering::Relaxed)
            {
                self.capped = self.capped || self.shared.capped.load(Ordering::Relaxed);
                return false;
            }
        }
        let fr = max_flatten(r);
        if fr > remaining {
            self.prune_flat += 1;
            return false;
        }
        if self.sub_probe && remaining >= self.probe_min_remaining {
            if sub_bound(r, fr, remaining + 1) > remaining {
                self.prune_sub += 1;
                return false;
            }
        }
        let mut id = max;
        while id > 0 {
            id -= 1;
            let (al, be, ga) = (id >> 18 & 511, id >> 9 & 511, id & 511);
            if al == 0 || be == 0 || ga == 0 {
                // skip ids with a zero component: jump to the next valid id
                if ga == 0 {
                    continue;
                }
                continue;
            }
            if id == skip {
                continue;
            }
            let m = product_mask(al, be, ga);
            let mut nr = *r;
            xor(&mut nr, &m);
            if self.dfs(&nr, remaining - 1, id, skip) {
                return true;
            }
            if self.capped {
                return false;
            }
        }
        false
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let get = |k: &str| args.iter().position(|a| a == k).and_then(|i| args.get(i + 1).cloned());
    let r: u32 = get("--r").and_then(|v| v.parse().ok()).unwrap_or(9);
    let cap: f64 = get("--time").and_then(|v| v.parse().ok()).unwrap_or(600.0);
    let sub_probe = args.iter().any(|a| a == "--sub-probe");
    let probe_min_remaining: u32 =
        get("--probe-min-remaining").and_then(|v| v.parse().ok()).unwrap_or(3);

    let t = build_t3();
    assert_eq!(max_flatten(&t), 9, "matmul flattening sanity");

    // alpha rank representatives (as 9-bit row-major 3x3 matrices):
    // E11 = 0b000000001, E11+E22 = 0b000010001, I = 0b100010001
    let alpha_reps: [u32; 3] = [0b000_000_001, 0b000_010_001, 0b100_010_001];

    struct Tally { nodes: u64, prune_flat: u64, prune_sub: u64, capped: bool }
    let mut s = Tally { nodes: 0, prune_flat: 0, prune_sub: 0, capped: false };

    let full: u32 = (511 << 18) | (511 << 9) | 511;
    let threads: usize = get("--threads").and_then(|v| v.parse().ok()).unwrap_or(12);
    // work units: (alpha_rep, beta) pairs, each covering the 511 gamma roots
    let units: Vec<(u32, u32)> = alpha_reps
        .iter()
        .flat_map(|&al| (1..512u32).rev().map(move |be| (al, be)))
        .collect();
    let shared = Shared {
        capped: AtomicBool::new(false),
        found: AtomicBool::new(false),
        nodes: AtomicU64::new(0),
        prune_flat: AtomicU64::new(0),
        prune_sub: AtomicU64::new(0),
        work: AtomicUsize::new(0),
    };
    let start = Instant::now();
    std::thread::scope(|scope| {
        for _ in 0..threads {
            scope.spawn(|| {
                let mut w = Search {
                    nodes: 0,
                    prune_flat: 0,
                    prune_sub: 0,
                    sub_probe,
                    probe_min_remaining,
                    cap,
                    start,
                    capped: false,
                    shared: &shared,
                };
                loop {
                    let u = shared.work.fetch_add(1, Ordering::Relaxed);
                    if u >= units.len()
                        || shared.capped.load(Ordering::Relaxed)
                        || shared.found.load(Ordering::Relaxed)
                    {
                        break;
                    }
                    let (al, be) = units[u];
                    for ga in (1..512u32).rev() {
                        let first_id = (al << 18) | (be << 9) | ga;
                        let m = product_mask(al, be, ga);
                        let mut nr = t;
                        xor(&mut nr, &m);
                        if w.dfs(&nr, r - 1, full + 1, first_id) {
                            shared.found.store(true, Ordering::Relaxed);
                            break;
                        }
                        if shared.capped.load(Ordering::Relaxed)
                            || shared.found.load(Ordering::Relaxed)
                        {
                            break;
                        }
                    }
                }
                shared.nodes.fetch_add(w.nodes, Ordering::Relaxed);
                shared.prune_flat.fetch_add(w.prune_flat, Ordering::Relaxed);
                shared.prune_sub.fetch_add(w.prune_sub, Ordering::Relaxed);
            });
        }
    });
    let found = shared.found.load(Ordering::Relaxed);
    s.nodes = shared.nodes.load(Ordering::Relaxed);
    s.prune_flat = shared.prune_flat.load(Ordering::Relaxed);
    s.prune_sub = shared.prune_sub.load(Ordering::Relaxed);
    s.capped = shared.capped.load(Ordering::Relaxed);

    let el = start.elapsed().as_secs_f64();
    if found {
        println!("r={r}: SAT?! — a scheme surfaced; INVESTIGATE (should be impossible for r<20)");
    } else if s.capped {
        println!(
            "r={r}: CAP ({} nodes, {:.1}s, prunes flat {} sub {})",
            s.nodes, el, s.prune_flat, s.prune_sub
        );
    } else {
        println!(
            "r={r}: UNSAT — exhausted ({} nodes, {:.1}s, prunes flat {} sub {}) => rank_F2(<3,3,3>) > {}",
            s.nodes,
            el,
            s.prune_flat,
            s.prune_sub,
            r
        );
    }
}
