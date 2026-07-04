//! Parallel flip-graph search over mod-2 matrix-multiplication schemes
//! (Kauers–Moosbauer moves), Rust port of the validated matmul/flip.py
//! pipeline — built for the 4×4 descend campaign: reduction-greedy walks
//! down from a high-rank seed (e.g. the trivial 64-product scheme),
//! saving, deduping and lift-testing every landing at low rank.
//!
//! Moves (validity-preserving by construction; every landing is
//! re-verified against the Brent equations before being reported):
//!   flip:   two summands equal in one slot exchange material in the
//!           other two; a zeroed factor deletes its summand (rank −1).
//!   split:  rank +1, aimed at an existing summand's factor so the child
//!           shares with a non-twin (twin-only sharing is sterile).
//!
//! Parallelism: independent worker trajectories (one RNG each) stream
//! landings over a channel to a single collector that verifies,
//! canon-dedupes (sorted-summand key), writes files, and (optionally)
//! shells out to matmul/lift.py for the ±1-liftability lottery.

use crate::anf::{brent, verify, Anf, Dims, Rng};
use std::collections::{HashMap, HashSet};
use std::io::Write;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{mpsc, Mutex};
use std::time::Instant;

pub type Summand = [u16; 3];

#[derive(Clone, Copy)]
pub struct FlipCfg {
    pub n1: usize,
    pub n2: usize,
    pub n3: usize,
    pub save_at: usize,
    pub record: usize, // strictly-below => jackpot banner
    pub minutes: f64,
    pub threads: usize,
    pub seek_attempts: usize,
    pub stall_limit: usize,
    pub seed: u64,
}

pub fn factor_sizes(c: &FlipCfg) -> (usize, usize, usize) {
    (c.n1 * c.n2, c.n2 * c.n3, c.n1 * c.n3)
}

pub fn bits_to_summands(bits: &[u8], c: &FlipCfg) -> Vec<Summand> {
    let (sa, sb, sg) = factor_sizes(c);
    let per = sa + sb + sg;
    assert_eq!(bits.len() % per, 0);
    let r = bits.len() / per;
    let (na, nb) = (r * sa, r * sb);
    let mut out = Vec::with_capacity(r);
    for m in 0..r {
        let mut s: Summand = [0, 0, 0];
        for k in 0..sa {
            s[0] |= (bits[m * sa + k] as u16) << k;
        }
        for k in 0..sb {
            s[1] |= (bits[na + m * sb + k] as u16) << k;
        }
        for k in 0..sg {
            s[2] |= (bits[na + nb + m * sg + k] as u16) << k;
        }
        out.push(s);
    }
    out
}

pub fn summands_to_bits(s: &[Summand], c: &FlipCfg) -> Vec<u8> {
    let (sa, sb, sg) = factor_sizes(c);
    let r = s.len();
    let (na, nb) = (r * sa, r * sb);
    let mut bits = vec![0u8; r * (sa + sb + sg)];
    for (m, sm) in s.iter().enumerate() {
        for k in 0..sa {
            bits[m * sa + k] = ((sm[0] >> k) & 1) as u8;
        }
        for k in 0..sb {
            bits[na + m * sb + k] = ((sm[1] >> k) & 1) as u8;
        }
        for k in 0..sg {
            bits[na + nb + m * sg + k] = ((sm[2] >> k) & 1) as u8;
        }
    }
    bits
}

/// one random flip; drops zeroed summands. Returns Some(true) if the
/// rank dropped, Some(false) for a plain flip, None if no eligible pair
/// was sampled. `allow_zero=false` skips zero-producing (reducing) flips
/// so exploration diffuses instead of annihilating fresh splits.
#[inline]
pub fn random_flip(
    s: &mut Vec<Summand>,
    rng: &mut Rng,
    allow_zero: bool,
) -> Option<bool> {
    let r = s.len();
    for _ in 0..64 {
        let slot = rng.below(3);
        let i = rng.below(r);
        let j = rng.below(r);
        if i == j || s[i][slot] != s[j][slot] || s[i][slot] == 0 {
            continue;
        }
        let (mut o1, mut o2) = match slot {
            0 => (1, 2),
            1 => (0, 2),
            _ => (0, 1),
        };
        if rng.f64() < 0.5 {
            std::mem::swap(&mut o1, &mut o2);
        }
        let would_zero = s[i][o1] == s[j][o1] || s[i][o2] == s[j][o2];
        if would_zero && !allow_zero {
            continue;
        }
        s[i][o1] ^= s[j][o1];
        s[j][o2] ^= s[i][o2];
        if s[i].contains(&0) || s[j].contains(&0) {
            s.retain(|x| !x.contains(&0));
            return Some(true);
        }
        return Some(false);
    }
    None
}

/// split (rank +1) aimed at another summand's factor so the child shares
/// with a non-twin summand.
pub fn split_toward(s: &mut Vec<Summand>, rng: &mut Rng) {
    let r = s.len();
    for _ in 0..64 {
        let m = rng.below(r);
        let k = rng.below(r);
        let slot = rng.below(3);
        let f = s[m][slot];
        let x = s[k][slot];
        if k == m || x == f || x == 0 || f == 0 {
            continue;
        }
        let mut child = s[m];
        s[m][slot] = x;
        child[slot] = f ^ x;
        s.push(child);
        return;
    }
    // fallback: random split of a random summand
    let m = rng.below(r);
    let slot = rng.below(3);
    let f = s[m][slot];
    let x = (rng.next_u64() as u16) & 0xffff;
    let x = if x == 0 || x == f { f ^ 1 } else { x };
    let mut child = s[m];
    s[m][slot] = x;
    child[slot] = f ^ x;
    s.push(child);
}

pub fn seek_reduction(
    s: &mut Vec<Summand>,
    rng: &mut Rng,
    attempts: usize,
) -> bool {
    for _ in 0..attempts {
        if random_flip(s, rng, true) == Some(true) {
            return true;
        }
    }
    false
}

pub struct Stats {
    pub flips: AtomicU64,
    pub reductions: AtomicU64,
    pub trajectories: AtomicU64,
    pub landings: AtomicU64,
}

/// the parallel descend campaign. Returns (per-rank new-scheme counts,
/// min rank reached).
pub fn descend_campaign<F>(
    seed_summands: Vec<Summand>,
    cfg: FlipCfg,
    mut on_new: F,
) -> (HashMap<usize, usize>, usize)
where
    F: FnMut(usize, &[u8], usize),
    // (rank, bits, seq-within-rank); called after verification + dedupe
{
    let stop = AtomicBool::new(false);
    let stats = Stats {
        flips: AtomicU64::new(0),
        reductions: AtomicU64::new(0),
        trajectories: AtomicU64::new(0),
        landings: AtomicU64::new(0),
    };
    let (tx, rx) = mpsc::channel::<Vec<Summand>>();
    let t0 = Instant::now();
    // shared frontier: low-rank states accumulate; restarts draw from
    // here so effort concentrates at the bottom of the funnel instead of
    // re-paying the easy high-rank descent per trajectory.
    let frontier: Mutex<Vec<Vec<Summand>>> = Mutex::new(Vec::new());
    let frontier_rank = seed_summands.len().min(cfg.save_at + 4);

    std::thread::scope(|scope| {
        let mut result: (HashMap<usize, usize>, usize) =
            (HashMap::new(), seed_summands.len());
        for w in 0..cfg.threads {
            let seed = seed_summands.clone();
            let tx = tx.clone();
            let stop = &stop;
            let stats = &stats;
            let frontier = &frontier;
            let cfg = cfg;
            scope.spawn(move || {
                let mut rng =
                    Rng::new(cfg.seed.wrapping_add(w as u64).wrapping_mul(
                        0x9e3779b97f4a7c15,
                    ));
                let mut cur = seed.clone();
                let mut stall = 0usize;
                let mut nf = 0u64;
                let mut deposited = usize::MAX;
                loop {
                    if nf % 512 == 0 && stop.load(Ordering::Relaxed) {
                        break;
                    }
                    // rank-adaptive seek effort: deep pockets down low
                    let rk = cur.len();
                    let mult = if rk <= cfg.save_at + 2 {
                        25
                    } else if rk <= cfg.save_at + 5 {
                        4
                    } else {
                        1
                    };
                    if seek_reduction(
                        &mut cur,
                        &mut rng,
                        cfg.seek_attempts * mult,
                    ) {
                        stats.reductions.fetch_add(1, Ordering::Relaxed);
                        stall = 0;
                        let rk = cur.len();
                        if rk <= frontier_rank && rk < deposited {
                            deposited = rk;
                            let mut fr = frontier.lock().unwrap();
                            fr.push(cur.clone());
                            if fr.len() > 256 {
                                // keep the lowest-rank half
                                fr.sort_by_key(|s| s.len());
                                fr.truncate(128);
                            }
                        }
                        if rk <= cfg.save_at {
                            stats.landings.fetch_add(1, Ordering::Relaxed);
                            let _ = tx.send(cur.clone());
                        }
                    } else {
                        let n = 200 + rng.below(1000);
                        for _ in 0..n {
                            if random_flip(&mut cur, &mut rng, false)
                                == Some(false)
                            {
                                nf += 1;
                            }
                        }
                        stats.flips.fetch_add(n as u64, Ordering::Relaxed);
                        stall += 1;
                        if stall > cfg.stall_limit {
                            stats
                                .trajectories
                                .fetch_add(1, Ordering::Relaxed);
                            // restart from the frontier when it exists:
                            // perturb up (splits+diffusion), re-descend
                            let pick = {
                                let fr = frontier.lock().unwrap();
                                if fr.is_empty() {
                                    None
                                } else {
                                    Some(fr[rng.below(fr.len())].clone())
                                }
                            };
                            match pick {
                                Some(f) if rng.f64() < 0.8 => {
                                    cur = f;
                                    for _ in 0..2 + rng.below(4) {
                                        split_toward(&mut cur, &mut rng);
                                    }
                                    for _ in 0..500 + rng.below(2000) {
                                        random_flip(
                                            &mut cur, &mut rng, false,
                                        );
                                    }
                                }
                                _ => cur = seed.clone(),
                            }
                            deposited = usize::MAX;
                            stall = 0;
                        }
                    }
                }
            });
        }
        drop(tx);

        // collector (this thread)
        let mut anfs: HashMap<usize, Anf> = HashMap::new();
        let mut pool: HashSet<Vec<Summand>> = HashSet::new();
        let mut counts: HashMap<usize, usize> = HashMap::new();
        let mut min_rank = seed_summands.len();
        let mut last_report = Instant::now();
        loop {
            let el = t0.elapsed().as_secs_f64();
            if el > cfg.minutes * 60.0 {
                stop.store(true, Ordering::Relaxed);
                break;
            }
            match rx.recv_timeout(std::time::Duration::from_millis(500)) {
                Ok(summ) => {
                    let rk = summ.len();
                    let mut key = summ.clone();
                    key.sort_unstable();
                    if pool.contains(&key) {
                        continue;
                    }
                    let bits = summands_to_bits(&summ, &cfg);
                    let anf = anfs.entry(rk).or_insert_with(|| {
                        brent(Dims {
                            n1: cfg.n1,
                            n2: cfg.n2,
                            n3: cfg.n3,
                            r: rk,
                        })
                    });
                    if verify(anf, &bits) != 0 {
                        eprintln!("c FLIP BUG: landing fails Brent, dropped");
                        continue;
                    }
                    pool.insert(key);
                    let seq = counts.entry(rk).or_insert(0);
                    *seq += 1;
                    let seq = *seq;
                    if rk < min_rank {
                        min_rank = rk;
                        println!(
                            "c [{el:7.0}s] new min rank {rk} (landing #{seq})"
                        );
                    }
                    on_new(rk, &bits, seq);
                }
                Err(mpsc::RecvTimeoutError::Timeout) => {}
                Err(mpsc::RecvTimeoutError::Disconnected) => break,
            }
            if last_report.elapsed().as_secs() >= 60 {
                last_report = Instant::now();
                let mut ranks: Vec<_> = counts.iter().collect();
                ranks.sort();
                println!(
                    "c [{:7.0}s] reductions {} | landings {} | distinct {:?} | trajectories {} | diffuse-flips {:.1}M",
                    t0.elapsed().as_secs_f64(),
                    stats.reductions.load(Ordering::Relaxed),
                    stats.landings.load(Ordering::Relaxed),
                    ranks,
                    stats.trajectories.load(Ordering::Relaxed),
                    stats.flips.load(Ordering::Relaxed) as f64 / 1e6,
                );
                let _ = std::io::stdout().flush();
            }
        }
        stop.store(true, Ordering::Relaxed);
        result = (counts, min_rank);
        result
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn trivial(n: usize) -> (Vec<Summand>, FlipCfg) {
        let cfg = FlipCfg {
            n1: n,
            n2: n,
            n3: n,
            save_at: 0,
            record: 0,
            minutes: 0.0,
            threads: 1,
            seek_attempts: 1000,
            stall_limit: 8,
            seed: 1,
        };
        let mut s = Vec::new();
        for i in 0..n {
            for k in 0..n {
                for j in 0..n {
                    s.push([
                        1u16 << (i * n + k),
                        1u16 << (k * n + j),
                        1u16 << (i * n + j),
                    ]);
                }
            }
        }
        (s, cfg)
    }

    #[test]
    fn moves_preserve_validity() {
        let (mut s, cfg) = trivial(3);
        let anf27 = brent(Dims { n1: 3, n2: 3, n3: 3, r: 27 });
        assert_eq!(verify(&anf27, &summands_to_bits(&s, &cfg)), 0);
        let mut rng = Rng::new(7);
        let mut anfs: HashMap<usize, Anf> = HashMap::new();
        for step in 0..20_000 {
            if s.len() < 30 && rng.f64() < 0.1 {
                split_toward(&mut s, &mut rng);
            } else {
                let az = rng.f64() < 0.2;
                random_flip(&mut s, &mut rng, az);
            }
            if step % 1000 == 0 {
                let rk = s.len();
                let anf = anfs.entry(rk).or_insert_with(|| {
                    brent(Dims { n1: 3, n2: 3, n3: 3, r: rk })
                });
                assert_eq!(
                    verify(anf, &summands_to_bits(&s, &cfg)),
                    0,
                    "invalid after {step} moves at rank {rk}"
                );
            }
        }
    }

    #[test]
    fn roundtrip_bits_summands() {
        let (s, cfg) = trivial(4);
        let bits = summands_to_bits(&s, &cfg);
        assert_eq!(bits_to_summands(&bits, &cfg), s);
        let anf = brent(Dims { n1: 4, n2: 4, n3: 4, r: 64 });
        assert_eq!(verify(&anf, &bits), 0);
    }
}
