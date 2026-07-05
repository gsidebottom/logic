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

pub type Summand = [u32; 3];

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
            s[0] |= (bits[m * sa + k] as u32) << k;
        }
        for k in 0..sb {
            s[1] |= (bits[na + m * sb + k] as u32) << k;
        }
        for k in 0..sg {
            s[2] |= (bits[na + nb + m * sg + k] as u32) << k;
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
    let x = (rng.next_u64() as u32) & ((1u32 << 25) - 1);
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

// ---------------- guided descent (wave 3) ----------------
//
// At the funnel bottom a reduction needs a MERGEABLE pair: two summands
// equal in two slots (a⊗b⊗c + a⊗b⊗c' -> a⊗b⊗(c+c')). Random flips
// essentially never produce one at rank 49 (measured: ~3e5 visits,
// zero). Guidance: score candidate flips by the agreement structure
// they create and take the best (Metropolis on ties/worse); merge
// deterministically the moment a mergeable pair exists.

/// number of slots in which summands i and j hold equal factors
#[inline]
fn agreements(s: &[Summand], i: usize, j: usize) -> u32 {
    (s[i][0] == s[j][0]) as u32
        + (s[i][1] == s[j][1]) as u32
        + (s[i][2] == s[j][2]) as u32
}

/// pair-structure score contribution of summand m against all others:
/// 1 per 1-agreement pair, heavy bonus per mergeable (>=2) pair.
fn row_score(s: &[Summand], m: usize) -> i64 {
    let mut sc = 0i64;
    for j in 0..s.len() {
        if j == m {
            continue;
        }
        match agreements(s, m, j) {
            0 => {}
            1 => sc += 1,
            _ => sc += 200,
        }
    }
    sc
}

/// merge one mergeable pair if present. Returns true if rank dropped.
pub fn merge_if_available(s: &mut Vec<Summand>) -> bool {
    let r = s.len();
    for i in 0..r {
        for j in i + 1..r {
            if agreements(s, i, j) >= 2 {
                // combine in the (a) disagreeing slot, or annihilate
                let o = (0..3).find(|&k| s[i][k] != s[j][k]);
                match o {
                    Some(k) => {
                        s[j][k] ^= s[i][k];
                        s.remove(i);
                        if s[j - 1].contains(&0) {
                            s.remove(j - 1);
                        }
                    }
                    None => {
                        // identical summands cancel entirely (mod 2)
                        s.remove(j);
                        s.remove(i);
                    }
                }
                return true;
            }
        }
    }
    false
}

/// one guided flip: sample K legal candidates, apply the one with the
/// best agreement-score delta (Metropolis acceptance for non-improving).
pub fn guided_flip(s: &mut Vec<Summand>, rng: &mut Rng, k: usize) -> bool {
    let r = s.len();
    let mut best: Option<(i64, usize, usize, usize, usize)> = None;
    for _ in 0..k * 8 {
        if best.as_ref().map_or(false, |_| false) {
            break;
        }
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
        if s[i][o1] == s[j][o1] || s[i][o2] == s[j][o2] {
            continue; // zero-producing: merges are handled explicitly
        }
        // trial apply, score, revert
        let before = row_score(s, i) + row_score(s, j);
        s[i][o1] ^= s[j][o1];
        s[j][o2] ^= s[i][o2];
        let after = row_score(s, i) + row_score(s, j);
        s[j][o2] ^= s[i][o2];
        s[i][o1] ^= s[j][o1];
        let d = after - before;
        if best.map_or(true, |(bd, ..)| d > bd) {
            best = Some((d, i, j, o1, o2));
        }
        if best.map_or(false, |(bd, ..)| bd > 0) && rng.f64() < 0.35 {
            break; // good enough, keep moving
        }
    }
    if let Some((d, i, j, o1, o2)) = best {
        // Metropolis: always take improvements; sometimes take flat/worse
        if d >= 0 || rng.f64() < (0.25f64).powi((-d).min(8) as i32) {
            s[i][o1] ^= s[j][o1];
            s[j][o2] ^= s[i][o2];
            return true;
        }
    }
    false
}

/// one payload flip: i[o] ^= k[o] via shared slot t (side effect:
/// k[third] ^= i[third]). Preconditions checked; drops zeroed summands.
/// Returns false (and changes nothing) if the flip is illegal now.
#[inline]
fn payload_flip(
    s: &mut Vec<Summand>,
    i: usize,
    k: usize,
    t: usize,
    o: usize,
) -> bool {
    if i == k || t == o || s[i][t] != s[k][t] || s[i][t] == 0 {
        return false;
    }
    let third = 3 - t - o;
    s[i][o] ^= s[k][o];
    s[k][third] ^= s[i][third];
    // payload never zeroes i[o] here by construction (target = j's
    // nonzero factor), but the side effect may zero k[third]:
    if s[k].contains(&0) {
        s.retain(|x| !x.contains(&0));
    }
    true
}

/// WAVE 4: certified pair equalization. For each 1-agreement pair
/// (i,j), disagreeing slot o with difference d: find a 1- or 2-flip
/// XOR chain from flip-adjacent summands whose payloads sum to d;
/// execute it and merge. Exact search, not sampling.
/// Returns true if the rank dropped.
pub fn try_equalize_merge(s: &mut Vec<Summand>, rng: &mut Rng) -> bool {
    if merge_if_available(s) {
        return true;
    }
    // transactional: any payload flips are rolled back unless the rank
    // actually drops, so a failed attempt never corrupts the scheme.
    let snapshot = s.clone();
    if try_equalize_inner(s, rng) {
        return true;
    }
    *s = snapshot;
    false
}

fn try_equalize_inner(s: &mut Vec<Summand>, rng: &mut Rng) -> bool {
    let r = s.len();
    let start = rng.below(r.max(1));
    for ii in 0..r {
        let i = (start + ii) % r;
        for j in 0..r {
            if j == i || agreements(s, i, j) != 1 {
                continue;
            }
            // the agreeing slot
            let sa = (0..3).find(|&k| s[i][k] == s[j][k]).unwrap();
            for o in 0..3 {
                if o == sa {
                    continue;
                }
                let d = s[i][o] ^ s[j][o];
                // adjacency: k reachable from i via shared slot t (t!=o)
                // collect (k, t, payload = s[k][o])
                let mut adj: Vec<(usize, usize, u32)> = Vec::new();
                for k in 0..s.len() {
                    if k == i || k == j {
                        continue;
                    }
                    for t in 0..3 {
                        if t != o && s[i][t] == s[k][t] && s[i][t] != 0 {
                            adj.push((k, t, s[k][o]));
                            break;
                        }
                    }
                }
                // 1-step
                if let Some(&(k, t, _)) =
                    adj.iter().find(|&&(_, _, p)| p == d)
                {
                    if payload_flip(s, i, k, t, o) {
                        if merge_if_available(s) || s.len() < r {
                            return true;
                        }
                    }
                }
                // 2-step: payloads p1 ^ p2 == d
                if adj.len() >= 2 {
                    let mut seen: HashMap<u32, (usize, usize)> =
                        HashMap::new();
                    for &(k, t, p) in &adj {
                        if let Some(&(k1, t1)) = seen.get(&(p ^ d)) {
                            // execute k1 then k (re-check legality —
                            // step 1's side effect may have moved things)
                            let before = s.len();
                            if payload_flip(s, i, k1, t1, o)
                                && s.len() == before
                                && payload_flip(s, i, k, t, o)
                            {
                                if merge_if_available(s) || s.len() < before
                                {
                                    return true;
                                }
                            } else if s.len() < before {
                                return true; // side-effect reduction
                            }
                        }
                        seen.insert(p, (k, t));
                    }
                }
            }
        }
    }
    false
}

/// guided burst: try to force a reduction within `steps` guided flips.
/// funnel-bottom reducer: the proven deep random seek is the workhorse
/// (`seek` attempts — keep this large, it is what punched 52->49 in the
/// scale waves), and certified equalization is layered on top as the new
/// lever, tried before an expensive steered burst.
pub fn guided_descend(
    s: &mut Vec<Summand>,
    rng: &mut Rng,
    seek: usize,
    k: usize,
) -> bool {
    // 1) deep random seek — the workhorse (do NOT shrink this budget).
    if seek_reduction(s, rng, seek) {
        return true;
    }
    // 2) certified equalization from the stuck state (transactional).
    if try_equalize_merge(s, rng) {
        return true;
    }
    // 3) a short steered burst that engineers mergeable structure, then
    //    one more certified pass — bounded so it never dominates time.
    for _ in 0..48 {
        guided_flip(s, rng, k);
        if merge_if_available(s) {
            return true;
        }
    }
    try_equalize_merge(s, rng)
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
        let result: (HashMap<usize, usize>, usize);
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
                    // rank-adaptive effort: guided descent at the funnel
                    // bottom, cheap random seeks up high
                    let rk = cur.len();
                    let reduced = if rk <= cfg.save_at + 3 {
                        // deep seek (wave-2's 25x) + certified equalization
                        guided_descend(
                            &mut cur,
                            &mut rng,
                            cfg.seek_attempts * 25,
                            12,
                        )
                    } else if rk <= cfg.save_at + 6 {
                        seek_reduction(&mut cur, &mut rng,
                                       cfg.seek_attempts * 4)
                    } else {
                        seek_reduction(&mut cur, &mut rng,
                                       cfg.seek_attempts)
                    };
                    if reduced {
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
                        1u32 << (i * n + k),
                        1u32 << (k * n + j),
                        1u32 << (i * n + j),
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
    fn merge_and_guided_preserve_validity() {
        let (mut s, cfg) = trivial(3);
        let mut rng = Rng::new(11);
        let mut anfs: HashMap<usize, Anf> = HashMap::new();
        // trivial has many mergeable pairs? (no two summands agree in 2
        // slots there) — create material via splits+flips then exercise
        // merge_if_available + guided_flip and re-verify throughout.
        for step in 0..8_000 {
            match step % 8 {
                0 if s.len() < 32 => split_toward(&mut s, &mut rng),
                1 | 2 => {
                    guided_flip(&mut s, &mut rng, 8);
                }
                3 => {
                    merge_if_available(&mut s);
                }
                4 => {
                    try_equalize_merge(&mut s, &mut rng);
                }
                _ => {
                    random_flip(&mut s, &mut rng, false);
                }
            }
            if step % 500 == 0 {
                let rk = s.len();
                let anf = anfs.entry(rk).or_insert_with(|| {
                    brent(Dims { n1: 3, n2: 3, n3: 3, r: rk })
                });
                assert_eq!(
                    verify(anf, &summands_to_bits(&s, &cfg)),
                    0,
                    "invalid after {step} steps at rank {rk}"
                );
            }
        }
    }

    #[test]
    fn descends_below_trivial_rank() {
        // guards against silent descent stalls (the wave-4 regression):
        // from the trivial 3x3 rank-27 scheme a single guided worker must
        // reach at least rank 24 within a bounded step budget, every
        // landing Brent-valid.
        let (seed, _cfg) = trivial(3);
        let mut rng = Rng::new(3);
        let mut cur = seed.clone();
        let mut min_rank = cur.len();
        let mut anfs: HashMap<usize, Anf> = HashMap::new();
        let mut stall = 0;
        for _ in 0..4000 {
            if guided_descend(&mut cur, &mut rng, 3000, 12) {
                let rk = cur.len();
                let anf = anfs.entry(rk).or_insert_with(|| {
                    brent(Dims { n1: 3, n2: 3, n3: 3, r: rk })
                });
                assert_eq!(verify(anf, &summands_to_bits(&cur, &_cfg)), 0);
                min_rank = min_rank.min(rk);
                stall = 0;
                if min_rank <= 23 {
                    break;
                }
            } else {
                for _ in 0..300 {
                    random_flip(&mut cur, &mut rng, false);
                }
                stall += 1;
                if stall > 20 {
                    cur = seed.clone();
                    stall = 0;
                }
            }
        }
        assert!(min_rank <= 24, "stalled at rank {min_rank} (>24)");
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
