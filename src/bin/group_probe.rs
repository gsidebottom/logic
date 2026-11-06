//! Direct test of the subspace re-decomposition moves at saved states.
//!
//! For every *.bits scheme in DIR (visited states of a descend campaign,
//! e.g. the rank-30 landings of a <3,3,4> run), ask three questions
//! with fresh copies each time:
//!
//!   base   does the baseline local reducer (guided_descend, no group
//!          moves, the engine's own seek budget) lower the rank in
//!          T tries?
//!   group  does group_reduce alone (G1 same-factor groups, G2 lines)
//!          lower it, with no flips at all?
//!   shuf   do N plateau shuffles (random line re-decompositions),
//!          each followed by group_reduce, lower it?
//!   both   does guided_descend WITH the group moves lower it in T tries?
//!
//! and cross-tabulate base against (group or shuf): a state the baseline
//! cannot lower but a group move can is what the moves are for; if that
//! cell is empty the moves only re-route reductions the baseline finds
//! anyway.
//!
//! ```text
//! usage: group_probe N1 N2 N3 DIR [--tries T=3] [--shuffles N=200]
//!                    [--seek A=100000] [--threads 12] [--seed 1] [--max N]
//! ```

use logic::anf::{brent, verify, Dims, Rng};
use logic::flip::*;
use logic::flip_group::{group_reduce, group_shuffle, GroupStats};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

fn arg_val<T: std::str::FromStr>(args: &[String], key: &str) -> Option<T> {
    args.iter()
        .position(|a| a == key)
        .and_then(|i| args.get(i + 1))
        .and_then(|s| s.parse().ok())
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() < 4 {
        eprintln!("usage: group_probe N1 N2 N3 DIR [--tries T] [--shuffles N] [--seek A] [--threads T] [--seed S]");
        std::process::exit(2);
    }
    let cfg = FlipCfg {
        n1: args[0].parse().unwrap(),
        n2: args[1].parse().unwrap(),
        n3: args[2].parse().unwrap(),
        save_at: 0,
        record: 0,
        minutes: 0.0,
        threads: arg_val(&args, "--threads").unwrap_or(12),
        seek_attempts: 4000,
        stall_limit: 16,
        seed: arg_val(&args, "--seed").unwrap_or(1),
        group_moves: 0,
        shuffles: 0,
    };
    let dir = &args[3];
    let tries: usize = arg_val(&args, "--tries").unwrap_or(3);
    let nshuf: usize = arg_val(&args, "--shuffles").unwrap_or(200);
    let seek: usize = arg_val(&args, "--seek").unwrap_or(100_000);
    let sizes = slot_sizes(&cfg);
    let width = cfg.n1 * cfg.n2 + cfg.n2 * cfg.n3 + cfg.n1 * cfg.n3;

    // load
    let mut names: Vec<_> = std::fs::read_dir(dir)
        .expect("dir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().map(|x| x == "bits").unwrap_or(false))
        .collect();
    names.sort();
    if let Some(mx) = arg_val::<usize>(&args, "--max") {
        names.truncate(mx);
    }
    let mut schemes: Vec<Vec<Summand>> = Vec::new();
    let mut by_rank: std::collections::BTreeMap<usize, usize> = Default::default();
    for path in &names {
        let txt = std::fs::read_to_string(path).unwrap();
        let bits: Vec<u8> = txt
            .split_whitespace()
            .last()
            .unwrap()
            .bytes()
            .map(|b| b - b'0')
            .collect();
        if bits.len() % width != 0 {
            eprintln!("skip {}: {} bits", path.display(), bits.len());
            continue;
        }
        let s = bits_to_summands(&bits, &cfg);
        let anf = brent(Dims { n1: cfg.n1, n2: cfg.n2, n3: cfg.n3, r: s.len() });
        assert_eq!(verify(&anf, &bits), 0, "{} fails Brent", path.display());
        *by_rank.entry(s.len()).or_insert(0) += 1;
        schemes.push(s);
    }
    println!(
        "c group_probe <{},{},{}>: {} schemes from {} by rank {:?}; tries {} shuffles {} seek {} threads {}",
        cfg.n1, cfg.n2, cfg.n3, schemes.len(), dir, by_rank, tries, nshuf, seek, cfg.threads
    );

    // census of the structures the moves act on, at these states: same-
    // factor groups of k >= 3 terms and lines {u, v, u+v} with k >= 3
    // terms, by k (a line with k = 3 is a flip + merge in disguise; k >= 4
    // is where the move goes beyond the flip graph)
    {
        let mut same: std::collections::BTreeMap<usize, usize> = Default::default();
        let mut lines: std::collections::BTreeMap<usize, usize> = Default::default();
        let mut with_line4 = 0usize;
        for s in &schemes {
            let mut any4 = false;
            for t in 0..3 {
                let mut cnt: std::collections::HashMap<u32, usize> = Default::default();
                for m in s {
                    *cnt.entry(m[t]).or_insert(0) += 1;
                }
                for (_, &k) in &cnt {
                    if k >= 3 {
                        *same.entry(k).or_insert(0) += 1;
                    }
                }
                let mut vals: Vec<u32> = cnt.keys().copied().collect();
                vals.sort_unstable();
                for (i, &u) in vals.iter().enumerate() {
                    for &v in &vals[i + 1..] {
                        let w = u ^ v;
                        if w <= v {
                            continue;
                        }
                        if let Some(&kw) = cnt.get(&w) {
                            let k = cnt[&u] + cnt[&v] + kw;
                            *lines.entry(k).or_insert(0) += 1;
                            if k >= 4 {
                                any4 = true;
                            }
                        }
                    }
                }
            }
            if any4 {
                with_line4 += 1;
            }
        }
        println!(
            "c census over {} schemes: same-factor groups by k {:?} | lines by k {:?} | schemes with a line of k >= 4: {}",
            schemes.len(), same, lines, with_line4
        );
    }

    // outcome bits per scheme: 1 base, 2 group, 4 shuf, 8 both
    let n = schemes.len();
    let outcomes: Vec<AtomicUsize> = (0..n).map(|_| AtomicUsize::new(0)).collect();
    let next = AtomicUsize::new(0);
    let t_base = AtomicUsize::new(0);
    let t_group = AtomicUsize::new(0);
    let t_shuf = AtomicUsize::new(0);
    let t_both = AtomicUsize::new(0);
    let t0 = Instant::now();
    std::thread::scope(|scope| {
        for w in 0..cfg.threads {
            let schemes = &schemes;
            let outcomes = &outcomes;
            let next = &next;
            let (t_base, t_group, t_shuf, t_both) = (&t_base, &t_group, &t_shuf, &t_both);
            scope.spawn(move || {
                let mut rng = Rng::new(
                    cfg.seed.wrapping_add(w as u64).wrapping_mul(0x9e3779b97f4a7c15),
                );
                let gst = GroupStats::default();
                loop {
                    let i = next.fetch_add(1, Ordering::Relaxed);
                    if i >= schemes.len() {
                        break;
                    }
                    let s0 = &schemes[i];
                    let r = s0.len();
                    let mut o = 0usize;
                    // base
                    let t = Instant::now();
                    for _ in 0..tries {
                        let mut s = s0.clone();
                        if guided_descend(&mut s, &mut rng, seek, 12, 0, sizes, &gst) && s.len() < r {
                            o |= 1;
                            break;
                        }
                    }
                    t_base.fetch_add(t.elapsed().as_micros() as usize, Ordering::Relaxed);
                    // group alone
                    let t = Instant::now();
                    {
                        let mut s = s0.clone();
                        if group_reduce(&mut s, sizes, &gst) && s.len() < r {
                            o |= 2;
                        }
                    }
                    t_group.fetch_add(t.elapsed().as_micros() as usize, Ordering::Relaxed);
                    // shuffles + group
                    let t = Instant::now();
                    {
                        let mut s = s0.clone();
                        for _ in 0..nshuf {
                            group_shuffle(&mut s, sizes, &mut rng, &gst);
                            if s.len() < r || group_reduce(&mut s, sizes, &gst) {
                                o |= 4;
                                break;
                            }
                        }
                    }
                    t_shuf.fetch_add(t.elapsed().as_micros() as usize, Ordering::Relaxed);
                    // guided descend with the moves
                    let t = Instant::now();
                    for _ in 0..tries {
                        let mut s = s0.clone();
                        if guided_descend(&mut s, &mut rng, seek, 12, 1, sizes, &gst) && s.len() < r {
                            o |= 8;
                            break;
                        }
                    }
                    t_both.fetch_add(t.elapsed().as_micros() as usize, Ordering::Relaxed);
                    outcomes[i].store(o, Ordering::Relaxed);
                }
            });
        }
    });
    let el = t0.elapsed().as_secs_f64();
    let o: Vec<usize> = outcomes.iter().map(|a| a.load(Ordering::Relaxed)).collect();
    let cnt = |mask: usize| o.iter().filter(|&&x| x & mask != 0).count();
    let base = cnt(1);
    let group = cnt(2);
    let shuf = cnt(4);
    let both = cnt(8);
    let g_any = o.iter().filter(|&&x| x & 6 != 0).count();
    let base_and_g = o.iter().filter(|&&x| x & 1 != 0 && x & 6 != 0).count();
    let base_only = o.iter().filter(|&&x| x & 1 != 0 && x & 6 == 0).count();
    let g_only = o.iter().filter(|&&x| x & 1 == 0 && x & 6 != 0).count();
    let neither = o.iter().filter(|&&x| x & 7 == 0).count();
    let both_not_base = o.iter().filter(|&&x| x & 8 != 0 && x & 1 == 0).count();
    let base_not_both = o.iter().filter(|&&x| x & 1 != 0 && x & 8 == 0).count();
    println!("c {} schemes in {:.1}s", n, el);
    println!(
        "c lowered by: base {} ({} tries x seek {}) | group alone {} | {} shuffles+group {} | guided+moves {}",
        base, tries, seek, group, nshuf, shuf, both
    );
    println!(
        "c cross-tab base vs any group move: both {} | base only {} | GROUP ONLY {} | neither {} (group any {})",
        base_and_g, base_only, g_only, neither, g_any
    );
    println!(
        "c guided+moves vs base: lowered by guided+moves but not base {} | by base but not guided+moves {}",
        both_not_base, base_not_both
    );
    let us = |a: &AtomicUsize| a.load(Ordering::Relaxed) as f64 / n.max(1) as f64 / 1e3;
    println!(
        "c mean ms per scheme: base {:.2} | group {:.3} | shuffles+group {:.2} | guided+moves {:.2}",
        us(&t_base), us(&t_group), us(&t_shuf), us(&t_both)
    );
}
