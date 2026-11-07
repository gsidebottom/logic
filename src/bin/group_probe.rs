//! Direct test of the subspace re-decomposition moves at saved states.
//!
//! For every *.bits scheme in DIR (visited states of a descend campaign,
//! e.g. the rank-30 landings of a <3,3,4> run), ask with fresh copies:
//!
//!   base    does the baseline local reducer (guided_descend, no group
//!           moves, the engine's own seek budget) lower the rank in T
//!           tries?
//!   group   does group_reduce alone (G1 same-factor groups, G2 lines)
//!           lower it, with no flips at all?
//!   shuf    do N plateau shuffles (random line re-decompositions), each
//!           followed by group_reduce, lower it?
//!   both    does guided_descend WITH the G1/G2 moves lower it in T tries?
//!   plane   does the greedy plane reducer (G3, dimension 3) lower it?
//!   planesat for every plane group of 4..=8 terms whose profile bound
//!           allows fewer terms and whose greedy found none: a SAT call
//!           (CaDiCaL) decides exactly whether a shorter decomposition
//!           exists; a witness is verified against the tensor and the
//!           rewritten scheme against Brent before it counts.
//!
//! and cross-tabulate base against the group moves: a state the baseline
//! cannot lower but a group move can is what the moves are for; if that
//! cell is empty the moves only re-route reductions the baseline finds
//! anyway.
//!
//! ```text
//! usage: group_probe N1 N2 N3 DIR [--tries T=3] [--shuffles N=200]
//!                    [--seek A=100000] [--threads 12] [--seed 1] [--max N]
//!                    [--tmp DIR] [--sat-timeout S=10] [--sat-max N=24] [--no-sat]
//!
//! --max N takes a seeded random sample of N states; --sat-max caps the
//! SAT calls per state (the groups left after it are counted as skipped).
//! ```

use logic::anf::{brent, verify, Anf, Dims, Rng};
use logic::flip::*;
use logic::flip_group::*;
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

fn arg_val<T: std::str::FromStr>(args: &[String], key: &str) -> Option<T> {
    args.iter()
        .position(|a| a == key)
        .and_then(|i| args.get(i + 1))
        .and_then(|s| s.parse().ok())
}

/// CNF for "the 3 x du x dv tensor csl has a decomposition with rho
/// terms": variables x[t][j], u[t][a], v[t][b], Tseitin AND gates and
/// XOR chains per entry.  Returns (nvars, clauses, var index closure data).
fn plane_cnf(csl: &[Vec<u16>; 3], du: usize, dv: usize, rho: usize) -> (usize, Vec<Vec<i32>>) {
    let xv = |t: usize, j: usize| -> i32 { (1 + t * 3 + j) as i32 };
    let uv = |t: usize, a: usize| -> i32 { (1 + rho * 3 + t * du + a) as i32 };
    let vv = |t: usize, b: usize| -> i32 { (1 + rho * 3 + rho * du + t * dv + b) as i32 };
    let mut nv = rho * (3 + du + dv);
    let mut cl: Vec<Vec<i32>> = Vec::new();
    for t in 0..rho {
        cl.push((0..3).map(|j| xv(t, j)).collect());
        cl.push((0..du).map(|a| uv(t, a)).collect());
        cl.push((0..dv).map(|b| vv(t, b)).collect());
    }
    for j in 0..3 {
        for a in 0..du {
            for b in 0..dv {
                let target = (csl[j][a] >> b) & 1 == 1;
                let mut acc: Option<i32> = None;
                for t in 0..rho {
                    nv += 1;
                    let m = nv as i32;
                    let (x, u, v) = (xv(t, j), uv(t, a), vv(t, b));
                    cl.push(vec![-m, x]);
                    cl.push(vec![-m, u]);
                    cl.push(vec![-m, v]);
                    cl.push(vec![m, -x, -u, -v]);
                    acc = Some(match acc {
                        None => m,
                        Some(y) => {
                            nv += 1;
                            let z = nv as i32;
                            cl.push(vec![-z, y, m]);
                            cl.push(vec![-z, -y, -m]);
                            cl.push(vec![z, -y, m]);
                            cl.push(vec![z, y, -m]);
                            z
                        }
                    });
                }
                let y = acc.unwrap();
                cl.push(vec![if target { y } else { -y }]);
            }
        }
    }
    (nv, cl)
}

/// run CaDiCaL on the clauses: Some(Some(model)) SAT, Some(None) UNSAT,
/// None unknown (timeout or failure)
fn run_cadical(path: &str, nv: usize, cl: &[Vec<i32>], timeout_s: usize) -> Option<Option<Vec<bool>>> {
    let mut txt = format!("p cnf {} {}\n", nv, cl.len());
    for c in cl {
        for l in c {
            txt.push_str(&l.to_string());
            txt.push(' ');
        }
        txt.push_str("0\n");
    }
    std::fs::write(path, txt).ok()?;
    let out = std::process::Command::new("/opt/homebrew/bin/cadical")
        .args(["-q", "-t", &timeout_s.to_string(), path])
        .output()
        .ok()?;
    let s = String::from_utf8_lossy(&out.stdout);
    if s.contains("s UNSATISFIABLE") {
        return Some(None);
    }
    if !s.contains("s SATISFIABLE") {
        return None;
    }
    let mut model = vec![false; nv + 1];
    for line in s.lines() {
        if let Some(rest) = line.strip_prefix("v ") {
            for tok in rest.split_whitespace() {
                if let Ok(l) = tok.parse::<i64>() {
                    if l > 0 && (l as usize) <= nv {
                        model[l as usize] = true;
                    }
                }
            }
        }
    }
    Some(Some(model))
}

/// the decomposition read off a model: (code, u-coords, v-coords) per term
fn decode(model: &[bool], du: usize, dv: usize, rho: usize) -> Vec<(u32, u32, u32)> {
    let mut out = Vec::new();
    for t in 0..rho {
        let mut x = 0u32;
        for j in 0..3 {
            if model[1 + t * 3 + j] {
                x |= 1 << j;
            }
        }
        let mut u = 0u32;
        for a in 0..du {
            if model[1 + rho * 3 + t * du + a] {
                u |= 1 << a;
            }
        }
        let mut v = 0u32;
        for b in 0..dv {
            if model[1 + rho * 3 + rho * du + t * dv + b] {
                v |= 1 << b;
            }
        }
        out.push((x, u, v));
    }
    out
}

struct PlaneCounters {
    groups: AtomicUsize,
    by_k: Vec<AtomicUsize>,
    lb_closed: AtomicUsize,
    open: AtomicUsize,
    greedy_red: AtomicUsize,
    sat_calls: AtomicUsize,
    sat_skipped: AtomicUsize,
    sat_red: AtomicUsize,
    sat_unsat: AtomicUsize,
    sat_unknown: AtomicUsize,
    sat_us: AtomicUsize,
    big: AtomicUsize,
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() < 4 {
        eprintln!("usage: group_probe N1 N2 N3 DIR [--tries T] [--shuffles N] [--seek A] [--threads T] [--seed S] [--max N] [--tmp DIR] [--sat-timeout S] [--sat-max N] [--no-sat]");
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
    let tmp: String = arg_val(&args, "--tmp").unwrap_or_else(|| std::env::temp_dir().to_string_lossy().to_string());
    let sat_timeout: usize = arg_val(&args, "--sat-timeout").unwrap_or(10);
    let sat_max: usize = arg_val(&args, "--sat-max").unwrap_or(24);
    let use_sat = !args.iter().any(|a| a == "--no-sat");
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
        // a seeded random sample of the states
        let mut rng = Rng::new(cfg.seed ^ 0x5eed);
        for i in (1..names.len()).rev() {
            let j = rng.below(i + 1);
            names.swap(i, j);
        }
        names.truncate(mx);
        names.sort();
    }
    let mut schemes: Vec<Vec<Summand>> = Vec::new();
    let mut by_rank: BTreeMap<usize, usize> = Default::default();
    let mut anfs: BTreeMap<usize, Anf> = Default::default();
    for path in &names {
        let txt = std::fs::read_to_string(path).unwrap();
        let bits: Vec<u8> = txt.split_whitespace().last().unwrap().bytes().map(|b| b - b'0').collect();
        if bits.len() % width != 0 {
            eprintln!("skip {}: {} bits", path.display(), bits.len());
            continue;
        }
        let s = bits_to_summands(&bits, &cfg);
        let anf = anfs
            .entry(s.len())
            .or_insert_with(|| brent(Dims { n1: cfg.n1, n2: cfg.n2, n3: cfg.n3, r: s.len() }));
        assert_eq!(verify(anf, &bits), 0, "{} fails Brent", path.display());
        *by_rank.entry(s.len()).or_insert(0) += 1;
        schemes.push(s);
    }
    println!(
        "c group_probe <{},{},{}>: {} schemes from {} by rank {:?}; tries {} shuffles {} seek {} threads {} sat {}",
        cfg.n1, cfg.n2, cfg.n3, schemes.len(), dir, by_rank, tries, nshuf, seek, cfg.threads,
        if use_sat { format!("on (timeout {sat_timeout} s)") } else { "off".to_string() }
    );

    // census of the structures the moves act on
    {
        let mut same: BTreeMap<usize, usize> = Default::default();
        let mut lines: BTreeMap<usize, usize> = Default::default();
        let mut planes: BTreeMap<usize, usize> = Default::default();
        let mut with_line4 = 0usize;
        let mut with_plane4 = 0usize;
        for s in &schemes {
            let mut any4 = false;
            let mut anyp = false;
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
                for g in plane_groups(s, t, 4, usize::MAX) {
                    *planes.entry(g.members.len()).or_insert(0) += 1;
                    anyp = true;
                }
            }
            if any4 {
                with_line4 += 1;
            }
            if anyp {
                with_plane4 += 1;
            }
        }
        println!(
            "c census over {} schemes: same-factor groups by k {:?} | lines by k {:?} | schemes with a line of k >= 4: {}",
            schemes.len(), same, lines, with_line4
        );
        println!(
            "c plane groups (3 present factors spanning, >= 4 terms) by k {:?} | schemes with one: {}",
            planes, with_plane4
        );
    }

    // outcome bits per scheme: 1 base, 2 group, 4 shuf, 8 both, 16 plane greedy, 32 plane SAT
    let n = schemes.len();
    let outcomes: Vec<AtomicUsize> = (0..n).map(|_| AtomicUsize::new(0)).collect();
    let next = AtomicUsize::new(0);
    let t_base = AtomicUsize::new(0);
    let t_group = AtomicUsize::new(0);
    let t_shuf = AtomicUsize::new(0);
    let t_both = AtomicUsize::new(0);
    let t_plane = AtomicUsize::new(0);
    let pc = PlaneCounters {
        groups: AtomicUsize::new(0),
        by_k: (0..=PLANE_KMAX).map(|_| AtomicUsize::new(0)).collect(),
        lb_closed: AtomicUsize::new(0),
        open: AtomicUsize::new(0),
        greedy_red: AtomicUsize::new(0),
        sat_calls: AtomicUsize::new(0),
        sat_skipped: AtomicUsize::new(0),
        sat_red: AtomicUsize::new(0),
        sat_unsat: AtomicUsize::new(0),
        sat_unknown: AtomicUsize::new(0),
        sat_us: AtomicUsize::new(0),
        big: AtomicUsize::new(0),
    };
    let anfs = &anfs;
    let n_done = AtomicUsize::new(0);
    let t0 = Instant::now();
    std::thread::scope(|scope| {
        for w in 0..cfg.threads {
            let schemes = &schemes;
            let outcomes = &outcomes;
            let next = &next;
            let pc = &pc;
            let tmp = &tmp;
            let (t_base, t_group, t_shuf, t_both, t_plane) = (&t_base, &t_group, &t_shuf, &t_both, &t_plane);
            let n_done = &n_done;
            scope.spawn(move || {
                let mut rng = Rng::new(cfg.seed.wrapping_add(w as u64).wrapping_mul(0x9e3779b97f4a7c15));
                let gst = GroupStats::default();
                let mut ncnf = 0usize;
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
                    // guided descend with the G1/G2 moves
                    let t = Instant::now();
                    for _ in 0..tries {
                        let mut s = s0.clone();
                        if guided_descend(&mut s, &mut rng, seek, 12, 1, sizes, &gst) && s.len() < r {
                            o |= 8;
                            break;
                        }
                    }
                    t_both.fetch_add(t.elapsed().as_micros() as usize, Ordering::Relaxed);
                    // planes: one pass over the plane groups of 4..=PLANE_KMAX
                    // terms: staged profile bound, greedy, then (capped per
                    // state) the SAT decision; the first lowering of each kind
                    // is applied to a copy and checked against Brent
                    let t = Instant::now();
                    {
                        let mut greedy_hit = false;
                        let mut sat_hit = false;
                        let mut nsat = 0usize;
                        for t_slot in 0..3 {
                            let (o1, o2) = others(t_slot);
                            for g in plane_groups(s0, t_slot, 4, usize::MAX) {
                                let k = g.members.len();
                                if k > PLANE_KMAX {
                                    pc.big.fetch_add(1, Ordering::Relaxed);
                                    continue;
                                }
                                pc.groups.fetch_add(1, Ordering::Relaxed);
                                pc.by_k[k].fetch_add(1, Ordering::Relaxed);
                                let (su, sv) = group_spans(s0, &g);
                                let csl = coord_slices(s0, &g, &su, &sv);
                                if plane_lower_bound(&csl, su.dim(), sv.dim(), k) >= k {
                                    pc.lb_closed.fetch_add(1, Ordering::Relaxed);
                                    continue;
                                }
                                pc.open.fetch_add(1, Ordering::Relaxed);
                                let sl = plane_slices(s0, &g, sizes[o1]);
                                let (cost, parts) = plane_greedy(&sl, PLANE_CAP);
                                if cost < k {
                                    pc.greedy_red.fetch_add(1, Ordering::Relaxed);
                                    if !greedy_hit {
                                        let mut s2 = s0.clone();
                                        apply_plane(&mut s2, &g, &parts);
                                        assert_eq!(s2.len(), r - k + cost);
                                        let anf = brent(Dims { n1: cfg.n1, n2: cfg.n2, n3: cfg.n3, r: s2.len() });
                                        assert_eq!(
                                            verify(&anf, &summands_to_bits(&s2, &cfg)),
                                            0,
                                            "plane greedy rewrite fails Brent"
                                        );
                                        greedy_hit = true;
                                        o |= 16;
                                    }
                                    continue;
                                }
                                if !use_sat || sat_hit {
                                    continue;
                                }
                                if nsat >= sat_max {
                                    pc.sat_skipped.fetch_add(1, Ordering::Relaxed);
                                    continue;
                                }
                                nsat += 1;
                                // exact decision
                                let ts = Instant::now();
                                let (nv, cl) = plane_cnf(&csl, su.dim(), sv.dim(), k - 1);
                                ncnf += 1;
                                let path = format!("{tmp}/probe_w{w}_{ncnf}.cnf");
                                let res = run_cadical(&path, nv, &cl, sat_timeout);
                                let _ = std::fs::remove_file(&path);
                                pc.sat_calls.fetch_add(1, Ordering::Relaxed);
                                pc.sat_us.fetch_add(ts.elapsed().as_micros() as usize, Ordering::Relaxed);
                                match res {
                                    None => {
                                        pc.sat_unknown.fetch_add(1, Ordering::Relaxed);
                                    }
                                    Some(None) => {
                                        pc.sat_unsat.fetch_add(1, Ordering::Relaxed);
                                    }
                                    Some(Some(model)) => {
                                        let dec = decode(&model, su.dim(), sv.dim(), k - 1);
                                        // verify against the coordinate tensor
                                        let du = su.dim();
                                        let mut back = [vec![0u16; du], vec![0u16; du], vec![0u16; du]];
                                        for &(x, u, v) in &dec {
                                            for j in 0..3 {
                                                if x >> j & 1 == 1 {
                                                    for a in 0..du {
                                                        if u >> a & 1 == 1 {
                                                            back[j][a] ^= v as u16;
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                        assert_eq!(back, csl, "SAT witness does not reproduce the tensor");
                                        // rewrite a copy of the scheme and check Brent at the new rank
                                        let mut s2 = s0.clone();
                                        let mut idx: Vec<usize> = g.members.iter().map(|m| m.0).collect();
                                        idx.sort_unstable_by(|a, b| b.cmp(a));
                                        for i in idx {
                                            s2.swap_remove(i);
                                        }
                                        for &(x, u, v) in &dec {
                                            let mut term: Summand = [0; 3];
                                            term[t_slot] = plane_elem(&g.basis, x);
                                            term[o1] = su.vector(u);
                                            term[o2] = sv.vector(v);
                                            if term.contains(&0) {
                                                continue;
                                            }
                                            s2.push(term);
                                        }
                                        assert!(s2.len() < r);
                                        let anf = brent(Dims { n1: cfg.n1, n2: cfg.n2, n3: cfg.n3, r: s2.len() });
                                        assert_eq!(
                                            verify(&anf, &summands_to_bits(&s2, &cfg)),
                                            0,
                                            "plane SAT rewrite fails Brent"
                                        );
                                        pc.sat_red.fetch_add(1, Ordering::Relaxed);
                                        sat_hit = true;
                                        o |= 32;
                                    }
                                }
                            }
                        }
                    }
                    t_plane.fetch_add(t.elapsed().as_micros() as usize, Ordering::Relaxed);
                    outcomes[i].store(o, Ordering::Relaxed);
                    let done = n_done.fetch_add(1, Ordering::Relaxed) + 1;
                    if done % 200 == 0 || done == schemes.len() {
                        let ld = |a: &AtomicUsize| a.load(Ordering::Relaxed);
                        println!(
                            "c [{:.0}s] {} states | plane groups {} open {} greedy-reduced {} | SAT calls {} reduced {} unsat {} unknown {} skipped {}",
                            t0.elapsed().as_secs_f64(), done, ld(&pc.groups), ld(&pc.open), ld(&pc.greedy_red),
                            ld(&pc.sat_calls), ld(&pc.sat_red), ld(&pc.sat_unsat), ld(&pc.sat_unknown), ld(&pc.sat_skipped)
                        );
                    }
                }
            });
        }
    });
    let _ = anfs;
    let el = t0.elapsed().as_secs_f64();
    let o: Vec<usize> = outcomes.iter().map(|a| a.load(Ordering::Relaxed)).collect();
    let cnt = |mask: usize| o.iter().filter(|&&x| x & mask != 0).count();
    let gm = 2 | 4 | 16 | 32;
    println!("c {} schemes in {:.1}s", n, el);
    println!(
        "c lowered by: base {} ({} tries x seek {}) | group alone {} | {} shuffles+group {} | guided+moves {} | plane greedy {} | plane SAT {}",
        cnt(1), tries, seek, cnt(2), nshuf, cnt(4), cnt(8), cnt(16), cnt(32)
    );
    let both = o.iter().filter(|&&x| x & 1 != 0 && x & gm != 0).count();
    let base_only = o.iter().filter(|&&x| x & 1 != 0 && x & gm == 0).count();
    let g_only = o.iter().filter(|&&x| x & 1 == 0 && x & gm != 0).count();
    let neither = o.iter().filter(|&&x| x & (1 | gm) == 0).count();
    println!(
        "c cross-tab base vs any group move (G1/G2, shuffles, planes): both {} | base only {} | GROUP ONLY {} | neither {}",
        both, base_only, g_only, neither
    );
    let p_only_g = o.iter().filter(|&&x| x & 16 != 0 && x & (1 | 2 | 4) == 0).count();
    let p_only_s = o.iter().filter(|&&x| x & 32 != 0 && x & (1 | 2 | 4 | 16) == 0).count();
    println!(
        "c planes beyond the rest: lowered by the plane greedy but by neither base nor G1/G2 {} | by plane SAT only {}",
        p_only_g, p_only_s
    );
    println!(
        "c guided+moves vs base: lowered by guided+moves but not base {} | by base but not guided+moves {}",
        o.iter().filter(|&&x| x & 8 != 0 && x & 1 == 0).count(),
        o.iter().filter(|&&x| x & 1 != 0 && x & 8 == 0).count()
    );
    let byk: Vec<String> = (4..=PLANE_KMAX).map(|k| format!("{k}: {}", pc.by_k[k].load(Ordering::Relaxed))).collect();
    println!(
        "c plane groups examined {} (by k {}; above k = {}: {}) | closed by the profile bound {} | left open {} | reduced by the greedy {} | SAT calls {} (reduced {}, unsat {}, unknown {}; skipped by the per-state cap {}; mean {:.1} ms)",
        pc.groups.load(Ordering::Relaxed),
        byk.join(", "),
        PLANE_KMAX,
        pc.big.load(Ordering::Relaxed),
        pc.lb_closed.load(Ordering::Relaxed),
        pc.open.load(Ordering::Relaxed),
        pc.greedy_red.load(Ordering::Relaxed),
        pc.sat_calls.load(Ordering::Relaxed),
        pc.sat_red.load(Ordering::Relaxed),
        pc.sat_unsat.load(Ordering::Relaxed),
        pc.sat_unknown.load(Ordering::Relaxed),
        pc.sat_skipped.load(Ordering::Relaxed),
        pc.sat_us.load(Ordering::Relaxed) as f64 / 1e3 / pc.sat_calls.load(Ordering::Relaxed).max(1) as f64
    );
    let us = |a: &AtomicUsize| a.load(Ordering::Relaxed) as f64 / n.max(1) as f64 / 1e3;
    println!(
        "c mean ms per scheme: base {:.2} | group {:.3} | shuffles+group {:.2} | guided+moves {:.2} | planes (greedy + SAT) {:.2}",
        us(&t_base), us(&t_group), us(&t_shuf), us(&t_both), us(&t_plane)
    );
}
