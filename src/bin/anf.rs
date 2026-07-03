//! Native-ANF stochastic local search for fast matrix multiplication
//! (Brent equations mod 2) — the matmul track's R1 engine.
//!
//! ```text
//! usage: anf N1 N2 N3 R [options]
//!   --seconds S          wall budget (default 10)
//!   --seed S             base RNG seed (default 1)
//!   --threads T          parallel independent chains (default 1)
//!   --noise P            WalkSAT noise (default 0.2)
//!   --probsat            probSAT candidate sampling (default WalkSAT/SKC)
//!   --cb C               probSAT base (default 2.5)
//!   --density D          random-init one-density (default 0.25)
//!   --luby-unit F        flips per Luby unit, 0 = no restarts (default 2^20)
//!   --pert P             restart-from-best perturbation prob (default 0.06)
//!   --closure-every N    exact GF(2) tensor closure every N flips (0=off);
//!                        cycles gamma/alpha/beta; a consistent closure
//!                        solves the instance outright
//!   --fix-scheme NAME    seed mode: laderman | strassen
//!   --nfix K             #base vars frozen at the scheme's values
//!   --pair               freeze a random type-3 pairing (method 1)
//!   --bench S            flip-rate microbenchmark for S seconds, then exit
//!   --quiet              suppress the scheme printout
//! examples:
//!   anf 2 2 2 7 --seconds 5
//!   anf 3 3 3 23 --fix-scheme laderman --nfix 414
//!   anf 3 3 3 23 --pair --seconds 300 --threads 10
//! ```

use logic::anf::*;
use std::sync::atomic::AtomicBool;
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
        eprintln!("usage: anf N1 N2 N3 R [--seconds S] [--fix-scheme NAME --nfix K] [--pair] ... (see src/bin/anf.rs)");
        std::process::exit(2);
    }
    let d = Dims {
        n1: args[0].parse().unwrap(),
        n2: args[1].parse().unwrap(),
        n3: args[2].parse().unwrap(),
        r: args[3].parse().unwrap(),
    };
    let mut cfg = SlsCfg::default();
    cfg.max_secs = arg_val(&args, "--seconds").unwrap_or(10.0);
    cfg.seed = arg_val(&args, "--seed").unwrap_or(1);
    cfg.noise = arg_val(&args, "--noise").unwrap_or(0.2);
    cfg.cb = arg_val(&args, "--cb").unwrap_or(2.5);
    cfg.density = arg_val(&args, "--density").unwrap_or(0.25);
    cfg.luby_unit = arg_val(&args, "--luby-unit").unwrap_or(1 << 20);
    cfg.pert = arg_val(&args, "--pert").unwrap_or(0.06);
    cfg.closure_every = arg_val(&args, "--closure-every").unwrap_or(0);
    cfg.probsat = args.iter().any(|a| a == "--probsat");
    let threads: usize = arg_val(&args, "--threads").unwrap_or(1);
    let quiet = args.iter().any(|a| a == "--quiet");

    let anf = brent(d);
    eprintln!(
        "c brent <{},{},{}> r={}: {} vars, {} eqs ({} odd)",
        d.n1,
        d.n2,
        d.n3,
        d.r,
        anf.nvars,
        anf.neqs(),
        anf.rhs.iter().map(|&x| x as usize).sum::<usize>()
    );

    // --bench: raw flip-rate, no restarts, single chain
    if let Some(secs) = arg_val::<f64>(&args, "--bench") {
        let mut c = cfg;
        c.luby_unit = 0;
        c.max_secs = secs;
        let mut sls = Sls::new(&anf, &[], &c);
        let t0 = Instant::now();
        let stop = AtomicBool::new(false);
        let mut best = usize::MAX;
        let solved = sls.run(&c, t0, &stop, &mut best, None);
        let dt = t0.elapsed().as_secs_f64();
        println!(
            "c bench: {} flips in {:.2}s = {:.2}M flips/s (best {} unsat{})",
            sls.flips,
            dt,
            sls.flips as f64 / dt / 1e6,
            best,
            if solved { ", SOLVED" } else { "" }
        );
        return;
    }

    // frozen units: seeded scheme and/or pairing
    let mut frozen: Vec<(u32, u8)> = Vec::new();
    let mut seed_bits: Option<Vec<u8>> = None;
    if let Some(name) = args
        .iter()
        .position(|a| a == "--fix-scheme")
        .and_then(|i| args.get(i + 1))
    {
        let bits = match name.as_str() {
            "laderman" => bits_of(LADERMAN_BITS),
            "strassen" => bits_of(STRASSEN_BITS),
            _ => panic!("unknown scheme {name}"),
        };
        eprintln!("c seed scheme: {name}");
        seed_bits = Some(bits);
    }
    if let Some(path) = args
        .iter()
        .position(|a| a == "--fix-file")
        .and_then(|i| args.get(i + 1))
    {
        let txt = std::fs::read_to_string(path).expect("fix file");
        let s = txt.split_whitespace().last().expect("bits in fix file");
        eprintln!("c seed scheme from {path}");
        seed_bits = Some(bits_of(s));
    }
    if let Some(bits) = &seed_bits {
        assert_eq!(bits.len(), anf.nvars, "scheme dims mismatch");
        let nfix: usize = arg_val(&args, "--nfix").unwrap_or(bits.len() * 2 / 3);
        let mut rng = Rng::new(cfg.seed ^ 0xfeed);
        let mut idx: Vec<u32> = (0..anf.nvars as u32).collect();
        for i in (1..idx.len()).rev() {
            idx.swap(i, rng.below(i + 1));
        }
        frozen.extend(idx[..nfix].iter().map(|&v| (v, bits[v as usize])));
        eprintln!("c seeded: froze {nfix} vars at the seed scheme's values");
    }
    if args.iter().any(|a| a == "--pair") {
        let mut rng = Rng::new(cfg.seed ^ 0xbeef);
        let fr = loop {
            if let Some(fr) = random_pairing(d, &mut rng) {
                break fr;
            }
        };
        eprintln!("c pairing: froze {} type-3 unit bits", fr.len());
        frozen.extend(fr);
    }
    if let Some(path) = args
        .iter()
        .position(|a| a == "--freeze-file")
        .and_then(|i| args.get(i + 1))
    {
        let txt = std::fs::read_to_string(path).expect("freeze file");
        let mut n = 0;
        for line in txt.lines() {
            let mut it = line.split_whitespace();
            if let (Some(v), Some(b)) = (it.next(), it.next()) {
                frozen.push((v.parse().unwrap(), b.parse().unwrap()));
                n += 1;
            }
        }
        eprintln!("c freeze-file: froze {n} bits from {path}");
    }

    let closure_hook = move |bits: &mut [u8], frz: &[u8], k: u64| {
        let block =
            [Block::Gamma, Block::Alpha, Block::Beta][(k % 3) as usize];
        let _ = closure_tensor(d, bits, frz, block);
    };
    let hook: Option<Hook> = if cfg.closure_every > 0 {
        eprintln!("c closure hook: every {} flips (G/A/B cycle)",
            cfg.closure_every);
        Some(&closure_hook)
    } else {
        None
    };
    let t0 = Instant::now();
    let (sol, flips, best, best_bits) =
        solve_portfolio(&anf, &frozen, &cfg, threads, hook);
    let dt = t0.elapsed().as_secs_f64();
    let emit_best = args.iter().any(|a| a == "--emit-best");
    let rate = flips as f64 / dt / 1e6;
    match sol {
        Some(bits) => {
            let bad = verify(&anf, &bits);
            assert_eq!(bad, 0, "SOLVER BUG: claimed solution fails verify");
            println!(
                "s SATISFIABLE  ({dt:.3}s, {flips} flips over {threads} thread(s), {rate:.2}M flips/s, VERIFIED 0/{} violated)",
                anf.neqs()
            );
            let support: usize = bits.iter().map(|&b| b as usize).sum();
            println!("c support {} / {}", support, anf.nvars);
            let refb = seed_bits
                .clone()
                .or_else(|| (bits.len() == 621).then(|| bits_of(LADERMAN_BITS)));
            if let Some(rb) = refb {
                let dh: usize =
                    bits.iter().zip(&rb).filter(|(a, b)| a != b).count();
                println!("c hamming-to-seed {dh}");
            }
            println!(
                "b {}",
                bits.iter().map(|b| (b + b'0') as char).collect::<String>()
            );
            if !quiet {
                print_scheme(&d, &bits);
            }
        }
        None => {
            println!(
                "s UNKNOWN  ({dt:.3}s, {flips} flips, {rate:.2}M flips/s, best {best} unsat of {})",
                anf.neqs()
            );
            if emit_best && !best_bits.is_empty() {
                println!(
                    "B {}",
                    best_bits
                        .iter()
                        .map(|b| (b + b'0') as char)
                        .collect::<String>()
                );
            }
        }
    }
}

fn print_scheme(d: &Dims, bits: &[u8]) {
    for m in 0..d.r {
        let al: Vec<String> = (0..d.n1)
            .flat_map(|a| (0..d.n2).map(move |b| (a, b)))
            .filter(|&(a, b)| bits[d.a_idx(m, a, b) as usize] == 1)
            .map(|(a, b)| format!("A{}{}", a + 1, b + 1))
            .collect();
        let be: Vec<String> = (0..d.n2)
            .flat_map(|c| (0..d.n3).map(move |dd| (c, dd)))
            .filter(|&(c, dd)| bits[d.b_idx(m, c, dd) as usize] == 1)
            .map(|(c, dd)| format!("B{}{}", c + 1, dd + 1))
            .collect();
        println!("c M{:<2} = ({})*({})", m + 1, al.join("+"), be.join("+"));
    }
    for p in 0..d.n1 {
        for q in 0..d.n3 {
            let ms: Vec<String> = (0..d.r)
                .filter(|&m| bits[d.g_idx(m, p, q) as usize] == 1)
                .map(|m| format!("M{}", m + 1))
                .collect();
            println!("c C{}{} = {}", p + 1, q + 1, ms.join("+"));
        }
    }
}
