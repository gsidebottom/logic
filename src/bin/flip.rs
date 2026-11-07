//! Parallel flip-graph descend campaign (Kauers–Moosbauer discovery
//! pipeline) with the sign-SAT liftability lottery.
//!
//! ```text
//! usage: flip N1 N2 N3 --seed-file F [options]
//!   --seed-file F     bits file of the starting scheme (rank inferred)
//!   --out DIR         archive dir for landings (default matmul/found4r)
//!   --save-at R       save landings at rank <= R (default 49)
//!   --record R        rank < R prints the jackpot banner (default 47)
//!   --lift-below R    shell matmul/lift.py for landings <= R (default 48)
//!   --matmul-dir D    where lift.py lives (default matmul)
//!   --minutes M       wall budget (default 60)
//!   --threads T       worker trajectories (default 10)
//!   --seek N          reduction-seek attempts per round (default 4000)
//!   --stall N         stalls before trajectory restart (default 16)
//!   --seed S          RNG seed (default 1)
//!   --trivial         start from the trivial n1*n2*n3-product scheme
//!                     (no --seed-file needed)
//!   --seeds-dir D     (descend mode) start every trajectory from a random
//!                     *.bits scheme of D, any ranks (projected seeds)
//!   --write-at R      write landing files only at rank <= R (default:
//!                     --save-at; reporting still covers every rank <= save-at)
//!   --group-moves M   subspace re-decomposition moves (src/flip_group.rs):
//!                     bit 0 group reductions (same factor, lines), bit 1
//!                     plateau shuffles, bit 2 plane reductions (dim 3)
//!                     (default 0 = the engine before 2026-11-06)
//!   --shuffles N      plateau line shuffles per stalled round (default 2)
//! example:
//!   flip 4 4 4 --seed-file matmul/seeds4triv/trivial64.bits \
//!        --minutes 90 --threads 10
//!
//! WALK mode (fixed-rank wander, the 3x3 50-hunt generator):
//!   flip 3 3 3 --walk --seeds-dir D --out ARCH [--minutes M]
//!        [--threads T] [--max-excess 8] [--hard-excess 14] [--kick 20]
//!        [--rank 23]
//!   loads every *.bits in D of the given rank as seeds, pre-seeds dedup from
//!   ARCH, writes new distinct landings as ARCH/flip-NNNNN.bits.
//! ```

use logic::flip::*;

fn arg_val<T: std::str::FromStr>(args: &[String], key: &str) -> Option<T> {
    args.iter()
        .position(|a| a == key)
        .and_then(|i| args.get(i + 1))
        .and_then(|s| s.parse().ok())
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() < 3 {
        eprintln!("usage: flip N1 N2 N3 --seed-file F [--minutes M] [--threads T] ... (see src/bin/flip.rs)");
        std::process::exit(2);
    }
    let cfg = FlipCfg {
        n1: args[0].parse().unwrap(),
        n2: args[1].parse().unwrap(),
        n3: args[2].parse().unwrap(),
        save_at: arg_val(&args, "--save-at").unwrap_or(49),
        record: arg_val(&args, "--record").unwrap_or(47),
        minutes: arg_val(&args, "--minutes").unwrap_or(60.0),
        threads: arg_val(&args, "--threads").unwrap_or(10),
        seek_attempts: arg_val(&args, "--seek").unwrap_or(4000),
        stall_limit: arg_val(&args, "--stall").unwrap_or(16),
        seed: arg_val(&args, "--seed").unwrap_or(1),
        group_moves: arg_val(&args, "--group-moves").unwrap_or(0),
        shuffles: arg_val(&args, "--shuffles").unwrap_or(2),
    };
    if args.iter().any(|a| a == "--walk") {
        let seeds_dir: String =
            arg_val(&args, "--seeds-dir").expect("--seeds-dir required");
        let out: String = arg_val(&args, "--out").expect("--out required");
        let max_excess: usize = arg_val(&args, "--max-excess").unwrap_or(8);
        let hard_excess: usize =
            arg_val(&args, "--hard-excess").unwrap_or(14);
        let kick: usize = arg_val(&args, "--kick").unwrap_or(20);
        let rank: usize = arg_val(&args, "--rank").unwrap_or(23);
        std::fs::create_dir_all(&out).unwrap();
        let load_dir = |dir: &str| -> Vec<Vec<Summand>> {
            let mut v = Vec::new();
            let mut names: Vec<_> = std::fs::read_dir(dir)
                .unwrap()
                .filter_map(|e| e.ok().map(|e| e.path()))
                .filter(|p| {
                    p.extension().map(|x| x == "bits").unwrap_or(false)
                })
                .collect();
            names.sort();
            for path in names {
                let txt = std::fs::read_to_string(&path).unwrap();
                let bits: Vec<u8> = txt
                    .split_whitespace()
                    .last()
                    .unwrap()
                    .bytes()
                    .map(|b| b - b'0')
                    .collect();
                if bits.len()
                    == (cfg.n1 * cfg.n2 + cfg.n2 * cfg.n3 + cfg.n1 * cfg.n3)
                        * rank
                {
                    v.push(bits_to_summands(&bits, &cfg));
                }
            }
            v
        };
        let seeds = load_dir(&seeds_dir);
        let pool_init = load_dir(&out);
        let nseq0 = std::fs::read_dir(&out)
            .unwrap()
            .filter_map(|e| e.ok())
            .filter(|e| {
                e.file_name().to_string_lossy().starts_with("flip-")
            })
            .count();
        println!(
            "c flip WALK: <{},{},{}> rank {rank}, {} seeds, {} archived, {} threads, {} min",
            cfg.n1, cfg.n2, cfg.n3, seeds.len(), pool_init.len(),
            cfg.threads, cfg.minutes
        );
        let outdir = out.clone();
        let n = walk_campaign(
            seeds, pool_init, cfg, max_excess, hard_excess, kick,
            |bits, seq| {
                let s: String =
                    bits.iter().map(|b| (b + b'0') as char).collect();
                let path =
                    format!("{outdir}/flip-{:05}.bits", nseq0 + seq - 1);
                std::fs::write(&path, format!("{s}\n")).unwrap();
            },
        );
        println!("c walk done: {n} new distinct schemes");
        return;
    }
    let trivial = args.iter().any(|a| a == "--trivial");
    let seeds_dir: Option<String> = arg_val(&args, "--seeds-dir");
    let seed_file: String = if trivial {
        "trivial".to_string()
    } else if let Some(d) = &seeds_dir {
        format!("pool {d}")
    } else {
        arg_val(&args, "--seed-file").expect("--seed-file, --seeds-dir or --trivial required")
    };
    let write_at: usize = arg_val(&args, "--write-at").unwrap_or(cfg.save_at);
    let out: String =
        arg_val(&args, "--out").unwrap_or_else(|| "matmul/found4r".into());
    let lift_below: usize = arg_val(&args, "--lift-below").unwrap_or(48);
    let matmul_dir: String =
        arg_val(&args, "--matmul-dir").unwrap_or_else(|| "matmul".into());
    std::fs::create_dir_all(&out).unwrap();

    let seed: Vec<Summand> = if trivial {
        let (n1, n2, n3) = (cfg.n1, cfg.n2, cfg.n3);
        let mut s = Vec::with_capacity(n1 * n2 * n3);
        for i in 0..n1 {
            for k in 0..n2 {
                for j in 0..n3 {
                    s.push([
                        1u32 << (i * n2 + k),
                        1u32 << (k * n3 + j),
                        1u32 << (i * n3 + j),
                    ]);
                }
            }
        }
        s
    } else if seeds_dir.is_some() {
        Vec::new()
    } else {
        let txt = std::fs::read_to_string(&seed_file).expect("seed file");
        let bits: Vec<u8> = txt
            .split_whitespace()
            .last()
            .unwrap()
            .bytes()
            .map(|b| b - b'0')
            .collect();
        bits_to_summands(&bits, &cfg)
    };
    // the seed pool: every *.bits of the directory, any rank, each checked
    // against the Brent equations at its own rank (2026-11-07, for the
    // projected seeds of matmul/project_f2.py)
    use logic::anf::{brent, verify, Dims};
    let width = cfg.n1 * cfg.n2 + cfg.n2 * cfg.n3 + cfg.n1 * cfg.n3;
    let seeds: Vec<Vec<Summand>> = match &seeds_dir {
        Some(dir) => {
            let mut names: Vec<_> = std::fs::read_dir(dir)
                .expect("seeds dir")
                .filter_map(|e| e.ok().map(|e| e.path()))
                .filter(|p| p.extension().map(|x| x == "bits").unwrap_or(false))
                .collect();
            names.sort();
            let mut anfs: std::collections::HashMap<usize, logic::anf::Anf> = Default::default();
            let mut v = Vec::new();
            for path in names {
                let txt = std::fs::read_to_string(&path).unwrap();
                let bits: Vec<u8> =
                    txt.split_whitespace().last().unwrap().bytes().map(|b| b - b'0').collect();
                assert!(bits.len() % width == 0, "{}: {} bits", path.display(), bits.len());
                let s = bits_to_summands(&bits, &cfg);
                let anf = anfs.entry(s.len()).or_insert_with(|| {
                    brent(Dims { n1: cfg.n1, n2: cfg.n2, n3: cfg.n3, r: s.len() })
                });
                assert_eq!(verify(anf, &bits), 0, "{} fails Brent", path.display());
                v.push(s);
            }
            assert!(!v.is_empty(), "no .bits files in {dir}");
            v
        }
        None => {
            // the seed must be a scheme: check it against the Brent equations
            let anf = brent(Dims { n1: cfg.n1, n2: cfg.n2, n3: cfg.n3, r: seed.len() });
            assert_eq!(verify(&anf, &summands_to_bits(&seed, &cfg)), 0, "seed fails Brent");
            vec![seed]
        }
    };
    let from_desc = if seeds.len() == 1 {
        format!("rank {}", seeds[0].len())
    } else {
        let lo = seeds.iter().map(|s| s.len()).min().unwrap();
        let hi = seeds.iter().map(|s| s.len()).max().unwrap();
        format!("{} seeds of ranks {lo}..{hi}", seeds.len())
    };
    println!(
        "c flip descend: <{},{},{}> from {} ({}), save<={}, write<={}, lift<={}, {} threads, {} min, group-moves {} shuffles {}",
        cfg.n1, cfg.n2, cfg.n3, from_desc, seed_file, cfg.save_at, write_at,
        lift_below, cfg.threads, cfg.minutes, cfg.group_moves, cfg.shuffles
    );

    let record = cfg.record;
    let outdir = out.clone();
    let (counts, min_rank) = descend_campaign_seeds(seeds, cfg, |rk, bits, seq| {
        if rk > write_at && rk >= record {
            return;
        }
        let s: String =
            bits.iter().map(|b| (b + b'0') as char).collect();
        let path = format!("{outdir}/r{rk}-{seq:05}.bits");
        std::fs::write(&path, format!("{s}\n")).unwrap();
        if rk < record {
            println!("{}", "!".repeat(60));
            println!("RANK {rk} < {record} REACHED (verified) -> {path}");
            println!("{}", "!".repeat(60));
        }
        if rk <= lift_below {
            let dims = format!("{},{},{},{}", cfg.n1, cfg.n2, cfg.n3, rk);
            let abs = std::fs::canonicalize(&path).unwrap();
            let r = std::process::Command::new("python3")
                .args(["lift.py", "--dims", &dims,
                       abs.to_str().unwrap(), "--outdir",
                       "found4r-lifted"])
                .current_dir(&matmul_dir)
                .output();
            match r {
                Ok(o) => {
                    let sout = String::from_utf8_lossy(&o.stdout);
                    if sout.contains("LIFTED") {
                        println!("{}", "!".repeat(60));
                        println!(
                            "LIFTABLE rank-{rk} SCHEME over Z: {path}"
                        );
                        println!("{}", "!".repeat(60));
                    } else {
                        println!(
                            "c lift-test r{rk}-{seq:05}: not +-1-liftable"
                        );
                    }
                }
                Err(e) => eprintln!("c lift-test failed to run: {e}"),
            }
        }
    });
    let mut ranks: Vec<_> = counts.iter().collect();
    ranks.sort();
    println!(
        "c DONE: min rank {min_rank}; distinct landings by rank: {ranks:?}"
    );
}
