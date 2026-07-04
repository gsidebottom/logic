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
//! example:
//!   flip 4 4 4 --seed-file matmul/seeds4triv/trivial64.bits \
//!        --minutes 90 --threads 10
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
    };
    let seed_file: String = arg_val(&args, "--seed-file")
        .expect("--seed-file required");
    let out: String =
        arg_val(&args, "--out").unwrap_or_else(|| "matmul/found4r".into());
    let lift_below: usize = arg_val(&args, "--lift-below").unwrap_or(48);
    let matmul_dir: String =
        arg_val(&args, "--matmul-dir").unwrap_or_else(|| "matmul".into());
    std::fs::create_dir_all(&out).unwrap();

    let txt = std::fs::read_to_string(&seed_file).expect("seed file");
    let bits: Vec<u8> = txt
        .split_whitespace()
        .last()
        .unwrap()
        .bytes()
        .map(|b| b - b'0')
        .collect();
    let seed = bits_to_summands(&bits, &cfg);
    println!(
        "c flip descend: <{},{},{}> from rank {} ({}), save<={}, lift<={}, {} threads, {} min",
        cfg.n1, cfg.n2, cfg.n3, seed.len(), seed_file, cfg.save_at,
        lift_below, cfg.threads, cfg.minutes
    );

    let record = cfg.record;
    let outdir = out.clone();
    let (counts, min_rank) = descend_campaign(seed, cfg, |rk, bits, seq| {
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
