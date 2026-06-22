//! `gmi_mcgs` — Monte-Carlo Graph Search over the GMI constraint-set DAG.
//!
//! Rung 1 of AlphaZero-for-cutting-planes: does a guided graph search (PUCT +
//! transposition merging + rollout value) find SHORTER refutations than
//! best-of-K random rollouts at an EQUAL rollout budget, on the held-out
//! graph-PHP instances?  Pure engine (no Burn): the action prior is the cut
//! violation and the leaf value is a stochastic rollout's proof length.  A node
//! is keyed by its constraint *set* (order-independent), so cut orders reaching
//! the same system share one node and pool statistics — the "graph" (vs tree)
//! the ExpIt non-result called for.
//!
//! Leaf evaluation uses `gmi::mcgs_step`: ONE cold LP solve per leaf, then a
//! warm-started rollout (dual-resolve per added cut) — orders of magnitude
//! faster than re-solving cold every step.  The winning MCGS proof is confirmed
//! exactly in BigRational (`gmi::refutes_exact`).
//!
//! If MCGS clearly beats best-of-K here, the value/visit-count TRAINING loop
//! (rung 2: a learned prior + value head trained on MCGS visit counts, replacing
//! the violation prior and the rollout) is justified.
//!
//! Run: `cargo run --release --bin gmi_mcgs`   (env: SIMS, NTE, CAP, CPUCT)

use logic::gmi::{self, Pb};
use std::collections::HashMap;

type Key = String;
/// One MCGS leaf step (expand + warm rollout); Q fast path or exact BigRational.
type StepFn =
    fn(&[Pb], usize, &[Pb], usize, &mut dyn FnMut(&[f64]) -> usize) -> (bool, Vec<(Pb, f64)>, Option<Vec<Pb>>);

#[derive(Default)]
struct Node {
    n: u32,        // visit count
    w: f64,        // summed value (reward) over visits
    terminal: bool,
    expanded: bool,
    acts: Vec<Act>,
}
struct Act {
    cut: Pb,
    prior: f64,
    child: Key,
}

/// Small LCG — deterministic per seed so runs are reproducible.
struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Rng {
        Rng(seed ^ 0x9e3779b97f4a7c15)
    }
    fn f(&mut self) -> f64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((self.0 >> 33) as f64) / ((1u64 << 31) as f64)
    }
    /// Sample an index ∝ weights, mixed with a uniform ε-floor for exploration.
    fn sample(&mut self, w: &[f64]) -> usize {
        let n = w.len();
        if n == 0 {
            return 0;
        }
        let eps = 0.10;
        let tot: f64 = w.iter().sum::<f64>().max(1e-12);
        let mut r = self.f();
        for i in 0..n {
            let p = (1.0 - eps) * (w[i] / tot) + eps / n as f64;
            if r < p {
                return i;
            }
            r -= p;
        }
        n - 1
    }
}

/// Constraint-set key: sorted multiset of the chosen cuts' canonical keys, so
/// transpositions (same cuts, different order) collapse to one node.
fn state_key(added: &[Pb]) -> Key {
    let mut ks: Vec<String> = added.iter().map(|c| c.key()).collect();
    ks.sort();
    ks.join("|")
}

/// Shorter proof ⇒ higher reward, in [0,1].
fn reward(len: usize, cap: usize) -> f64 {
    1.0 - (len as f64 / cap as f64).min(1.0)
}

fn argmax(v: &[f64]) -> usize {
    (0..v.len())
        .max_by(|&a, &b| v[a].partial_cmp(&v[b]).unwrap_or(std::cmp::Ordering::Equal))
        .unwrap_or(0)
}

/// MCGS from the root (empty cut set): `sims` simulations of select → expand →
/// warm-rollout → backup over the transposition DAG.  Returns the shortest
/// complete proof found.
fn mcgs(
    inputs: &[Pb],
    nvars: usize,
    sims: usize,
    cap: usize,
    c_puct: f64,
    rng: &mut Rng,
    step: StepFn,
) -> Option<Vec<Pb>> {
    let mut dag: HashMap<Key, Node> = HashMap::new();
    let root = state_key(&[]);
    let mut best = usize::MAX;
    let mut best_cuts: Option<Vec<Pb>> = None;
    for _ in 0..sims {
        // ── SELECTION: descend by PUCT until an unexpanded / terminal leaf ──
        let mut added: Vec<Pb> = Vec::new();
        let mut path: Vec<Key> = vec![root.clone()];
        loop {
            let key = path.last().unwrap();
            match dag.get(key) {
                Some(nd) if nd.expanded && !nd.terminal && !nd.acts.is_empty() => {
                    let sn = (nd.n as f64).max(1.0);
                    let (mut bi, mut bu) = (0usize, f64::NEG_INFINITY);
                    for (i, a) in nd.acts.iter().enumerate() {
                        let (cn, cq) = match dag.get(&a.child) {
                            Some(c) if c.n > 0 => (c.n as f64, c.w / c.n as f64),
                            _ => (0.0, 0.0),
                        };
                        let u = cq + c_puct * a.prior * sn.sqrt() / (1.0 + cn);
                        if u > bu {
                            bu = u;
                            bi = i;
                        }
                    }
                    let a = &nd.acts[bi];
                    added.push(a.cut.clone());
                    path.push(a.child.clone());
                }
                _ => break,
            }
        }
        // ── EXPANSION + EVALUATION (one cold solve + warm rollout) ──
        let leaf = path.last().unwrap().clone();
        let (term, cands, proof) = {
            let mut pick = |v: &[f64]| rng.sample(v);
            step(inputs, nvars, &added, cap, &mut pick)
        };
        if let Some(ref pr) = proof {
            if pr.len() < best {
                best = pr.len();
                best_cuts = Some(pr.clone());
            }
        }
        let value = if term {
            let nd = dag.entry(leaf).or_default();
            nd.terminal = true;
            nd.expanded = true;
            reward(added.len(), cap)
        } else {
            let tot: f64 = cands.iter().map(|(_, v)| v.max(1e-9)).sum::<f64>().max(1e-12);
            let acts = cands
                .iter()
                .map(|(cut, v)| {
                    let mut ca = added.clone();
                    ca.push(cut.clone());
                    Act {
                        cut: cut.clone(),
                        prior: v.max(1e-9) / tot,
                        child: state_key(&ca),
                    }
                })
                .collect();
            {
                let nd = dag.entry(leaf).or_default();
                nd.acts = acts;
                nd.expanded = true;
            }
            match proof {
                Some(pr) => reward(pr.len(), cap),
                None => 0.0,
            }
        };
        // ── BACKUP (graph: every node on the path, transpositions pooled) ──
        for k in &path {
            let nd = dag.entry(k.clone()).or_default();
            nd.n += 1;
            nd.w += value;
        }
    }
    best_cuts
}

fn main() {
    let envn = |k: &str, d: usize| std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d);
    let sims = envn("SIMS", 400);
    let nte = envn("NTE", 8);
    let cap = envn("CAP", 150);
    let c_puct: f64 = std::env::var("CPUCT")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(1.5);
    let (p, h) = (envn("P", 6), envn("H", 5));
    let dens: f64 = std::env::var("DENS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(0.7);
    // exact BigRational by default (the headroom regime overflows i128); EXACT=0 → Q
    let exact = std::env::var("EXACT").map(|v| v != "0").unwrap_or(true);
    let step: StepFn = if exact { gmi::mcgs_step_exact } else { gmi::mcgs_step };
    println!(
        "MCGS over the GMI constraint DAG — g-PHP({p},{h}) dens {dens}, sims={sims}, c_puct={c_puct}"
    );
    println!("  best-of-K uses K=sims (equal rollout budget); greedy = argmax-violation\n");
    let t0 = std::time::Instant::now();
    let (mut sg, mut sk, mut sm, mut cnt, mut wins) = (0usize, 0usize, 0usize, 0usize, 0usize);
    for s in 0..nte {
        let (nvars, clauses) = gmi::graph_php(p, h, dens, 1000 + s as u64);
        let inputs: Vec<Pb> = clauses.iter().map(|c| Pb::from_clause(c)).collect();
        let mut rng = Rng::new(7 + s as u64);
        // greedy: deterministic argmax-violation rollout from root
        let greedy = {
            let mut pick = |v: &[f64]| argmax(v);
            step(&inputs, nvars, &[], cap, &mut pick).2.map(|c| c.len())
        };
        // best-of-K: K = sims stochastic rollouts from root (equal budget vs MCGS)
        let mut bok = usize::MAX;
        for _ in 0..sims {
            let mut pick = |v: &[f64]| rng.sample(v);
            if let Some(c) = step(&inputs, nvars, &[], cap, &mut pick).2 {
                bok = bok.min(c.len());
            }
        }
        let mc = mcgs(&inputs, nvars, sims, cap, c_puct, &mut rng, step);
        match (greedy, mc) {
            (Some(g), Some(proof)) if bok != usize::MAX => {
                let m = proof.len();
                let ok = if gmi::refutes_exact(&inputs, nvars, &proof) {
                    "✓"
                } else {
                    "✗UNSOUND"
                };
                let flag = if m < bok {
                    wins += 1;
                    "  ← MCGS wins"
                } else if m > bok {
                    "  (best-of-K wins)"
                } else {
                    "  (tie)"
                };
                println!("  inst {s}: greedy {g:>3}  best-of-K {bok:>3}  MCGS {m:>3} {ok}{flag}");
                use std::io::Write;
                std::io::stdout().flush().ok();
                sg += g;
                sk += bok;
                sm += m;
                cnt += 1;
            }
            _ => println!("  inst {s}: (no refutation within cap)"),
        }
    }
    if cnt > 0 {
        println!(
            "\n  AVG over {cnt}: greedy {:.1}  best-of-K {:.1}  MCGS {:.1} cuts   (MCGS strictly wins {wins}/{cnt})   [{:.1}s]",
            sg as f64 / cnt as f64,
            sk as f64 / cnt as f64,
            sm as f64 / cnt as f64,
            t0.elapsed().as_secs_f64(),
        );
    }
}
