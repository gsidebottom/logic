//! `gmi_train` — Rust/Burn GNN cut-scorer over the GMI constraint graph.
//!
//! Reproduces the MLX de-risk in Rust: on the asymmetric graph-PHP family a GNN
//! over the bipartite var×constraint graph should beat a logistic over intrinsic
//! cut features at predicting cut-usefulness.  Data comes from the fast Rust
//! engine (`gmi::gen_data`).  Build: `cargo run --release --features gnn --bin gmi_train`.
//!
//! Burn-0.21 gotchas (learned the hard way): the `#[derive(Module)]` backend
//! generic MUST be named `B`; never add a manual `#[derive(Clone)]` (the derive
//! emits an id-preserving one); use the `relu` function, not a stored field.

use burn::backend::Autodiff;
use burn::module::Module;
use burn::nn::{LayerNorm, LayerNormConfig, Linear, LinearConfig};
use burn::optim::{AdamConfig, GradientsParams, Optimizer};
use burn::tensor::activation::{relu, sigmoid};
use burn::tensor::{backend::Backend, Int, Tensor, TensorData};
use logic::gmi::{self, Pb, Snapshot};

// Backend swap: `--features gpu` → Burn Metal (wgpu) on Apple Silicon; else CPU.
#[cfg(not(feature = "gpu"))]
type BK = burn::backend::NdArray<f32>;
#[cfg(not(feature = "gpu"))]
type Dev = burn::backend::ndarray::NdArrayDevice;
#[cfg(feature = "gpu")]
type BK = burn::backend::Metal<f32, i32>;
#[cfg(feature = "gpu")]
type Dev = burn::backend::wgpu::WgpuDevice;
type AD = Autodiff<BK>;

// ── graph-PHP generator (sparse random bipartite pigeonhole) ─────────────────

fn graph_php(p: usize, h: usize, density: f64, seed: u64) -> (usize, Vec<Vec<i32>>) {
    let mut st = seed.wrapping_mul(0x9e3779b97f4a7c15).wrapping_add(12345);
    let mut rng = || {
        st = st.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        ((st >> 33) as f64) / ((1u64 << 31) as f64)
    };
    let mut nv = 0i32;
    let mut nbr: Vec<Vec<i32>> = vec![Vec::new(); p];
    let mut incid: Vec<Vec<i32>> = vec![Vec::new(); h];
    for pig in 0..p {
        let mut hs: Vec<usize> = (0..h).filter(|_| rng() < density).collect();
        if hs.is_empty() {
            hs.push((rng() * h as f64) as usize % h);
        }
        for hole in hs {
            nv += 1;
            nbr[pig].push(nv);
            incid[hole].push(nv);
        }
    }
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    for pig in 0..p {
        clauses.push(nbr[pig].clone()); // >= 1 hole
    }
    for es in &incid {
        for i in 0..es.len() {
            for j in i + 1..es.len() {
                clauses.push(vec![-es[i], -es[j]]); // <= 1 pigeon
            }
        }
    }
    (nv as usize, clauses)
}

// ── intrinsic cut features (the logistic baseline) ───────────────────────────

fn feats5(cut: &Pb, x: &[f64], nvars: usize) -> [f32; 5] {
    let viol = cut.rhs_f64() - cut.dot(x);
    let coefs: Vec<f64> = cut.coefs_f64();
    let maxc = coefs.iter().fold(0.0f64, |a, &c| a.max(c.abs()));
    [
        viol as f32,
        cut.rhs_f64().abs() as f32,
        coefs.len() as f32,
        maxc as f32,
        coefs.len() as f32 / nvars.max(1) as f32,
    ]
}

/// Logistic regression (manual GD, standardized) → held-out accuracy.
fn logistic_ab(train: &[([f32; 5], f32)], test: &[([f32; 5], f32)]) -> f64 {
    let n = train.len().max(1) as f32;
    let mut mu = [0.0f32; 5];
    let mut sd = [0.0f32; 5];
    for (f, _) in train {
        for k in 0..5 {
            mu[k] += f[k] / n;
        }
    }
    for (f, _) in train {
        for k in 0..5 {
            sd[k] += (f[k] - mu[k]).powi(2) / n;
        }
    }
    for k in 0..5 {
        sd[k] = sd[k].sqrt().max(1e-6);
    }
    let z = |f: &[f32; 5]| {
        let mut o = [0.0f32; 5];
        for k in 0..5 {
            o[k] = ((f[k] - mu[k]) / sd[k]).clamp(-10.0, 10.0);
        }
        o
    };
    let (mut w, mut b) = ([0.0f32; 5], 0.0f32);
    for _ in 0..2000 {
        let (mut gw, mut gb) = ([0.0f32; 5], 0.0f32);
        for (f, y) in train {
            let zz = z(f);
            let logit = (0..5).map(|k| w[k] * zz[k]).sum::<f32>() + b;
            let g = 1.0 / (1.0 + (-logit).exp()) - y;
            for k in 0..5 {
                gw[k] += g * zz[k] / n;
            }
            gb += g / n;
        }
        for k in 0..5 {
            w[k] -= 0.3 * (gw[k] + 0.01 * w[k]);
        }
        b -= 0.3 * gb;
    }
    let mut ok = 0;
    for (f, y) in test {
        let zz = z(f);
        let logit = (0..5).map(|k| w[k] * zz[k]).sum::<f32>() + b;
        let pred = if 1.0 / (1.0 + (-logit).exp()) >= 0.5 { 1.0 } else { 0.0 };
        if (pred - y).abs() < 0.5 {
            ok += 1;
        }
    }
    ok as f64 / test.len().max(1) as f64
}

// ── GNN over the bipartite var×constraint graph ──────────────────────────────

struct Graph {
    m: Tensor<AD, 2>,         // C × nvars  (coefficients)
    mt: Tensor<AD, 2>,        // nvars × C
    vfeat: Tensor<AD, 2>,     // nvars × 2
    cfeat: Tensor<AD, 2>,     // C × 3
    cand: Tensor<AD, 1, Int>, // candidate row indices
    ncand: usize,
    labels: Vec<f32>, // empty for inference
}

/// Build the bipartite var×constraint graph from the constraint nodes (`cons`),
/// the LP point `x`, and the candidate cuts to score.  Used for both training
/// (via `build_graph`) and in-loop inference (the scorer closure).
fn build_graph_raw(cons: &[Pb], x: &[f64], cands: &[Pb], nvars: usize, device: &Dev) -> Graph {
    let nodes: Vec<&Pb> = cons.iter().chain(cands.iter()).collect();
    let cc = nodes.len();
    let mut m = vec![0.0f32; cc * nvars];
    let mut cfeat = vec![0.0f32; cc * 3];
    for (c, pb) in nodes.iter().enumerate() {
        let absum = 1.0 + pb.coefs_f64().iter().map(|x| x.abs()).sum::<f64>();
        let slack = pb.dot(x) - pb.rhs_f64();
        for (v, coef) in pb.coef_f64_pairs() {
            if v >= 1 && v <= nvars {
                m[c * nvars + (v - 1)] = coef as f32;
            }
        }
        cfeat[c * 3] = (pb.rhs_f64() / absum) as f32;
        cfeat[c * 3 + 1] = (slack / absum) as f32;
        cfeat[c * 3 + 2] = if c >= cons.len() { 1.0 } else { 0.0 };
    }
    let mut vfeat = vec![0.0f32; nvars * 2];
    for v in 0..nvars {
        let xv = x.get(v).copied().unwrap_or(0.0);
        vfeat[v * 2] = xv as f32;
        vfeat[v * 2 + 1] = xv.min(1.0 - xv) as f32;
    }
    let cand: Vec<i64> = (cons.len()..cc).map(|i| i as i64).collect();
    let mk2 = |data: Vec<f32>, r: usize, c: usize| {
        Tensor::<AD, 2>::from_data(TensorData::new(data, [r, c]), device)
    };
    let mt = mk2(m.clone(), cc, nvars).transpose();
    Graph {
        m: mk2(m, cc, nvars),
        mt,
        vfeat: mk2(vfeat, nvars, 2),
        cfeat: mk2(cfeat, cc, 3),
        cand: Tensor::<AD, 1, Int>::from_data(TensorData::new(cand, [cands.len()]), device),
        ncand: cands.len(),
        labels: Vec::new(),
    }
}

fn build_graph(snap: &Snapshot, device: &Dev) -> Graph {
    let mut g = build_graph_raw(&snap.cons, &snap.x, &snap.cand_cuts, snap.nvars, device);
    g.labels = snap.labels.clone();
    g
}

/// GNN cut-usefulness logits for the candidates given the current (cons, x*).
fn gnn_logits(model: &CutGnn<AD>, device: &Dev, cons: &[Pb], x: &[f64], cands: &[Pb]) -> Vec<f64> {
    let nv = cons
        .iter()
        .chain(cands.iter())
        .flat_map(|p| p.coef_f64_pairs())
        .map(|(v, _)| v)
        .max()
        .unwrap_or(1);
    let g = build_graph_raw(cons, x, cands, nv, device);
    model
        .forward(&g)
        .into_data()
        .to_vec::<f32>()
        .unwrap()
        .into_iter()
        .map(|v| v as f64)
        .collect()
}

#[derive(Module, Debug)]
struct CutGnn<B: Backend> {
    v_emb: Linear<B>,
    c_emb: Linear<B>,
    v2c: Linear<B>,
    c2v: Linear<B>,
    c_upd: Linear<B>,
    v_upd: Linear<B>,
    ln_c: LayerNorm<B>,
    ln_v: LayerNorm<B>,
    r1: Linear<B>,
    r2: Linear<B>,
    rounds: usize,
}

impl<B: Backend> CutGnn<B> {
    fn new(dim: usize, rounds: usize, device: &B::Device) -> Self {
        Self {
            v_emb: LinearConfig::new(2, dim).init(device),
            c_emb: LinearConfig::new(3, dim).init(device),
            v2c: LinearConfig::new(dim, dim).init(device),
            c2v: LinearConfig::new(dim, dim).init(device),
            c_upd: LinearConfig::new(2 * dim, dim).init(device),
            v_upd: LinearConfig::new(2 * dim, dim).init(device),
            ln_c: LayerNormConfig::new(dim).init(device),
            ln_v: LayerNormConfig::new(dim).init(device),
            r1: LinearConfig::new(dim, dim).init(device),
            r2: LinearConfig::new(dim, 1).init(device),
            rounds,
        }
    }
}

impl CutGnn<AD> {
    fn forward(&self, g: &Graph) -> Tensor<AD, 1> {
        let mut v = self.v_emb.forward(g.vfeat.clone());
        let mut c = self.c_emb.forward(g.cfeat.clone());
        for _ in 0..self.rounds {
            let c_msg = g.m.clone().matmul(self.v2c.forward(v.clone()));
            let c_in = Tensor::cat(vec![c.clone(), c_msg], 1);
            c = self.ln_c.forward(c.clone() + self.c_upd.forward(c_in).tanh());
            let v_msg = g.mt.clone().matmul(self.c2v.forward(c.clone()));
            let v_in = Tensor::cat(vec![v.clone(), v_msg], 1);
            v = self.ln_v.forward(v.clone() + self.v_upd.forward(v_in).tanh());
        }
        let logits = self.r2.forward(relu(self.r1.forward(c))); // C × 1
        logits.select(0, g.cand.clone()).reshape([g.ncand])
    }
}

fn bce_with_logits(logits: Tensor<AD, 1>, labels: &[f32], device: &Dev) -> Tensor<AD, 1> {
    let y = Tensor::<AD, 1>::from_data(TensorData::new(labels.to_vec(), [labels.len()]), device);
    // stable: relu(z) - z*y + log(1+exp(-|z|))
    let max0 = logits.clone().clamp_min(0.0);
    let term = max0 - logits.clone() * y + (logits.abs().neg().exp() + 1.0).log();
    term.mean()
}

fn gnn_acc(model: &CutGnn<AD>, graphs: &[Graph]) -> f64 {
    let (mut ok, mut tot) = (0usize, 0usize);
    for g in graphs {
        let p = sigmoid(model.forward(g)).into_data().to_vec::<f32>().unwrap();
        for (pi, yi) in p.iter().zip(g.labels.iter()) {
            if ((*pi >= 0.5) as i32 as f32 - yi).abs() < 0.5 {
                ok += 1;
            }
            tot += 1;
        }
    }
    ok as f64 / tot.max(1) as f64
}

/// Run `f(i, model, device)` for i in 0..n via rayon.  CutGnn is Sync, so the
/// model + device are SHARED (no per-thread clone).  Crucially this uses rayon
/// for the OUTER loop too: burn-ndarray's ops are themselves rayon, so a single
/// shared pool composes via work-stealing — whereas a std::thread outer pool
/// nested over burn's rayon oversubscribes and spins (10× slower, learned the
/// hard way).  Results in index order.
fn par_instances<R: Send>(
    n: usize,
    model: &CutGnn<AD>,
    device: &Dev,
    f: impl Fn(usize, &CutGnn<AD>, &Dev) -> R + Sync,
) -> Vec<R> {
    use rayon::prelude::*;
    (0..n).into_par_iter().map(|i| f(i, model, device)).collect()
}

/// Train a fresh GNN on the given graphs (mini-batched, lr-decayed).
fn train_gnn(tr: &[Graph], device: &Dev, epochs: usize) -> CutGnn<AD> {
    let mut model = CutGnn::<AD>::new(32, 8, device);
    let mut opt = AdamConfig::new().init::<AD, CutGnn<AD>>();
    let bs = 16;
    for ep in 1..=epochs {
        let lr = if ep * 3 <= epochs * 2 { 3e-3 } else { 1e-3 };
        let mut i = 0;
        while i < tr.len() {
            let end = (i + bs).min(tr.len());
            let total = tr[i..end]
                .iter()
                .map(|g| bce_with_logits(model.forward(g), &g.labels, device))
                .reduce(|a, b| a + b)
                .unwrap();
            let grads = GradientsParams::from_grads::<AD, CutGnn<AD>>(total.backward(), &model);
            model = opt.step(lr, model, grads);
            i = end;
        }
    }
    model
}

fn main() {
    #[cfg(not(feature = "gpu"))]
    let device = burn::backend::ndarray::NdArrayDevice::default();
    #[cfg(feature = "gpu")]
    let device = burn::backend::wgpu::WgpuDevice::default();
    println!(
        "backend: {} | rayon {} threads",
        if cfg!(feature = "gpu") { "Metal (GPU)" } else { "NdArray (CPU)" },
        rayon::current_num_threads()
    );
    let (p, h, dens) = (6usize, 5usize, 0.7f64);
    let envn = |k: &str, d: usize| std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d);
    let (ntr, nte, epochs) = (envn("NTR", 16), envn("NTE", 8), envn("EPOCHS", 300));

    // generate data via the fast Rust engine — parallel (pure engine, no Burn)
    use rayon::prelude::*;
    let gendata = |seeds: std::ops::Range<usize>, base: u64| -> Vec<Snapshot> {
        seeds
            .into_par_iter()
            .flat_map(|s| {
                let (nv, cl) = graph_php(p, h, dens, base + s as u64);
                gmi::gen_data(&cl, nv, 200, 4, 30.0, 1.0, None).0
            })
            .collect()
    };
    let t_data = std::time::Instant::now();
    let tr_snaps = gendata(0..ntr, 0);
    let te_snaps = gendata(0..nte, 1000);
    eprintln!("c data-gen {:.1}s", t_data.elapsed().as_secs_f64());
    let ncand = |ss: &[Snapshot]| ss.iter().map(|s| s.labels.len()).sum::<usize>();
    let npos = |ss: &[Snapshot]| ss.iter().flat_map(|s| &s.labels).filter(|&&l| l > 0.5).count();
    println!(
        "train: {} snaps, {} cands ({} useful); test: {} snaps, {} cands ({} useful)",
        tr_snaps.len(), ncand(&tr_snaps), npos(&tr_snaps),
        te_snaps.len(), ncand(&te_snaps), npos(&te_snaps)
    );

    // logistic baseline on the same data
    let to_feat = |ss: &[Snapshot]| -> Vec<([f32; 5], f32)> {
        ss.iter()
            .flat_map(|s| {
                s.cand_cuts
                    .iter()
                    .zip(s.labels.iter())
                    .map(move |(cut, &lab)| (feats5(cut, &s.x, s.nvars), lab))
            })
            .collect()
    };
    let log_acc = logistic_ab(&to_feat(&tr_snaps), &to_feat(&te_snaps));
    let base = {
        let pos = npos(&te_snaps);
        let tot = ncand(&te_snaps);
        (pos.max(tot - pos)) as f64 / tot.max(1) as f64
    };

    // build graphs + train the GNN
    let tr: Vec<Graph> = tr_snaps.iter().map(|s| build_graph(s, &device)).collect();
    let te: Vec<Graph> = te_snaps.iter().map(|s| build_graph(s, &device)).collect();
    let t_train = std::time::Instant::now();
    let model = train_gnn(&tr, &device, epochs);
    let (best, last) = (gnn_acc(&model, &te), gnn_acc(&model, &te));
    println!("  (imitation GNN: 300 epochs in {:.1}s)", t_train.elapsed().as_secs_f64());
    println!("\n=== A/B (held-out g-PHP cut-usefulness accuracy) ===");
    println!("  majority baseline : {base:.3}");
    println!("  logistic (5 feats): {log_acc:.3}");
    println!("  GNN (graph)       : {last:.3} final, {best:.3} best");

    // Per-instance rollout loops below are embarrassingly parallel → 12 threads.
    let mknoisy_seed = |s: usize, k: usize, salt: u64| {
        salt.wrapping_add((s as u64 * 131 + k as u64) * 0x9e3779b97f4a7c15)
    };

    // ── end-to-end: GNN as the in-loop cut selector vs add-all & logistic ──
    println!("\n=== end-to-end refutation cut counts (held-out g-PHP, top-50%/round) ===");
    let ab: Vec<(Option<usize>, Option<usize>, Option<usize>)> =
        par_instances(nte, &model, &device, |s, m, dev| {
            let (nv, cl) = graph_php(p, h, dens, 1000 + s as u64);
            let add = gmi::refute(&cl, nv, 200, 4, 30.0).map(|r| r.cuts.len());
            let log = gmi::refute_policy(&cl, nv, 200, 4, 30.0, 0.5).map(|r| r.cuts.len());
            let sc = |cons: &[Pb], x: &[f64], cands: &[Pb]| gnn_logits(m, dev, cons, x, cands);
            let gnn = gmi::refute_scored(&cl, nv, 200, 4, 30.0, 0.5, &sc).map(|r| r.cuts.len());
            (add, log, gnn)
        });
    let (mut s_add, mut s_log, mut s_gnn, mut n) = (0usize, 0usize, 0usize, 0usize);
    for s in 0..ab.len() {
        if let (Some(a), Some(l), Some(gg)) = ab[s] {
            s_add += a;
            s_log += l;
            s_gnn += gg;
            n += 1;
            println!("  inst {s}: add-all {a:3}  logistic {l:3}  GNN {gg:3}");
        }
    }
    if n > 0 {
        println!(
            "  AVG over {n}: add-all {:.1}  logistic {:.1}  GNN {:.1} cuts",
            s_add as f64 / n as f64,
            s_log as f64 / n as f64,
            s_gnn as f64 / n as f64
        );
    }

    // ── ExpIt de-risk: best-of-K stochastic search vs the deterministic policy ──
    println!("\n=== ExpIt de-risk: best-of-K search vs deterministic GNN policy ===");
    let kk = 12usize;
    let bok_res: Vec<(Option<usize>, usize)> = par_instances(nte, &model, &device, |s, m, dev| {
        let (nv, cl) = graph_php(p, h, dens, 1000 + s as u64);
        let scd = |cons: &[Pb], x: &[f64], cands: &[Pb]| gnn_logits(m, dev, cons, x, cands);
        let det = gmi::refute_scored(&cl, nv, 200, 4, 30.0, 0.5, &scd).map(|r| r.cuts.len());
        let mut bok = usize::MAX;
        for k in 0..kk {
            let rng = std::cell::Cell::new(mknoisy_seed(s, k, 0x1234));
            let noisy = |cons: &[Pb], x: &[f64], cands: &[Pb]| -> Vec<f64> {
                let mut sc = gnn_logits(m, dev, cons, x, cands);
                for v in sc.iter_mut() {
                    let mut r = rng.get();
                    r = r.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                    rng.set(r);
                    *v += 2.0 * (((r >> 33) as f64) / ((1u64 << 31) as f64) - 0.5);
                }
                sc
            };
            if let Some(r) = gmi::refute_scored(&cl, nv, 200, 4, 30.0, 0.5, &noisy) {
                bok = bok.min(r.cuts.len());
            }
        }
        (det, bok)
    });
    let (mut s_det, mut s_bok, mut n2) = (0usize, 0usize, 0usize);
    for s in 0..bok_res.len() {
        let (det, bok) = bok_res[s];
        if let (Some(d), true) = (det, bok != usize::MAX) {
            s_det += d;
            s_bok += bok;
            n2 += 1;
            println!("  inst {s}: deterministic {d:3}  best-of-{kk} {bok:3}");
        }
    }
    let bok_avg = if n2 > 0 { s_bok as f64 / n2 as f64 } else { 0.0 };
    if n2 > 0 {
        println!(
            "  AVG over {n2}: deterministic {:.1}  best-of-{kk} {:.1} cuts",
            s_det as f64 / n2 as f64,
            bok_avg
        );
    }

    // ── ExpIt iteration: relabel on shortest rollouts, retrain, compare ──
    println!("\n=== ExpIt iteration: retrain on search-improved (shortest-rollout) data ===");
    let per_inst: Vec<Vec<Snapshot>> = par_instances(ntr, &model, &device, |s, m, dev| {
        let (nv, cl) = graph_php(p, h, dens, s as u64);
        let mut best_len = usize::MAX;
        let mut best_snaps: Vec<Snapshot> = Vec::new();
        for k in 0..6 {
            let rng = std::cell::Cell::new(mknoisy_seed(s, k, 0x77));
            let noisy = |cons: &[Pb], x: &[f64], cands: &[Pb]| -> Vec<f64> {
                let mut sc = gnn_logits(m, dev, cons, x, cands);
                for v in sc.iter_mut() {
                    let mut r = rng.get();
                    r = r.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                    rng.set(r);
                    *v += 2.0 * (((r >> 33) as f64) / ((1u64 << 31) as f64) - 0.5);
                }
                sc
            };
            let (snaps, nc) = gmi::gen_data(&cl, nv, 200, 4, 30.0, 0.5, Some(&noisy));
            if nc > 0 && nc < best_len {
                best_len = nc;
                best_snaps = snaps;
            }
        }
        best_snaps
    });
    let search_snaps: Vec<Snapshot> = per_inst.into_iter().flatten().collect();
    let search_graphs: Vec<Graph> = search_snaps.iter().map(|s| build_graph(s, &device)).collect();
    println!("  search-improved data: {} snapshots", search_graphs.len());
    let model2 = train_gnn(&search_graphs, &device, epochs);

    // final A/B: imitation policy (reuse model's GNN column) vs ExpIt policy (model2)
    let m2_cuts: Vec<Option<usize>> = par_instances(nte, &model2, &device, |s, m, dev| {
        let (nv, cl) = graph_php(p, h, dens, 1000 + s as u64);
        let sc = |cons: &[Pb], x: &[f64], cands: &[Pb]| gnn_logits(m, dev, cons, x, cands);
        gmi::refute_scored(&cl, nv, 200, 4, 30.0, 0.5, &sc).map(|r| r.cuts.len())
    });
    let (mut s_im, mut s_ex, mut n4) = (0usize, 0usize, 0usize);
    for s in 0..nte {
        if let (Some(a), Some(b)) = (ab[s].2, m2_cuts[s]) {
            s_im += a;
            s_ex += b;
            n4 += 1;
            println!("  inst {s}: imitation-GNN {a:3}  ExpIt-GNN {b:3}");
        }
    }
    if n4 > 0 {
        println!(
            "  AVG over {n4}: imitation-GNN {:.1}  ExpIt-GNN {:.1} cuts  (best-of-K search was {:.1})",
            s_im as f64 / n4 as f64,
            s_ex as f64 / n4 as f64,
            bok_avg
        );
    }
}
