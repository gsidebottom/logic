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
    labels: Vec<f32>,
}

fn build_graph(snap: &Snapshot, device: &Dev) -> Graph {
    let nvars = snap.nvars;
    let nodes: Vec<&Pb> = snap.cons.iter().chain(snap.cand_cuts.iter()).collect();
    let cc = nodes.len();
    let mut m = vec![0.0f32; cc * nvars];
    let mut cfeat = vec![0.0f32; cc * 3];
    for (c, pb) in nodes.iter().enumerate() {
        let absum = 1.0 + pb.coefs_f64().iter().map(|x| x.abs()).sum::<f64>();
        let slack = pb.dot(&snap.x) - pb.rhs_f64();
        for (v, coef) in pb.coef_f64_pairs() {
            m[c * nvars + (v - 1)] = coef as f32;
        }
        cfeat[c * 3] = (pb.rhs_f64() / absum) as f32;
        cfeat[c * 3 + 1] = (slack / absum) as f32;
        cfeat[c * 3 + 2] = if c >= snap.cons.len() { 1.0 } else { 0.0 };
    }
    let mut vfeat = vec![0.0f32; nvars * 2];
    for v in 0..nvars {
        let xv = snap.x.get(v).copied().unwrap_or(0.0);
        vfeat[v * 2] = xv as f32;
        vfeat[v * 2 + 1] = xv.min(1.0 - xv) as f32;
    }
    let cand: Vec<i64> = (snap.cons.len()..cc).map(|i| i as i64).collect();
    let mk2 = |data: Vec<f32>, r: usize, c: usize| {
        Tensor::<AD, 2>::from_data(TensorData::new(data, [r, c]), device)
    };
    let mt = mk2(m.clone(), cc, nvars).transpose();
    Graph {
        m: mk2(m, cc, nvars),
        mt,
        vfeat: mk2(vfeat, nvars, 2),
        cfeat: mk2(cfeat, cc, 3),
        cand: Tensor::<AD, 1, Int>::from_data(
            TensorData::new(cand, [snap.cand_cuts.len()]),
            device,
        ),
        labels: snap.labels.clone(),
    }
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
        logits.select(0, g.cand.clone()).reshape([g.labels.len()])
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

fn main() {
    #[cfg(not(feature = "gpu"))]
    let device = burn::backend::ndarray::NdArrayDevice::default();
    #[cfg(feature = "gpu")]
    let device = burn::backend::wgpu::WgpuDevice::default();
    println!("backend: {}", if cfg!(feature = "gpu") { "Metal (GPU)" } else { "NdArray (CPU)" });
    let (p, h, dens) = (6usize, 5usize, 0.7f64);
    let (ntr, nte) = (16usize, 8usize);

    // generate data via the fast Rust engine
    let mut tr_snaps: Vec<Snapshot> = Vec::new();
    let mut te_snaps: Vec<Snapshot> = Vec::new();
    for s in 0..ntr {
        let (nv, cl) = graph_php(p, h, dens, s as u64);
        tr_snaps.extend(gmi::gen_data(&cl, nv, 200, 4, 30.0));
    }
    for s in 0..nte {
        let (nv, cl) = graph_php(p, h, dens, 1000 + s as u64);
        te_snaps.extend(gmi::gen_data(&cl, nv, 200, 4, 30.0));
    }
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
    let mut model = CutGnn::<AD>::new(32, 8, &device);
    let mut opt = AdamConfig::new().init::<AD, CutGnn<AD>>();
    let (mut best, mut last) = (0.0f64, 0.0f64);
    let bs = 16; // mini-batch over graphs (denoise vs per-graph SGD)
    let t_train = std::time::Instant::now();
    for ep in 1..=300 {
        let lr = if ep <= 200 { 3e-3 } else { 1e-3 }; // decay for stability late
        let mut i = 0;
        while i < tr.len() {
            let end = (i + bs).min(tr.len());
            let total = tr[i..end]
                .iter()
                .map(|g| bce_with_logits(model.forward(g), &g.labels, &device))
                .reduce(|a, b| a + b)
                .unwrap();
            let grads = GradientsParams::from_grads::<AD, CutGnn<AD>>(total.backward(), &model);
            model = opt.step(lr, model, grads);
            i = end;
        }
        if ep % 50 == 0 || ep == 300 {
            last = gnn_acc(&model, &te);
            best = best.max(last);
            println!("  ep{ep}: train_acc {:.3}  test_acc {:.3}", gnn_acc(&model, &tr), last);
        }
    }

    println!("  (300 epochs trained in {:.1}s)", t_train.elapsed().as_secs_f64());
    println!("\n=== A/B (held-out g-PHP cut-usefulness accuracy) ===");
    println!("  majority baseline : {base:.3}");
    println!("  logistic (5 feats): {log_acc:.3}");
    println!("  GNN (graph)       : {last:.3} final, {best:.3} best");
}
