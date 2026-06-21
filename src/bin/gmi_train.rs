//! `gmi_train` — Burn de-risk: confirm the framework compiles + trains here
//! before building the real constraint-graph GNN.  Trains an MLP to fit a linear
//! target; loss must drop.  Build: `cargo run --features gnn --bin gmi_train`.
//!
//! Two Burn gotchas learned here:
//!  - the `#[derive(Module)]` backend generic MUST be named `B` (the derive
//!    hardcodes that ident in its generated impls);
//!  - do NOT add a manual `#[derive(Clone)]` (the Module derive emits an
//!    id-preserving Clone; a field-wise one reassigns Param ids → no training),
//!    and use the `relu` function rather than a stored non-generic module field.

use burn::backend::ndarray::NdArrayDevice;
use burn::backend::{Autodiff, NdArray};
use burn::module::Module;
use burn::nn::{Linear, LinearConfig};
use burn::optim::{AdamConfig, GradientsParams, Optimizer};
use burn::tensor::activation::relu;
use burn::tensor::{backend::Backend, Distribution, Tensor};

type AD = Autodiff<NdArray<f32>>;

#[derive(Module, Debug)]
struct Mlp<B: Backend> {
    l1: Linear<B>,
    l2: Linear<B>,
}

impl<B: Backend> Mlp<B> {
    fn new(device: &B::Device) -> Self {
        Self {
            l1: LinearConfig::new(4, 16).init(device),
            l2: LinearConfig::new(16, 1).init(device),
        }
    }
    fn forward(&self, x: Tensor<B, 2>) -> Tensor<B, 2> {
        self.l2.forward(relu(self.l1.forward(x)))
    }
}

fn main() {
    let device = NdArrayDevice::default();
    let x = Tensor::<AD, 2>::random([64, 4], Distribution::Uniform(-1.0, 1.0), &device);
    let y = x.clone().sum_dim(1).detach(); // constant target [64,1]

    let mut model: Mlp<AD> = Mlp::new(&device);
    let mut opt = AdamConfig::new().init::<AD, Mlp<AD>>();
    let mut first = 0.0f32;
    for step in 0..400 {
        let loss = (model.forward(x.clone()) - y.clone()).powf_scalar(2.0).mean();
        let lv = loss.clone().into_scalar();
        if step == 0 {
            first = lv;
        }
        let grads = loss.backward();
        let gp = GradientsParams::from_grads::<AD, Mlp<AD>>(grads, &model);
        model = opt.step(1e-2, model, gp);
        if step % 100 == 0 {
            println!("mlp step {step}: loss {lv:.5}");
        }
    }
    let final_loss = (model.forward(x) - y).powf_scalar(2.0).mean().into_scalar();
    println!("MLP: first {first:.5} -> final {final_loss:.5}");
    if final_loss < first * 0.2 {
        println!("BURN OK: trained (loss dropped {:.1}x)", first / final_loss.max(1e-9));
    } else {
        println!("BURN TRAIN STILL BROKEN");
    }
}
