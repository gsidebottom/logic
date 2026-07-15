//! benchzk — measure the zkML paper's constraint predictions on a
//! real Groth16 stack (arkworks, BN254). Three gadgets prove the
//! witness x witness product C = A * B:
//!   naive     n^3 multiplication constraints
//!   strassen  2x2:7 recursion (integer coefficients)
//!   rank48    4x4:48 recursion (DPS dyadic coefficients, the same
//!             Brent-verified trio our flip engines load)
//! Additions and constant scalings are free in R1CS: they fold into
//! linear combinations (ark-r1cs-std FpVar + and *constant do not
//! allocate constraints), so measured constraint counts must equal
//! the paper's table: n^3 vs 7^(log2 n) vs 48^(log4 n), plus n^2
//! public-output equality rows identical across gadgets.
//!
//! Usage: benchzk <n> <naive|strassen|rank48> [--prove]
mod coeffs;

use ark_bn254::{Bn254, Fr};
use ark_ff::{Field, One, UniformRand, Zero};
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::R1CSVar;
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, SynthesisError,
};
use ark_snark::SNARK;
use ark_std::rand::SeedableRng;
use std::time::Instant;

type M = Vec<Vec<FpVar<Fr>>>;

fn zeros(n: usize) -> M {
    vec![vec![FpVar::zero(); n]; n]
}

fn madd(x: &M, y: &M) -> M {
    let n = x.len();
    let mut o = zeros(n);
    for i in 0..n {
        for j in 0..n {
            o[i][j] = &x[i][j] + &y[i][j];
        }
    }
    o
}

fn msub(x: &M, y: &M) -> M {
    let n = x.len();
    let mut o = zeros(n);
    for i in 0..n {
        for j in 0..n {
            o[i][j] = &x[i][j] - &y[i][j];
        }
    }
    o
}

fn block(x: &M, bi: usize, bj: usize, h: usize) -> M {
    (0..h)
        .map(|i| (0..h).map(|j| x[bi * h + i][bj * h + j].clone()).collect())
        .collect()
}

fn naive_mul(a: &M, b: &M) -> M {
    let n = a.len();
    let mut c = zeros(n);
    for i in 0..n {
        for j in 0..n {
            let mut acc = FpVar::zero();
            for k in 0..n {
                acc += &a[i][k] * &b[k][j]; // 1 constraint per product
            }
            c[i][j] = acc;
        }
    }
    c
}

fn strassen_mul(a: &M, b: &M) -> M {
    let n = a.len();
    if n == 1 {
        return vec![vec![&a[0][0] * &b[0][0]]];
    }
    let h = n / 2;
    let (a11, a12, a21, a22) = (
        block(a, 0, 0, h),
        block(a, 0, 1, h),
        block(a, 1, 0, h),
        block(a, 1, 1, h),
    );
    let (b11, b12, b21, b22) = (
        block(b, 0, 0, h),
        block(b, 0, 1, h),
        block(b, 1, 0, h),
        block(b, 1, 1, h),
    );
    let m1 = strassen_mul(&madd(&a11, &a22), &madd(&b11, &b22));
    let m2 = strassen_mul(&madd(&a21, &a22), &b11);
    let m3 = strassen_mul(&a11, &msub(&b12, &b22));
    let m4 = strassen_mul(&a22, &msub(&b21, &b11));
    let m5 = strassen_mul(&madd(&a11, &a12), &b22);
    let m6 = strassen_mul(&msub(&a21, &a11), &madd(&b11, &b12));
    let m7 = strassen_mul(&msub(&a12, &a22), &madd(&b21, &b22));
    let c11 = madd(&msub(&madd(&m1, &m4), &m5), &m7);
    let c12 = madd(&m3, &m5);
    let c21 = madd(&m2, &m4);
    let c22 = madd(&madd(&msub(&m1, &m2), &m3), &m6);
    let mut c = zeros(n);
    for i in 0..h {
        for j in 0..h {
            c[i][j] = c11[i][j].clone();
            c[i][j + h] = c12[i][j].clone();
            c[i + h][j] = c21[i][j].clone();
            c[i + h][j + h] = c22[i][j].clone();
        }
    }
    c
}

/// coefficient (sign, negexp) -> field constant sign / 2^negexp
fn dps_const(sign: i8, negexp: u8) -> Fr {
    let half = Fr::from(2u64).inverse().unwrap();
    let mut v = Fr::one();
    for _ in 0..negexp {
        v *= half;
    }
    if sign < 0 {
        -v
    } else {
        v
    }
}

fn materialize(x: &FpVar<Fr>) -> FpVar<Fr> {
    let cs = x.cs();
    let v = FpVar::new_witness(cs, || x.value()).unwrap();
    v.enforce_equal(x).unwrap();
    v
}

fn mat_m(x: M, on: bool) -> M {
    if !on {
        return x;
    }
    x.into_iter()
        .map(|row| row.into_iter().map(|e| materialize(&e)).collect())
        .collect()
}

fn rank48_mul(a: &M, b: &M, depth: usize, matlv: usize) -> M {
    let n = a.len();
    if n == 1 {
        return vec![vec![&a[0][0] * &b[0][0]]];
    }
    let h = n / 4;
    // 16 blocks each, row-major vec(A), vec(B)
    let ab: Vec<M> = (0..16).map(|x| block(a, x / 4, x % 4, h)).collect();
    let bb: Vec<M> = (0..16).map(|y| block(b, y / 4, y % 4, h)).collect();
    let mut prods: Vec<M> = Vec::with_capacity(48);
    for t in 0..48 {
        let mut la = zeros(h);
        let mut rb = zeros(h);
        for x in 0..16 {
            let (s, e) = coeffs::DPS_L[t][x];
            if s != 0 {
                let c = dps_const(s, e);
                for i in 0..h {
                    for j in 0..h {
                        la[i][j] += &ab[x][i][j] * c; // constant: no constraint
                    }
                }
            }
            let (s, e) = coeffs::DPS_R[t][x];
            if s != 0 {
                let c = dps_const(s, e);
                for i in 0..h {
                    for j in 0..h {
                        rb[i][j] += &bb[x][i][j] * c;
                    }
                }
            }
        }
        let on = depth <= matlv;
        prods.push(rank48_mul(&mat_m(la, on), &mat_m(rb, on), depth + 1, matlv));
    }
    let mut c = zeros(n);
    for t in 0..48 {
        for z in 0..16 {
            let (s, e) = coeffs::DPS_P[t][z];
            if s != 0 {
                let cc = dps_const(s, e);
                let (zi, zj) = (z / 4, z % 4);
                for i in 0..h {
                    for j in 0..h {
                        let cur = c[zi * h + i][zj * h + j].clone();
                        c[zi * h + i][zj * h + j] = cur + &prods[t][i][j] * cc;
                    }
                }
            }
        }
    }
    mat_m(c, depth <= matlv)
}

#[derive(Clone)]
struct MatMulCircuit {
    n: usize,
    matlv: usize,
    scheme: String,
    a: Vec<Vec<Fr>>,
    b: Vec<Vec<Fr>>,
    c: Vec<Vec<Fr>>, // public
}

impl ConstraintSynthesizer<Fr> for MatMulCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        let n = self.n;
        // public output first (input allocation order = verifier order)
        let mut cpub = Vec::with_capacity(n * n);
        for i in 0..n {
            for j in 0..n {
                cpub.push(FpVar::new_input(cs.clone(), || Ok(self.c[i][j]))?);
            }
        }
        let mut av = zeros(n);
        let mut bv = zeros(n);
        for i in 0..n {
            for j in 0..n {
                av[i][j] = FpVar::new_witness(cs.clone(), || Ok(self.a[i][j]))?;
                bv[i][j] = FpVar::new_witness(cs.clone(), || Ok(self.b[i][j]))?;
            }
        }
        let cv = match self.scheme.as_str() {
            "naive" => naive_mul(&av, &bv),
            "strassen" => strassen_mul(&av, &bv),
            "rank48" => rank48_mul(&av, &bv, 1, self.matlv),
            other => panic!("unknown scheme {other}"),
        };
        for i in 0..n {
            for j in 0..n {
                cv[i][j].enforce_equal(&cpub[i * n + j])?;
            }
        }
        Ok(())
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args[1].parse().unwrap();
    let scheme = args[2].clone();
    let prove = args.iter().any(|a| a == "--prove");
    let matlv: usize = args
        .iter()
        .position(|a| a == "--matlv")
        .and_then(|i| args.get(i + 1))
        .and_then(|v| v.parse().ok())
        .unwrap_or(0);

    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(42);
    let a: Vec<Vec<Fr>> = (0..n)
        .map(|_| (0..n).map(|_| Fr::rand(&mut rng)).collect())
        .collect();
    let b: Vec<Vec<Fr>> = (0..n)
        .map(|_| (0..n).map(|_| Fr::rand(&mut rng)).collect())
        .collect();
    // ground truth C = A*B, computed naively outside the circuit
    let mut c = vec![vec![Fr::zero(); n]; n];
    for i in 0..n {
        for j in 0..n {
            let mut s = Fr::zero();
            for k in 0..n {
                s += a[i][k] * b[k][j];
            }
            c[i][j] = s;
        }
    }
    let circuit = MatMulCircuit { n, matlv, scheme: scheme.clone(), a, b, c: c.clone() };

    // constraint count (cheap, no crypto)
    let cs = ConstraintSystem::<Fr>::new_ref();
    circuit.clone().generate_constraints(cs.clone()).unwrap();
    assert!(cs.is_satisfied().unwrap(), "circuit UNSATISFIED — gadget bug");
    let m = cs.num_constraints();
    let eq = n * n;
    println!(
        "n={n} scheme={scheme} matlv={matlv}: constraints {m} (mults {} + {} other rows)",
        m - eq, eq
    );

    if prove {
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(7);
        let t0 = Instant::now();
        let (pk, vk) =
            ark_groth16::Groth16::<Bn254>::circuit_specific_setup(circuit.clone(), &mut rng)
                .unwrap();
        let t_setup = t0.elapsed();
        let t1 = Instant::now();
        let proof = ark_groth16::Groth16::<Bn254>::prove(&pk, circuit, &mut rng).unwrap();
        let t_prove = t1.elapsed();
        let public: Vec<Fr> = c.into_iter().flatten().collect();
        let t2 = Instant::now();
        let ok = ark_groth16::Groth16::<Bn254>::verify(&vk, &public, &proof).unwrap();
        let t_verify = t2.elapsed();
        println!(
            "groth16: setup {:.2?}  prove {:.2?}  verify {:.2?}  valid {ok}",
            t_setup, t_prove, t_verify
        );
        assert!(ok);
    }
}
