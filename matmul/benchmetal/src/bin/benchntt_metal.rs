//! benchntt_metal — BabyBear radix-2 NTT on the Apple GPU (Metal),
//! the GPU column for the Appendix B transform table. Gates: GPU
//! forward AND inverse must match the CPU implementation (identical
//! Montgomery semantics) bit-for-bit at 2^14 and 2^18, plus a GPU
//! round-trip identity at 2^20, before any timing. One compute
//! encoder per butterfly stage (Metal orders encoders in a command
//! buffer); twiddle tables precomputed host-side per stage.
use metal::*;
use objc::rc::autoreleasepool;
use std::time::Instant;

const P: u32 = 0x7800_0001;
const P64: u64 = P as u64;
const NP: u32 = 0x77FF_FFFF;
const R2: u32 = ((1u128 << 64) % P as u128) as u32;
const SRC: &str = include_str!("../ntt.metal");

fn mmul(a: u32, b: u32) -> u32 {
    let t = a as u64 * b as u64;
    let m = (t as u32).wrapping_mul(NP);
    let t2 = ((t + m as u64 * P64) >> 32) as u32;
    if t2 >= P { t2 - P } else { t2 }
}
fn badd(a: u32, b: u32) -> u32 {
    let s = a + b;
    if s >= P { s - P } else { s }
}
fn bsub(a: u32, b: u32) -> u32 {
    if a >= b { a - b } else { a + P - b }
}
fn to_m(x: u32) -> u32 {
    mmul(x, R2)
}
fn mpow(mut b: u32, mut e: u64) -> u32 {
    let mut r = to_m(1);
    while e > 0 {
        if e & 1 == 1 {
            r = mmul(r, b);
        }
        b = mmul(b, b);
        e >>= 1;
    }
    r
}
fn minv(a: u32) -> u32 {
    mpow(a, P64 - 2)
}
fn root_of_order(n: u64) -> u32 {
    let w = mpow(to_m(31), (P64 - 1) / n);
    assert_eq!(mpow(w, n), to_m(1));
    assert_eq!(mpow(w, n / 2), to_m(P - 1));
    w
}
fn cpu_ntt(a: &mut [u32], root: u32) {
    let n = a.len();
    let lg = n.trailing_zeros();
    for i in 0..n {
        let j = (i as u32).reverse_bits() >> (32 - lg);
        if (j as usize) > i {
            a.swap(i, j as usize);
        }
    }
    let mut len = 2;
    while len <= n {
        let w_len = mpow(root, (n / len) as u64);
        for start in (0..n).step_by(len) {
            let mut w = to_m(1);
            for k in 0..len / 2 {
                let u = a[start + k];
                let v = mmul(a[start + k + len / 2], w);
                a[start + k] = badd(u, v);
                a[start + k + len / 2] = bsub(u, v);
                w = mmul(w, w_len);
            }
        }
        len <<= 1;
    }
}

/// per-stage twiddles, concatenated: stage s (len = 2^{s+1}) has
/// 2^s entries w_len^0..; offsets[s] indexes into the table
fn twiddles(n: usize, root: u32) -> (Vec<u32>, Vec<u32>) {
    let mut tw = Vec::with_capacity(n - 1);
    let mut offs = Vec::new();
    let mut len = 2usize;
    while len <= n {
        offs.push(tw.len() as u32);
        let w_len = mpow(root, (n / len) as u64);
        let mut w = to_m(1);
        for _ in 0..len / 2 {
            tw.push(w);
            w = mmul(w, w_len);
        }
        len <<= 1;
    }
    (tw, offs)
}

fn main() {
    assert_eq!(P.wrapping_mul(NP), u32::MAX);
    autoreleasepool(|| {
        let device = Device::system_default().expect("no Metal device");
        println!("GPU: {}", device.name());
        let queue = device.new_command_queue();
        let lib = device
            .new_library_with_source(SRC, &CompileOptions::new())
            .expect("MSL compile failed");
        let pso = |name: &str| {
            let f = lib.get_function(name, None).unwrap();
            device.new_compute_pipeline_state_with_function(&f).unwrap()
        };
        let pso_rev = pso("bitrev");
        let pso_stage = pso("stage");
        let pso_scale = pso("scale");
        let opts = MTLResourceOptions::StorageModeShared;
        let tg = MTLSize { width: 256, height: 1, depth: 1 };

        // encode one full NTT (bitrev from src into work, then stages)
        let run_ntt = |src_b: &Buffer, work_b: &Buffer, tw_b: &Buffer,
                       offs: &[u32], lg: u32, scale_c: Option<u32>, reps: usize| {
            let n = 1u64 << lg;
            let cmd = queue.new_command_buffer();
            for _ in 0..reps {
                let enc = cmd.new_compute_command_encoder();
                enc.set_compute_pipeline_state(&pso_rev);
                enc.set_buffer(0, Some(src_b), 0);
                enc.set_buffer(1, Some(work_b), 0);
                enc.set_bytes(2, 4, (&lg as *const u32).cast());
                enc.dispatch_threads(MTLSize { width: n, height: 1, depth: 1 }, tg);
                enc.end_encoding();
                for (s, off) in offs.iter().enumerate() {
                    let half_log = s as u32;
                    let enc = cmd.new_compute_command_encoder();
                    enc.set_compute_pipeline_state(&pso_stage);
                    enc.set_buffer(0, Some(work_b), 0);
                    enc.set_buffer(1, Some(tw_b), 0);
                    enc.set_bytes(2, 4, (&half_log as *const u32).cast());
                    enc.set_bytes(3, 4, (off as *const u32).cast());
                    enc.dispatch_threads(
                        MTLSize { width: n / 2, height: 1, depth: 1 },
                        tg,
                    );
                    enc.end_encoding();
                }
                if let Some(c) = scale_c {
                    let enc = cmd.new_compute_command_encoder();
                    enc.set_compute_pipeline_state(&pso_scale);
                    enc.set_buffer(0, Some(work_b), 0);
                    enc.set_bytes(1, 4, (&c as *const u32).cast());
                    enc.dispatch_threads(MTLSize { width: n, height: 1, depth: 1 }, tg);
                    enc.end_encoding();
                }
            }
            cmd.commit();
            cmd.wait_until_completed();
        };

        let mut rng = 0x9e37_79b9_7f4a_7c15u64;
        let mut next = move || {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            (rng % P64) as u32
        };

        // ---- gates ----
        for lg in [14u32, 18] {
            let n = 1usize << lg;
            let root = root_of_order(n as u64);
            let (tw, offs) = twiddles(n, root);
            let data: Vec<u32> = (0..n).map(|_| to_m(next())).collect();
            let src_b = device.new_buffer_with_data(
                data.as_ptr().cast(), (n * 4) as u64, opts);
            let work_b = device.new_buffer((n * 4) as u64, opts);
            let tw_b = device.new_buffer_with_data(
                tw.as_ptr().cast(), (tw.len() * 4) as u64, opts);
            run_ntt(&src_b, &work_b, &tw_b, &offs, lg, None, 1);
            let mut cpu = data.clone();
            cpu_ntt(&mut cpu, root);
            let gpu: &[u32] =
                unsafe { std::slice::from_raw_parts(work_b.contents().cast(), n) };
            assert_eq!(&cpu[..], gpu, "forward mismatch at 2^{lg}");
            // inverse gate: run inverse on the forward result
            let iroot = minv(root);
            let (itw, ioffs) = twiddles(n, iroot);
            let itw_b = device.new_buffer_with_data(
                itw.as_ptr().cast(), (itw.len() * 4) as u64, opts);
            let ninv = minv(to_m((n as u64 % P64) as u32));
            let fwd = gpu.to_vec();
            let fwd_b = device.new_buffer_with_data(
                fwd.as_ptr().cast(), (n * 4) as u64, opts);
            run_ntt(&fwd_b, &work_b, &itw_b, &ioffs, lg, Some(ninv), 1);
            let back: &[u32] =
                unsafe { std::slice::from_raw_parts(work_b.contents().cast(), n) };
            assert_eq!(&data[..], back, "round-trip mismatch at 2^{lg}");
            println!("gate: GPU forward == CPU and GPU round-trip == identity at 2^{lg}");
        }

        // ---- timing curve ----
        println!("BabyBear NTT on Apple GPU (forward, seconds; one transform per rep)");
        for lg in 14u32..=25 {
            let n = 1usize << lg;
            let root = root_of_order(n as u64);
            let (tw, offs) = twiddles(n, root);
            let data: Vec<u32> = (0..n).map(|_| to_m(next())).collect();
            let src_b = device.new_buffer_with_data(
                data.as_ptr().cast(), (n * 4) as u64, opts);
            let work_b = device.new_buffer((n * 4) as u64, opts);
            let tw_b = device.new_buffer_with_data(
                tw.as_ptr().cast(), (tw.len() * 4) as u64, opts);
            let reps = ((1usize << 24) >> lg).clamp(4, 256);
            run_ntt(&src_b, &work_b, &tw_b, &offs, lg, None, 2); // warm
            let t0 = Instant::now();
            run_ntt(&src_b, &work_b, &tw_b, &offs, lg, None, reps);
            let t = t0.elapsed().as_secs_f64() / reps as f64;
            println!("domain 2^{lg} ({n}): fwd {t:.6}");
        }
    });
}
