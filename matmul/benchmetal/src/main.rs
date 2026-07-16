//! benchmetal — batched 4x4 BabyBear tile witness-generation on the
//! Apple GPU (Metal compute), naive vs 284-op rank-48 kernels
//! (tiles.metal is generated from the same SLPs by gen_msl.py —
//! sixth codegen target). Gate: every GPU output must equal the CPU
//! Montgomery reference bit-for-bit before timing counts.
use metal::*;
use objc::rc::autoreleasepool;
use std::time::Instant;

const P: u32 = 0x7800_0001;
const P64: u64 = P as u64;
const NP: u32 = 0x77FF_FFFF; // -p^{-1} mod 2^32, asserted in main
const SRC: &str = include_str!("tiles.metal");

fn mont_mul(a: u32, b: u32) -> u32 {
    let t = a as u64 * b as u64;
    let m = (t as u32).wrapping_mul(NP);
    let t2 = ((t + m as u64 * P64) >> 32) as u32;
    if t2 >= P { t2 - P } else { t2 }
}
fn badd(a: u32, b: u32) -> u32 {
    let s = a + b;
    if s >= P { s - P } else { s }
}

fn main() {
    // np sanity + R2 for domain conversion in the reference
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
        let pso_naive = pso("tile_naive");
        let pso_unroll = pso("tile_naive_unrolled");
        let pso_284 = pso("tile_284");

        for log_t in [20usize, 22] {
            let t_tiles = 1usize << log_t;
            // SoA host data (values already in Montgomery domain --
            // domain choice is irrelevant to the benchmark, all paths
            // use the same representation)
            let mut rng = 0x243f_6a88_85a3_08d3u64;
            let mut next = move || {
                rng ^= rng << 13;
                rng ^= rng >> 7;
                rng ^= rng << 17;
                (rng % P64) as u32
            };
            let a_h: Vec<u32> = (0..16 * t_tiles).map(|_| next()).collect();
            let b_h: Vec<u32> = (0..16 * t_tiles).map(|_| next()).collect();
            // CPU reference (first 4096 tiles suffice for the gate at
            // full strength; full-range check on a stride)
            let expect = |tid: usize| -> [u32; 16] {
                let mut c = [0u32; 16];
                for i in 0..4 {
                    for j in 0..4 {
                        let mut s = 0u32;
                        for k in 0..4 {
                            s = badd(
                                s,
                                mont_mul(
                                    a_h[(i * 4 + k) * t_tiles + tid],
                                    b_h[(k * 4 + j) * t_tiles + tid],
                                ),
                            );
                        }
                        c[i * 4 + j] = s;
                    }
                }
                c
            };
            let opts = MTLResourceOptions::StorageModeShared;
            let buf = |v: &[u32]| {
                device.new_buffer_with_data(
                    v.as_ptr().cast(),
                    (v.len() * 4) as u64,
                    opts,
                )
            };
            let a_b = buf(&a_h);
            let b_b = buf(&b_h);
            let c_h = vec![0u32; 16 * t_tiles];
            let c_b = buf(&c_h);
            let tg = MTLSize { width: 256, height: 1, depth: 1 };
            let grid = MTLSize { width: t_tiles as u64, height: 1, depth: 1 };
            let t32 = t_tiles as u32;

            let dispatch = |pso: &ComputePipelineState| {
                let cmd = queue.new_command_buffer();
                let enc = cmd.new_compute_command_encoder();
                enc.set_compute_pipeline_state(pso);
                enc.set_buffer(0, Some(&a_b), 0);
                enc.set_buffer(1, Some(&b_b), 0);
                enc.set_buffer(2, Some(&c_b), 0);
                enc.set_bytes(3, 4, (&t32 as *const u32).cast());
                enc.dispatch_threads(grid, tg);
                enc.end_encoding();
                cmd.commit();
                cmd.wait_until_completed();
            };

            for (name, pso) in [
                ("naive", &pso_naive),
                ("naive-unrolled", &pso_unroll),
                ("rank48-284", &pso_284),
            ] {
                dispatch(pso); // includes the gate run
                // gate: exact equality vs CPU reference on a stride
                let c_out: &[u32] = unsafe {
                    std::slice::from_raw_parts(c_b.contents().cast(), 16 * t_tiles)
                };
                let step = (t_tiles / 4096).max(1);
                for tid in (0..t_tiles).step_by(step) {
                    let e = expect(tid);
                    for z in 0..16 {
                        assert_eq!(
                            c_out[z * t_tiles + tid],
                            e[z],
                            "GPU {name} mismatch tile {tid} out {z}"
                        );
                    }
                }
                // timing: 10 dispatches
                let reps = 10;
                let t0 = Instant::now();
                for _ in 0..reps {
                    dispatch(pso);
                }
                let ns = t0.elapsed().as_nanos() as f64 / reps as f64 / t_tiles as f64;
                let gt = 1e9 / ns / 1e9;
                println!(
                    "2^{log_t} tiles  {name:<11} {ns:6.2} ns/tile  ({gt:.2} Gtiles/s)  [gated vs CPU]"
                );
            }
        }
        println!();
        println!("CPU reference points (bench_bb): scalar naive 53.5 / 284 177.4 ns/tile;");
        println!("                         4-lane NEON naive 20.0 / 284 76.8 ns/tile");
    });
}
