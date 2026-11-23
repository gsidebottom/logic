#!/bin/zsh
# The Rust passes against the C library's calibrated pass entries (rust/src/bin/passcal.rs), for each pass driver
# of exec::run_par: iter (a parallel iterator over the chunks: the driver until 2026-11-22), spawn (one task per
# chunk, spawned at once: the default since), gcd (GCD's dispatch_apply, as the C library), and spawn on a pool of
# ten threads (the performance cores).  Entries whose largest block has at most 1200^2 elements, both precisions;
# each Rust entry measured as the Rust calibration measures it.  The C values are the calibration's
# (results/calib5_f32.txt, calib5_f64.txt), measured in the campaign of the same evening.
# Build: (cd rust && cargo build --release).  Output: results/rust_small_passes_2026-11-22.txt
cd "$(dirname "$0")" || exit 1
echo "# Rust passes against the C library's calibrated passes, by pass driver; $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string); logic $(git rev-parse --short HEAD) + working tree"
echo "# top CPU users before the run:"; ps -axo pcpu,pid,etime,comm -r | head -6 | sed 's/^/#   /'
for t in f32 f64; do
  for d in iter spawn gcd; do
    echo "## driver $d, $t  $(date '+%H:%M')"
    FMM_PASS_DISPATCH=$d timeout 600 ./rust/target/release/passcal results/calib5_$t.txt
  done
  echo "## driver spawn, ten threads, $t  $(date '+%H:%M')"
  FMM_THREADS=10 FMM_PASS_DISPATCH=spawn timeout 600 ./rust/target/release/passcal results/calib5_$t.txt
done
echo "# top CPU users after the run:"; ps -axo pcpu,pid,etime,comm -r | head -6 | sed 's/^/#   /'
echo "# done $(date '+%H:%M')"
