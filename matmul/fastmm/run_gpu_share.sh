#!/bin/zsh
# The GPU as a second engine for a level's products (f32): the library's picks against the same
# levels with the products shared between the SME units and the GPU (leaves GM, GkM), the classical
# product shared (K levels), and the GPU alone; exact errors (FMM_EXACT).  2026-11-14.
#   ./run_gpu_share.sh > results/gpu_share_2026-11-14.txt
cd ${0:A:h}
make build/bench_fmm_gpu build/gpu_share build/gpu_gemm >/dev/null || exit 1
echo "# GPU-shared leaves; $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string); logic $(git rev-parse --short HEAD)"
echo "## the probe: r products of one shape, streams alone, the GPU alone, both"
for sh in "4608 2304 4608 20" "2304 1152 2304 40" "1536 768 768 160" "1152 576 1152 40" "768 384 384 320"; do
  ./build/gpu_share ${=sh} 6 4 2>&1 | tail -1
done
echo "## n=3456 f32"
./build/gpu_gemm 3456 5 graph | head -1
FMM_EXACT=1 ./build/bench_fmm_gpu -n 3456 -t f -r 7 -m classical,plan=R363/G6,plan=K16/GM,plan=K32/G6M,plan=K64/G6M,plan=R363/G6M,plan=R363/GM,plan=D48/G6M,plan=R336/G6M
echo "## n=6912 f32"
./build/gpu_gemm 6912 5 graph | head -1
FMM_EXACT=1 ./build/bench_fmm_gpu -n 6912 -t f -r 5 -m classical,plan=R363+4/R633/G6,plan=K32/GM,plan=K64/G6M,plan=R363/G6M,plan=R363/GM,plan=R336/GM,plan=D48/G6M,plan=D48/GM,plan=R363+4/R633/G6M,plan=R363+4/D48/G6M
echo "## n=13824 f32"
./build/gpu_gemm 13824 3 graph | head -1
FMM_EXACT=1 ./build/bench_fmm_gpu -n 13824 -t f -r 5 -m classical,plan=R336+2/R363/G6,plan=K32/GM,plan=R363/GM,plan=R363/G6M,plan=R336/GM,plan=D48/GM,plan=R363+3/R336/G6M,plan=R363+4/R336/G6M,plan=R336+4/R363/G6M,plan=R363+4/R363/G6M,plan=R363+4/D48/G6M
echo "# done $(date '+%H:%M')"
