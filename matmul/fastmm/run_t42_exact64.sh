#!/bin/zsh
# The ternary trial's f64 rows (run_t42.sh) again, with the error against the exact (compensated) product:
# run_t42.sh measured f64 against Accelerate's product only.  Same plans, rounds and sizes.
# Output: results/t42_exact64_<date>.txt
cd "$(dirname "$0")" || exit 1
export FMM_EXACT=1 FMM_REFCACHE=${FMM_REFCACHE:-/private/tmp/claude-501/-Users-greg-projects-logic/3d45768d-4e94-4613-987d-3cadfd01d9af/scratchpad/refcache}
mkdir -p "$FMM_REFCACHE"
echo "# T42 f64 rows against the exact product; $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string); logic $(git rev-parse --short HEAD)"
echo "# top CPU users before the run:"; ps -axo pcpu,pid,etime,comm -r | head -6 | sed 's/^/#   /'
B=classical,plan=D48/G,plan=R336/G,plan=T336/G,plan=R363/G,plan=T363/G,plan=R633/G,plan=T633/G
echo "## n=13824 f64  $(date '+%H:%M')"
./build/bench_fmm -n 13824 -t d -r 3 -m $B,plan=R336/R363/R633/G,plan=T336/T363/T633/G,plan=SW/R363+3/R633/G6,plan=SW/T363+3/T633/G6,plan=R363+3/R633/G6,plan=T363+3/T633/G6 | grep -v '^#   '
echo "## n=6912 f64  $(date '+%H:%M')"
./build/bench_fmm -n 6912 -t d -r 5 -m $B,plan=R363+4/D48/G6,plan=T363+4/D48/G6,plan=R363+3/R633/G6,plan=T363+3/T633/G6 | grep -v '^#   '
echo "# done $(date '+%H:%M')"
