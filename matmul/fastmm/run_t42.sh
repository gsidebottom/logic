#!/bin/bash
# the ternary <3x3x6:42> levels (T336/T363/T633, Perminov's 3x3x6_m42_cr139, 139 additions) against
# the accurate <3x3x6:40> levels (R...) and the 4x4 level on fixed plans: speed, pass times and
# error, five (f32) or three (f64) interleaved rounds; FMM_EXACT for f32 (error against the f64
# product).  results/t42_campaign_2026-10-28.txt
cd "$(dirname "$0")" || exit 1
echo "# T42 campaign: ternary <3x3x6:42> levels vs the accurate <3x3x6:40> levels and D48, fixed plans; $(date '+%Y-%m-%d %H:%M'); $(sysctl -n machdep.cpu.brand_string)"
B=classical,plan=D48/G,plan=R336/G,plan=T336/G,plan=R363/G,plan=T363/G,plan=R633/G,plan=T633/G
echo "## n=13824 f32  $(date '+%H:%M')"
FMM_EXACT=1 ./build/bench_fmm -n 13824 -t f -r 5 -m $B,plan=R336/R363/R633/G,plan=T336/T363/T633/G,plan=R363+4/D48/G6,plan=T363+4/D48/G6,plan=R363+4/R363/G6,plan=T363+4/T363/G6 | grep -v '^#   '
echo "## n=13824 f64  $(date '+%H:%M')"
./build/bench_fmm -n 13824 -t d -r 3 -m $B,plan=R336/R363/R633/G,plan=T336/T363/T633/G,plan=SW/R363+3/R633/G6,plan=SW/T363+3/T633/G6,plan=R363+3/R633/G6,plan=T363+3/T633/G6 | grep -v '^#   '
echo "## n=6912 f32  $(date '+%H:%M')"
FMM_EXACT=1 ./build/bench_fmm -n 6912 -t f -r 5 -m $B,plan=R363+4/D48/G6,plan=T363+4/D48/G6,plan=R363+3/R633/G6,plan=T363+3/T633/G6 | grep -v '^#   '
echo "## n=6912 f64  $(date '+%H:%M')"
./build/bench_fmm -n 6912 -t d -r 5 -m $B,plan=R363+4/D48/G6,plan=T363+4/D48/G6,plan=R363+3/R633/G6,plan=T363+3/T633/G6 | grep -v '^#   '
echo "# done $(date '+%H:%M')"
