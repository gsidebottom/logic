# fast matrix multiplication benchmark (Apple silicon, Accelerate)
build/bench_fmm: bench_fmm.c bench_impl.h build/kernels.h
	clang -O3 -mcpu=apple-m4 -Wall -Wno-unused-function -Ibuild bench_fmm.c -framework Accelerate -o $@

build/kernels.h: gen_kernels.py ../dps48/cand48/p005_201n_L.slp ../dps48/cand48/p005_201n_R.slp ../dps48/cand48/p005_201n_P.slp
	mkdir -p build && python3 gen_kernels.py $@

# the same with every use of a scaled value as a fused multiply-add (x * 0.5 + y -> one FMLA);
# -ffp-contract=fast alone fuses nothing here: each halving feeds 4-5 additions
build/bench_fmm_fma: bench_fmm.c bench_impl.h build/fma/kernels.h
	clang -O3 -mcpu=apple-m4 -Wall -Wno-unused-function -Ibuild/fma bench_fmm.c -framework Accelerate -o $@

build/fma/kernels.h: gen_kernels.py ../dps48/cand48/p005_201n_L.slp ../dps48/cand48/p005_201n_R.slp ../dps48/cand48/p005_201n_P.slp
	mkdir -p build/fma && python3 gen_kernels.py $@ --fma
