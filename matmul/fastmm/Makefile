# fast matrix multiplication benchmark (Apple silicon, Accelerate)
build/bench_fmm: bench_fmm.c bench_impl.h build/kernels.h
	clang -O3 -mcpu=apple-m4 -Wall -Wno-unused-function -Ibuild bench_fmm.c -framework Accelerate -o $@

build/kernels.h: gen_kernels.py ../dps48/cand48/p005_201n_L.slp ../dps48/cand48/p005_201n_R.slp ../dps48/cand48/p005_201n_P.slp
	mkdir -p build && python3 gen_kernels.py $@
