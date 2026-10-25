# fast matrix multiplication benchmark (Apple silicon, Accelerate)
all: build/bench_fmm build/libfmm.a build/test_fmm build/probe_threads build/neon_test build/probe_overlap

build/bench_fmm: bench_fmm.c bench_impl.h fmm.c fmm_impl.h fmm.h neon_gemm.h build/kernels.h
	clang -O3 -mcpu=apple-m4 -Wall -Wno-unused-function -Ibuild bench_fmm.c -framework Accelerate -o $@

# the kernels: dps48 from the accurate DPS program (4x4x4_48_accurate), op-by-op lists from ours (201)
build/kernels.h: gen_kernels.py ../dps48/plinopt/data/4x4x4_48_accurate_L.slp ../dps48/plinopt/data/4x4x4_48_accurate_R.slp ../dps48/plinopt/data/4x4x4_48_accurate_P.slp ../dps48/cand48/p005_201n_L.slp ../dps48/cand48/p005_201n_R.slp ../dps48/cand48/p005_201n_P.slp
	mkdir -p build && python3 gen_kernels.py $@

# the same with every use of a scaled value as a fused multiply-add (x * 0.5 + y -> one FMLA);
# -ffp-contract=fast alone fuses nothing here: each halving feeds 4-5 additions
build/bench_fmm_fma: bench_fmm.c bench_impl.h fmm.c fmm_impl.h fmm.h neon_gemm.h build/fma/kernels.h
	clang -O3 -mcpu=apple-m4 -Wall -Wno-unused-function -Ibuild/fma bench_fmm.c -framework Accelerate -o $@

build/fma/kernels.h: gen_kernels.py ../dps48/cand48/p005_201n_L.slp ../dps48/cand48/p005_201n_R.slp ../dps48/cand48/p005_201n_P.slp
	mkdir -p build/fma && python3 gen_kernels.py $@ --fma --dps48 ../dps48/cand48/p005_201n

# how much of the machine Accelerate's GEMM uses: SME streams, NEON peak, both at once
build/probe_threads: probe_threads.c
	mkdir -p build && clang -O3 -mcpu=apple-m4 -Wall probe_threads.c -framework Accelerate -o $@

# the NEON GEMM of neon_gemm.h: correctness, one core, several cores, beside SME streams
build/neon_test: neon_test.c neon_gemm.h
	mkdir -p build && clang -O3 -mcpu=apple-m4 -Wall neon_test.c -framework Accelerate -o $@

# a fused pass beside SME GEMM streams: how much each slows the other
build/probe_overlap: probe_overlap.c build/kernels.h
	mkdir -p build && clang -O3 -mcpu=apple-m4 -Wall -Wno-unused-function -Ibuild probe_overlap.c -framework Accelerate -o $@

# the library: fmm.h, link with -framework Accelerate
build/libfmm.a: fmm.c fmm_impl.h fmm.h neon_gemm.h build/kernels.h
	mkdir -p build && clang -O3 -mcpu=apple-m4 -Wall -Wno-unused-function -Ibuild -c fmm.c -o build/fmm.o && ar rcs $@ build/fmm.o

# the library's entry points against Accelerate (FMM_CALIB_DIR=results build/test_fmm)
build/test_fmm: test_fmm.c fmm.h build/libfmm.a
	clang -O3 -mcpu=apple-m4 -Wall test_fmm.c build/libfmm.a -framework Accelerate -o $@

# the same with dps48's fused kernels from the original rational rank-48 scheme (315 operations)
build/bench_fmm_orig: bench_fmm.c bench_impl.h fmm.c fmm_impl.h fmm.h neon_gemm.h build/orig/kernels.h
	clang -O3 -mcpu=apple-m4 -Wall -Wno-unused-function -Ibuild/orig bench_fmm.c -framework Accelerate -o $@

build/orig/kernels.h: gen_kernels.py ../dps48/plinopt/data/4x4x4_48_rational_L.slp ../dps48/plinopt/data/4x4x4_48_rational_R.slp ../dps48/plinopt/data/4x4x4_48_rational_P.slp
	mkdir -p build/orig && python3 gen_kernels.py $@ --dps48 ../dps48/plinopt/data/4x4x4_48_rational

# the same with dps48's fused kernels from our 201-operation program
build/bench_fmm_201: bench_fmm.c bench_impl.h fmm.c fmm_impl.h fmm.h neon_gemm.h build/201/kernels.h
	clang -O3 -mcpu=apple-m4 -Wall -Wno-unused-function -Ibuild/201 bench_fmm.c -framework Accelerate -o $@

build/201/kernels.h: gen_kernels.py ../dps48/cand48/p005_201n_L.slp ../dps48/cand48/p005_201n_R.slp ../dps48/cand48/p005_201n_P.slp
	mkdir -p build/201 && python3 gen_kernels.py $@ --dps48 ../dps48/cand48/p005_201n
