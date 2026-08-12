# satsuma-iter+kissat — SAT Competition 2026 main-track winner (M. Anders et al.)
# Builds the satsuma-iter-kissat submission from the official competition tarball:
#   satsuma  (symmetry-breaking preprocessor, dejavu-based; emits binary-SR proof)
#   kissat   (CDCL solver; appends its refutation to the same proof file)
#   dsr-trim (SR proof checker: verifies the COMPOSED proof against the ORIGINAL
#             CNF -> end-to-end certified UNSAT), lsr-check, compress
# Build context must contain anders.tar.xz (see build.sh; archived at
# ~/projects/sat_benchmarks/archive/anders_satcomp2026.tar.xz, source
# https://satcompetition.github.io/2026/downloads/solvers/anders.tar.xz).
FROM ubuntu:24.04
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
      build-essential make xz-utils ca-certificates && rm -rf /var/lib/apt/lists/*
COPY anders.tar.xz /build/
RUN cd /build && tar xf anders.tar.xz \
    && mv anders/satsuma-iter-kissat/src /src && rm -rf /build
WORKDIR /src
# kissat (C)
RUN cd solver/kissat && rm -f makefile src/makefile && CC=gcc ./configure --competition \
    && make -j4 kissat && cp build/kissat /src/kissat
# satsuma (C++20 + vendored cliquer; dejavu is header-only inside)
RUN cd solver/satsuma-dev && make -j4 && cp satsuma /src/satsuma
# dsr-trim ships PREBUILT x86-64 binaries in bin/ — force a native rebuild
# (make alone says "nothing to be done" and the stale ELF dies under Rosetta).
RUN cd dsr-trim && rm -f bin/* && make -B -j4 && ./bin/dsr-trim 2>&1 | head -1 || true
CMD ["/bin/bash"]
