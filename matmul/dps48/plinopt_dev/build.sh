#!/bin/zsh
# Build PLinOpt programs on this Mac (Apple clang + libomp + the LinBox stack in matmul/dps48/stack).
#   build.sh [target ...]      default: optimizer SLPchecker compacter transpozer matrix-transpose
# Binaries go to the checkout's bin/ (untracked), like upstream's Makefile.
set -e
PL=/Users/greg/projects/logic/matmul/dps48/plinopt
export PKG_CONFIG_PATH=/Users/greg/projects/logic/matmul/dps48/stack/lib/pkgconfig
FL="-O3 -ffast-math -std=gnu++17 -Wno-invalid-specialization -Xpreprocessor -fopenmp -I/opt/homebrew/opt/libomp/include -D RANDOM_TIES"
CF="$(pkg-config linbox --cflags)"
LIBS="$(pkg-config linbox --libs | sed 's/-liml//;s/-lfplll//;s/-lflint//') -L/opt/homebrew/opt/libomp/lib -lomp"
targets=("$@"); [[ ${#targets} -eq 0 ]] && targets=(optimizer SLPchecker compacter transpozer matrix-transpose)
mkdir -p $PL/bin
for t in $targets; do
  src=$PL/src/$t.cpp
  if [[ $t == MMchecker ]]; then   # size_t vs uint64_t pow ambiguity on macOS (see memory note)
    sed 's/pow(r,e)/pow(r,(uint64_t)e)/' $src > /tmp/claude-501/MMchecker_mac.cpp; src=/tmp/claude-501/MMchecker_mac.cpp
  fi
  c++ ${=FL} -I$PL/include/ ${=CF} $src ${=LIBS} -o $PL/bin/$t 2> /tmp/claude-501/build_$t.log || { echo "BUILD FAILED: $t"; grep -m3 error /tmp/claude-501/build_$t.log; exit 1; }
  echo "built bin/$t"
done
