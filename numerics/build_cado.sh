#!/usr/bin/env bash
set -euo pipefail
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
SOURCE="$ROOT/third_party/cado-nfs"
BUILD=${CADO_BUILD_DIR:-$ROOT/build/cado}
PIN=e3f70ce77f6ce332a6a95092eedf04474165db08
[ "$(git -C "$SOURCE" rev-parse HEAD)" = "$PIN" ] || {
    echo 'Initialize the pinned CADO submodule first: git submodule update --init' >&2; exit 1;
}
ARCH_FLAGS=${ARCH_FLAGS:--march=native}
# Each seed is a shared-memory calculation; Slurm distributes independent seeds.
# No MPI or dynamically loaded matrix backend is needed.
env MPI=0 cmake -S "$SOURCE" -B "$BUILD" \
    -DCMAKE_BUILD_TYPE=Release -DENABLE_SHARED=OFF \
    "-DCMAKE_C_FLAGS=-O3 $ARCH_FLAGS" "-DCMAKE_CXX_FLAGS=-O3 $ARCH_FLAGS" \
    -DBWC_GFP_ARITHMETIC_BACKENDS= "$@"
cmake --build "$BUILD" --target bwc_full_gf2 --parallel "${BUILD_JOBS:-1}"
printf '\nSet CADO_BWC_DIR=%s/linalg/bwc before running the N=97 scripts.\n' "$BUILD"
