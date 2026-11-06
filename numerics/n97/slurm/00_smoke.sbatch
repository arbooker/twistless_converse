#!/usr/bin/env bash
#SBATCH --job-name=n97-smoke
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=48
#SBATCH --hint=multithread
#SBATCH --mem=16G
#SBATCH --time=00:30:00

set -euo pipefail
ROOT=${N97_BUNDLE_ROOT:?submit through submit_n97.sh}
export SMOKE_THREADS=${SMOKE_THREADS:-2x3}
export SMOKE_WIDTH=${SMOKE_WIDTH:-512}
export SMOKE_LANE_PARALLEL=${SMOKE_LANE_PARALLEL:-1}
"$ROOT/03_smoke_test.sh"
