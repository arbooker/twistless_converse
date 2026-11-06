#!/usr/bin/env bash
#SBATCH --job-name=n97-prepare
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=8G
#SBATCH --time=12:00:00

set -euo pipefail
ROOT=${N97_BUNDLE_ROOT:?submit through submit_n97.sh}
"$ROOT/00_check.sh"
"$ROOT/01_prepare_matrix.sh"
