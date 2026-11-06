#!/usr/bin/env bash
#SBATCH --job-name=n97-finish
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=64
#SBATCH --hint=multithread
#SBATCH --mem=350G
#SBATCH --time=14-00:00:00
#SBATCH --no-requeue

set -euo pipefail
ROOT=${N97_BUNDLE_ROOT:?submit through submit_n97.sh}
export OMP_NUM_THREADS=${SLURM_CPUS_PER_TASK:-64}
export OMP_PROC_BIND=spread
export OMP_PLACES=cores
"$ROOT/00_check.sh"
if [ ! -f "${N97_WORK_ROOT:?}/certificate/AUGMENTED_CERTIFICATE_COMPLETE" ]; then
    "$ROOT/04_check_candidates.sh"
fi
exec "$ROOT/05_finish.sh"
