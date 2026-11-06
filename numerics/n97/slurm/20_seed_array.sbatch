#!/usr/bin/env bash
#SBATCH --job-name=n97-bw
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=48
#SBATCH --hint=multithread
#SBATCH --mem=170G
#SBATCH --time=14-00:00:00
#SBATCH --no-requeue

set -euo pipefail
ROOT=${N97_BUNDLE_ROOT:?submit through submit_n97.sh}
. "$ROOT/settings.sh"
"$ROOT/00_check.sh"

: "${SLURM_ARRAY_TASK_ID:?This script must be submitted as an array job}"
offset=${N97_SEED_INDEX_OFFSET:-0}
case $offset in *[!0-9]*|'') echo "Invalid seed offset" >&2; exit 1 ;; esac
index=$((offset + SLURM_ARRAY_TASK_ID))
seed=$((SEED_BASE + SEED_STRIDE * index))

export BWC_LINGEN_THREADS=${BWC_LINGEN_THREADS:-4x6}
export N97_KRYLOV_STREAMS=${N97_KRYLOV_STREAMS:-8}
export N97_THREADS_PER_CORE=${N97_THREADS_PER_CORE:-2}
export N97_AUTO_COMPACT=1
exec "$ROOT/02_run_seed_lanes.sh" "$seed"
