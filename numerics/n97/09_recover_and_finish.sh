#!/usr/bin/env bash
# One-node recovery + exact union certificate + projected finisher.
set -euo pipefail
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
. "$ROOT/common.sh"
require_work_root
: "${SLURM_JOB_ID:?Run on a compute node}"
case ${1:-} in
    '') [ "$#" -eq 0 ] || exit 1; check_only=0 ;;
    --check-only) [ "$#" -eq 1 ] || exit 1; check_only=1 ;;
    *) echo "Usage: $0 [--check-only]" >&2; exit 1 ;;
esac
mkdir -p "$WORK_ROOT/recovery"
exec 7>"$WORK_ROOT/recovery/pipeline.lock"
flock -n 7 || { echo "Another recovery pipeline is active" >&2; exit 1; }
if [ ! -f "$WORK_ROOT/certificate/AUGMENTED_CERTIFICATE_COMPLETE" ]; then
    for ((i=0; i<DEFAULT_SEED_COUNT; i++)); do
        seed=$((SEED_BASE+SEED_STRIDE*i))
        bash "$ROOT/08_recover_seed.sh" "$seed"
        set +e
        "$ROOT/04_check_candidates.sh"
        status=$?
        set -e
        case $status in
            0) break ;;
            2) echo "More independent candidates required after seed $seed." ;;
            *) echo "Union check failed with status $status." >&2; exit "$status" ;;
        esac
    done
fi
[ -f "$WORK_ROOT/certificate/AUGMENTED_CERTIFICATE_COMPLETE" ] || {
    echo "All retained seeds exhausted without a complete union certificate." >&2
    exit 2
}
# Use further seeds only if required for the exact certificate: collecting
# redundant candidates is not part of the mathematical proof obligation.
[ "$check_only" -eq 0 ] || exit 0
export OMP_NUM_THREADS=${SLURM_CPUS_PER_TASK:-64}
exec "$ROOT/05_finish.sh"
