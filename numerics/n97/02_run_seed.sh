#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -ne 1 ]; then
    echo "Usage: $0 SEED" >&2
    exit 1
fi
SEED=$1
case $SEED in
    *[!0-9]*|'') echo "SEED must be a nonnegative integer" >&2; exit 1 ;;
esac

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
. "$ROOT/common.sh"
require_work_root
[ -f "$MATRIX_DIR/MATRIX_READY" ] || { echo "Matrix is not ready." >&2; exit 1; }

WDIR="$SEED_ROOT/seed-$SEED"
BWC="${CADO_BWC_DIR:?Set CADO_BWC_DIR to the CADO build linalg/bwc directory}"
mkdir -p "$WDIR"
if [ -f "$WDIR/SEED_COMPLETE" ]; then
    echo "Seed $SEED is already complete."
    exit 0
fi

common=(
    nullspace=RIGHT n="$BWC_N" m="$BWC_M" prime=2
    thr="$BWC_THREADS" seed="$SEED"
    checkpoint_precious="$BWC_CHECKPOINT_INTERVAL"
    lingen_thr="$BWC_LINGEN_THREADS"
    balancing_options=reorder=columns matrix="$SQUARE" wdir="$WDIR"
)
mksol_ranges=$(cado_mksol_ranges "$BWC_N")
output_ranges=$(cado_output_ranges "$BWC_N")

echo "Running/resuming seed $SEED with m=n=$BWC_N thr=$BWC_THREADS lingen_thr=$BWC_LINGEN_THREADS interval=$BWC_INTERVAL"
echo "CADO mksol ranges: $mksol_ranges; output ranges: $output_ranges"
{
    run_timed "$BWC/bwc.pl" :complete "${common[@]}" \
        interval="$BWC_INTERVAL" solutions="$output_ranges" stop_at_step=mksol
    run_timed "$BWC/bwc.pl" mksol "${common[@]}" interval="$BWC_MKSOL_INTERVAL" solutions="$mksol_ranges"
    run_timed "$BWC/bwc.pl" gather "${common[@]}" interval="$BWC_MKSOL_INTERVAL" solutions="$output_ranges"
    run_timed "$BWC/bwc.pl" cleanup "${common[@]}" interval="$BWC_MKSOL_INTERVAL" solutions="$output_ranges"
} 2>&1 | tee -a "$WDIR/complete.log"

solutions=()
for ((start=0; start<BWC_N; start+=64)); do
    end=$((start + 64))
    output="$WDIR/W.sols$start-$end"
    [ -f "$output" ] || { echo "ERROR: :complete did not create $output" >&2; exit 1; }
    solutions+=("$output")
done

echo "Analyzing the independent lingen rank lower bound..."
"$ROOT/../bin/cado_rank_from_lingen_f2" "$BWC_N" "$WDIR/F" \
    --max-order 32 --max-mib 8192 | tee "$WDIR/lingen-rank.txt"

echo "Independently checking all $BWC_N candidates against the completed matrix..."
check_report=$(run_timed "$ROOT/../bin/cado_solution_check_f2" \
    "$SQUARE" "${solutions[@]}" 2>&1 | tee "$WDIR/square-candidates.txt")
printf '%s\n' "$check_report"
summary=$(printf '%s\n' "$check_report" | grep '^mode=verify ' | tail -n 1)
rank=$(printf '%s\n' "$summary" | field_from_line candidate_rank)
bad=$(printf '%s\n' "$summary" | field_from_line bad_rows)
case ${rank:-} in *[!0-9]*|'') echo "ERROR: could not parse candidate rank." >&2; exit 1 ;; esac
case ${bad:-} in *[!0-9]*|'') echo "ERROR: could not parse bad-row count." >&2; exit 1 ;; esac
if [ "$rank" -eq 0 ] || [ "$bad" -ne 0 ]; then
    echo "ERROR: seed $SEED failed its exact candidate check (rank=$rank bad_rows=$bad)." >&2
    exit 1
fi

(
    cd "$WDIR"
    find . -maxdepth 1 -type f \
        \( -name 'F.sols*' -o -name 'W.sols*' -o -name 'lingen-rank.txt' \
           -o -name 'square-candidates.txt' \) -print0 \
        | sort -z | xargs -0 sha256sum
) >"$WDIR/retained.sha256"

date --iso-8601=seconds >"$WDIR/SEED_COMPLETE.tmp"
mv "$WDIR/SEED_COMPLETE.tmp" "$WDIR/SEED_COMPLETE"
echo "SEED_COMPLETE $SEED"

if [ "${N97_AUTO_COMPACT:-1}" -eq 1 ]; then
    "$ROOT/06_compact_seed.sh" "$SEED"
fi
