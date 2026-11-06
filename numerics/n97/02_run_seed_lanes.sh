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

streams=${N97_KRYLOV_STREAMS:-8}
threads_per_core=${N97_THREADS_PER_CORE:-1}
case $threads_per_core:$streams in
    1:4) lane_cores=6; lane_threads=6; lane_grid=2x3 ;;
    1:8) lane_cores=3; lane_threads=3; lane_grid=1x3 ;;
    2:8) lane_cores=3; lane_threads=6; lane_grid=2x3 ;;
    2:*) echo "Two hardware threads per core are supported only with eight streams." >&2; exit 1 ;;
    *) echo "N97_THREADS_PER_CORE must be 1 or 2, and N97_KRYLOV_STREAMS must be 4 or 8." >&2; exit 1 ;;
esac
post_grid=${BWC_LINGEN_THREADS:-4x6}

mapfile -t allocated_cores < <(allocated_core_cpu_lists)
[ "${#allocated_cores[@]}" -ge 24 ] || {
    echo "The allocation exposes only ${#allocated_cores[@]} physical cores; 24 are required." >&2
    exit 1
}
allocated_cores=("${allocated_cores[@]:0:24}")
core_cpu_lists=()
for cpu_group in "${allocated_cores[@]}"; do
    IFS=',' read -r -a siblings <<<"$cpu_group"
    [ "${#siblings[@]}" -ge "$threads_per_core" ] || {
        echo "Requested $threads_per_core hardware thread(s) per core, but core group $cpu_group exposes only ${#siblings[@]}." >&2
        exit 1
    }
    selected=${siblings[0]}
    if [ "$threads_per_core" -eq 2 ]; then
        selected="$selected,${siblings[1]}"
    fi
    core_cpu_lists+=("$selected")
done
echo "Using $streams Krylov streams, $lane_cores physical cores and $lane_threads hardware threads per stream."
echo "Allocated CPU groups by physical core: ${core_cpu_lists[*]}"

lane_common=(
    nullspace=RIGHT n="$BWC_N" m="$BWC_M" prime=2
    thr="$lane_grid" interval="$BWC_INTERVAL" seed="$SEED"
    balancing_options=reorder=columns matrix="$SQUARE" wdir="$WDIR"
)
post_common=(
    nullspace=RIGHT n="$BWC_N" m="$BWC_M" prime=2
    thr="$post_grid" interval="$BWC_MKSOL_INTERVAL" seed="$SEED"
    checkpoint_precious="$BWC_CHECKPOINT_INTERVAL"
    skip_online_checks=1
    balancing_options=reorder=columns matrix="$SQUARE" wdir="$WDIR"
)
output_ranges=$(cado_output_ranges "$BWC_N")

stage_worker=0
lane_workers=()
stop_children() {
    trap - TERM INT
    echo "Stopping active CADO processes." >&2
    if [ "$stage_worker" -gt 0 ]; then
        kill -TERM "$stage_worker" 2>/dev/null || true
    fi
    for worker in "${lane_workers[@]}"; do
        kill -TERM "$worker" 2>/dev/null || true
    done
    if [ "$stage_worker" -gt 0 ]; then
        wait "$stage_worker" 2>/dev/null || true
    fi
    for worker in "${lane_workers[@]}"; do
        wait "$worker" 2>/dev/null || true
    done
    exit 143
}
trap stop_children TERM INT

run_stage() {
    label=$1
    shift
    echo "Starting $label for seed $SEED."
    "$@" >>"$WDIR/complete.log" 2>&1 &
    stage_worker=$!
    set +e
    wait "$stage_worker"
    status=$?
    set -e
    stage_worker=0
    [ "$status" -eq 0 ] || {
        echo "$label failed with status $status; see $WDIR/complete.log." >&2
        return "$status"
    }
}

# These shared files must exist before lane workers enter the common workdir.
run_stage prep "$BWC/bwc.pl" prep "${lane_common[@]}"
run_stage secure "$BWC/bwc.pl" secure "${lane_common[@]}"

echo "Running/resuming the eight 64-lane Krylov ranges in groups of $streams."
wave_start=0
while [ "$wave_start" -lt "$BWC_N" ]; do
    lane_workers=()
    slot=0
    while [ "$slot" -lt "$streams" ]; do
        start=$((wave_start + 64 * slot))
        [ "$start" -lt "$BWC_N" ] || break
        end=$((start + 64))
        cpu_list=$(cpu_list_slice $((slot * lane_cores)) "$lane_cores" "${core_cpu_lists[@]}")
        echo "Krylov lane $start-$end CPU list: $cpu_list"
        taskset --cpu-list "$cpu_list" \
            "$BWC/bwc.pl" krylov "${lane_common[@]}" ys="$start..$end" \
            keep_rolling_checkpoints=1 checkpoint_precious="$BWC_CHECKPOINT_INTERVAL" \
            >>"$WDIR/krylov-$start-$end.log" 2>&1 &
        lane_workers+=("$!")
        slot=$((slot + 1))
    done
    status=0
    set +e
    for worker in "${lane_workers[@]}"; do
        wait "$worker" || status=1
    done
    set -e
    lane_workers=()
    [ "$status" -eq 0 ] || {
        echo "At least one Krylov lane failed; see $WDIR/krylov-*.log." >&2
        exit 1
    }
    wave_start=$((wave_start + 64 * streams))
done

run_stage lingen "$BWC/bwc.pl" lingen "${post_common[@]}" lingen_thr="$post_grid"

# The collected Krylov sequence is no longer needed after lingen.  Likewise,
# mksol needs only checkpoints at multiples of BWC_CHECKPOINT_INTERVAL.  Removing
# the other rolling vectors here makes this intentionally a one-shot
# calculation while preserving every vector needed for reconstruction.
shopt -s nullglob
for file in "$WDIR"/A*; do
    rm -f -- "$file"
done
for file in "$WDIR"/V*-*.*; do
    iteration=${file##*.}
    case $iteration in
        *[!0-9]*|'') echo "ERROR: unexpected checkpoint name $file" >&2; exit 1 ;;
    esac
    [ $((iteration % BWC_CHECKPOINT_INTERVAL)) -eq 0 ] || rm -f -- "$file"
done
for file in "$WDIR"/X "$WDIR"/Cd* "$WDIR"/Cr* "$WDIR"/Ct* "$WDIR"/Cv*; do
    [ -f "$file" ] && rm -f -- "$file"
done

# Reconstruct at most 256 candidates at a time, immediately turn each batch
# into its final W.sols* files, and discard the batch's S/K intermediates.
# This keeps the reconstruction peak bounded by one batch instead of two.
group_start=0
while [ "$group_start" -lt "$BWC_N" ]; do
    group_end=$((group_start + 256))
    [ "$group_end" -le "$BWC_N" ] || group_end=$BWC_N
    group="$group_start-$group_end"
    group_outputs=
    start=$group_start
    while [ "$start" -lt "$group_end" ]; do
        end=$((start + 64))
        [ -z "$group_outputs" ] || group_outputs="$group_outputs,"
        group_outputs="$group_outputs$start-$end"
        start=$end
    done

    run_stage "mksol $group" "$BWC/mksol" "${post_common[@]}" start=0 solutions="$group"
    run_stage "gather $group" "$BWC/bwc.pl" gather "${post_common[@]}" solutions="$group_outputs"
    run_stage "cleanup $group" "$BWC/bwc.pl" cleanup "${post_common[@]}" solutions="$group_outputs"

    start=$group_start
    while [ "$start" -lt "$group_end" ]; do
        end=$((start + 64))
        [ -f "$WDIR/W.sols$start-$end" ] || {
            echo "ERROR: reconstruction batch $group is missing W.sols$start-$end" >&2
            exit 1
        }
        for file in "$WDIR"/K.sols"$start-$end".*; do
            rm -f -- "$file"
        done
        for file in "$WDIR"/S.sols"$start-$end".*; do
            rm -f -- "$file"
        done
        start=$end
    done
    for file in "$WDIR"/V*-*.*; do
        iteration=${file##*.}
        case $iteration in
            *[!0-9]*|'') echo "ERROR: unexpected checkpoint name $file" >&2; exit 1 ;;
        esac
        [ $((iteration % BWC_CHECKPOINT_INTERVAL)) -eq 0 ] || rm -f -- "$file"
    done
    group_start=$group_end
done

# No reconstruction stage follows, so the remaining starting vectors are now
# disposable.  The exact checker below needs only the matrix, F, and W.sols*
# files.  Mksol's online checks are intentionally skipped because this checker
# independently multiplies every reconstructed candidate by the full matrix.
for file in "$WDIR"/V*; do
    [ -f "$file" ] && rm -f -- "$file"
done

solutions=()
for ((start=0; start<BWC_N; start+=64)); do
    end=$((start + 64))
    output="$WDIR/W.sols$start-$end"
    [ -f "$output" ] || { echo "ERROR: missing $output" >&2; exit 1; }
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
