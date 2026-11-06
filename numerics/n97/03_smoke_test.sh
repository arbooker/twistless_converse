#!/usr/bin/env bash
set -euo pipefail

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
. "$ROOT/common.sh"
require_work_root

if [ "${SMOKE_SKIP_PLATFORM_CHECK:-0}" -ne 1 ]; then
    "$ROOT/00_check.sh"
fi

BIN=${SMOKE_BIN_DIR:-$ROOT/../bin}
BWC=${SMOKE_BWC_DIR:-${CADO_BWC_DIR:?Set CADO_BWC_DIR to the CADO build linalg/bwc directory}}
WIDTH=${SMOKE_WIDTH:-512}
THREADS=${SMOKE_THREADS:-2x4}
case $WIDTH in
    *[!0-9]*|'') echo "Invalid SMOKE_WIDTH" >&2; exit 1 ;;
esac
if [ "$WIDTH" -lt 64 ] || [ $((WIDTH % 64)) -ne 0 ]; then
    echo "SMOKE_WIDTH must be a positive multiple of 64." >&2
    exit 1
fi

# This is the already certified N=71 control from the sparse-only pipeline.
SMOKE_N=71
SMOKE_Q=25585560
SMOKE_PARITY=0
SMOKE_COMPLETION_SEED=71001
EXPECTED_DEGREE=186455
EXPECTED_NULLITY=53

tag=${SLURM_JOB_ID:-local-$$}
SDIR="$WORK_ROOT/smoke/$tag"
if [ -e "$SDIR" ]; then
    echo "ERROR: smoke directory already exists: $SDIR" >&2
    exit 1
fi
mkdir -p "$SDIR/wdir"
core="$SDIR/n71-core0.bin"
square="$SDIR/n71-core0-square.bin"

run_timed "$BIN/spatial_crt_bw_export" \
    "$SMOKE_N" "$SMOKE_Q" "$SMOKE_PARITY" "$core"
run_timed "$BIN/cado_square_complete_f2" \
    "$core" "$SMOKE_COMPLETION_SEED" "$square"

seed=7105
output_ranges=$(cado_output_ranges "$WIDTH")
smoke_checkpoint_interval=${SMOKE_CHECKPOINT_INTERVAL:-512}
smoke_mksol_interval=${SMOKE_MKSOL_INTERVAL:-32}
lane_parallel=${SMOKE_LANE_PARALLEL:-0}
case $lane_parallel in 0|1) ;; *) echo "SMOKE_LANE_PARALLEL must be 0 or 1." >&2; exit 1 ;; esac

shopt -s nullglob
discard_smoke_lingen_inputs() {
    for file in "$SDIR/wdir"/A*; do
        rm -f -- "$file"
    done
    for file in "$SDIR/wdir"/V*-*.*; do
        iteration=${file##*.}
        case $iteration in
            *[!0-9]*|'') echo "Unexpected smoke checkpoint name $file" >&2; return 1 ;;
        esac
        [ $((iteration % smoke_checkpoint_interval)) -eq 0 ] || rm -f -- "$file"
    done
    for file in "$SDIR/wdir"/X "$SDIR/wdir"/Cd* "$SDIR/wdir"/Cr* \
                "$SDIR/wdir"/Ct* "$SDIR/wdir"/Cv*; do
        [ -f "$file" ] && rm -f -- "$file"
    done
}

run_smoke_reconstruction() {
    group_start=0
    while [ "$group_start" -lt "$WIDTH" ]; do
        group_end=$((group_start + 256))
        [ "$group_end" -le "$WIDTH" ] || group_end=$WIDTH
        group="$group_start-$group_end"
        group_outputs=
        start=$group_start
        while [ "$start" -lt "$group_end" ]; do
            end=$((start + 64))
            [ -z "$group_outputs" ] || group_outputs="$group_outputs,"
            group_outputs="$group_outputs$start-$end"
            start=$end
        done

        run_timed "$BWC/mksol" "${post_common[@]}" start=0 solutions="$group"
        run_timed "$BWC/bwc.pl" gather "${post_common[@]}" solutions="$group_outputs"
        run_timed "$BWC/bwc.pl" cleanup "${post_common[@]}" solutions="$group_outputs"

        start=$group_start
        while [ "$start" -lt "$group_end" ]; do
            end=$((start + 64))
            [ -f "$SDIR/wdir/W.sols$start-$end" ] || {
                echo "Missing smoke solution W.sols$start-$end" >&2
                return 1
            }
            for file in "$SDIR/wdir"/K.sols"$start-$end".*; do
                rm -f -- "$file"
            done
            for file in "$SDIR/wdir"/S.sols"$start-$end".*; do
                rm -f -- "$file"
            done
            start=$end
        done
        for file in "$SDIR/wdir"/V*-*.*; do
            iteration=${file##*.}
            case $iteration in
                *[!0-9]*|'') echo "Unexpected smoke checkpoint name $file" >&2; return 1 ;;
            esac
            [ $((iteration % smoke_checkpoint_interval)) -eq 0 ] || rm -f -- "$file"
        done
        group_start=$group_end
    done
}

if [ "$lane_parallel" -eq 0 ]; then
    lane_common=(
        nullspace=RIGHT n="$WIDTH" m="$WIDTH" prime=2
        thr="$THREADS" interval=64 seed="$seed"
        balancing_options=reorder=columns matrix="$square" wdir="$SDIR/wdir"
    )
    post_common=(
        nullspace=RIGHT n="$WIDTH" m="$WIDTH" prime=2
        thr="$THREADS" interval="$smoke_mksol_interval" checkpoint_precious="$smoke_checkpoint_interval" seed="$seed"
        skip_online_checks=1
        balancing_options=reorder=columns matrix="$square" wdir="$SDIR/wdir"
    )
    {
        run_timed "$BWC/bwc.pl" prep "${lane_common[@]}"
        run_timed "$BWC/bwc.pl" secure "${lane_common[@]}"
        run_timed "$BWC/bwc.pl" krylov "${lane_common[@]}" \
            keep_rolling_checkpoints=1 checkpoint_precious="$smoke_checkpoint_interval"
        run_timed "$BWC/bwc.pl" lingen "${post_common[@]}" lingen_thr="$THREADS"
        discard_smoke_lingen_inputs
        run_smoke_reconstruction
    } 2>&1 | tee "$SDIR/complete.log"
else
    [ "$WIDTH" -eq 512 ] || {
        echo "The lane-parallel smoke test requires width 512." >&2
        exit 1
    }
    mapfile -t allocated_cores < <(allocated_core_cpu_lists)
    [ "${#allocated_cores[@]}" -ge 24 ] || {
        echo "The SMT smoke allocation exposes only ${#allocated_cores[@]} physical cores; 24 are required." >&2
        exit 1
    }
    allocated_cores=("${allocated_cores[@]:0:24}")
    core_cpu_lists=()
    for cpu_group in "${allocated_cores[@]}"; do
        IFS=',' read -r -a siblings <<<"$cpu_group"
        [ "${#siblings[@]}" -ge 2 ] || {
            echo "The SMT smoke test needs both hardware threads, but core group $cpu_group exposes only ${#siblings[@]}." >&2
            exit 1
        }
        core_cpu_lists+=("${siblings[0]},${siblings[1]}")
    done
    echo "SMT smoke CPU groups: ${core_cpu_lists[*]}"

    lane_common=(
        nullspace=RIGHT n="$WIDTH" m="$WIDTH" prime=2
        thr=2x3 interval=64 seed="$seed"
        balancing_options=reorder=columns matrix="$square" wdir="$SDIR/wdir"
    )
    post_common=(
        nullspace=RIGHT n="$WIDTH" m="$WIDTH" prime=2
        thr=4x6 interval="$smoke_mksol_interval" checkpoint_precious="$smoke_checkpoint_interval" seed="$seed"
        skip_online_checks=1
        balancing_options=reorder=columns matrix="$square" wdir="$SDIR/wdir"
    )

    {
        run_timed "$BWC/bwc.pl" prep "${lane_common[@]}"
        run_timed "$BWC/bwc.pl" secure "${lane_common[@]}"
    } 2>&1 | tee "$SDIR/complete.log"

    run_lane_group() {
        pids=()
        lane=0
        while [ "$lane" -lt 8 ]; do
            start=$((64 * lane))
            end=$((start + 64))
            cpu_list=$(cpu_list_slice $((3 * lane)) 3 "${core_cpu_lists[@]}")
            echo "Krylov lane $start-$end CPU list: $cpu_list"
            run_timed taskset --cpu-list "$cpu_list" \
                "$BWC/bwc.pl" krylov "${lane_common[@]}" ys="$start..$end" \
                keep_rolling_checkpoints=1 checkpoint_precious="$smoke_checkpoint_interval" \
                >"$SDIR/krylov-$start-$end.log" 2>&1 &
            pids+=("$!")
            lane=$((lane + 1))
        done
        status=0
        set +e
        for pid in "${pids[@]}"; do
            wait "$pid" || status=1
        done
        set -e
        [ "$status" -eq 0 ] || {
            echo "The SMT Krylov group failed; see $SDIR/krylov-*.log." >&2
            return 1
        }
    }

    run_lane_group

    {
        run_timed "$BWC/bwc.pl" lingen "${post_common[@]}" lingen_thr=4x6
        discard_smoke_lingen_inputs
        run_smoke_reconstruction
    } 2>&1 | tee -a "$SDIR/complete.log"
fi

solutions=()
for ((start=0; start<WIDTH; start+=64)); do
    end=$((start + 64))
    file="$SDIR/wdir/W.sols$start-$end"
    [ -f "$file" ] || { echo "Missing smoke solution $file" >&2; exit 1; }
    solutions+=("$file")
done

rank_report=$("$BIN/cado_rank_from_lingen_f2" "$WIDTH" "$SDIR/wdir/F" \
    --max-order 32 --max-mib 2048)
printf '%s\n' "$rank_report" | tee "$SDIR/lingen-rank.txt"
degree=$(printf '%s\n' "$rank_report" | sed -n 's/^determinant_degree=//p')

check_report=$("$BIN/cado_solution_check_f2" "$square" "${solutions[@]}")
printf '%s\n' "$check_report" | tee "$SDIR/square-candidates.txt"
summary=$(printf '%s\n' "$check_report" | grep '^mode=verify ' | tail -n 1)
rank=$(printf '%s\n' "$summary" | field_from_line candidate_rank)
bad=$(printf '%s\n' "$summary" | field_from_line bad_rows)

if [ "$degree" -ne "$EXPECTED_DEGREE" ] || \
   [ "$rank" -ne "$EXPECTED_NULLITY" ] || [ "$bad" -ne 0 ]; then
    echo "ERROR: N=71 control failed: degree=$degree rank=$rank bad_rows=$bad" >&2
    exit 1
fi

mkdir -p "$WORK_ROOT"
printf 'job=%s time=%s width=%s threads=%s\n' \
    "$tag" "$(date --iso-8601=seconds)" "$WIDTH" "$THREADS" \
    >"$WORK_ROOT/SMOKE_PASS.tmp-$tag"
mv "$WORK_ROOT/SMOKE_PASS.tmp-$tag" "$WORK_ROOT/SMOKE_PASS"
echo "SMOKE_PASS: exact N=71 certificate reproduced at width $WIDTH (lane_parallel=$lane_parallel)."
