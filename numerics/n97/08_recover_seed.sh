#!/usr/bin/env bash
# Resume after lingen only: do not regenerate prep, Krylov or lingen inputs.
set -euo pipefail
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
. "$ROOT/common.sh"
require_work_root
BWC=${CADO_BWC_DIR:?Set CADO_BWC_DIR to the CADO build linalg/bwc directory}
: "${SLURM_JOB_ID:?Recovery must run in a compute allocation}"
[ "$#" -eq 1 ] || { echo "Usage: $0 SEED" >&2; exit 1; }
seed=$1
case $seed in ''|*[!0-9]*) echo "Invalid seed" >&2; exit 1;; esac
wdir="$SEED_ROOT/seed-$seed"
[ -d "$wdir" ] && [ -f "$MATRIX_DIR/MATRIX_READY" ] || exit 1
if [ -f "$wdir/SEED_COMPLETE" ]; then
    (cd "$wdir" && sha256sum -c retained.sha256)
    exit 0
fi
exec 8>"$wdir/recovery.lock"
flock -n 8 || { echo "Recovery already running: $wdir" >&2; exit 1; }
exec > >(tee -a "$wdir/recovery.log") 2>&1
echo "RECOVERY_START seed=$seed job=$SLURM_JOB_ID $(date --iso-8601=seconds)"

# Bound coefficient buffering independently of retained checkpoint spacing.
interval=$BWC_MKSOL_INTERVAL
precious=$BWC_CHECKPOINT_INTERVAL
grid=4x6
export OMP_NUM_THREADS=24
stage() {
    echo "RECOVERY_STAGE $(date --iso-8601=seconds) $*"
    # Bound each reconstruction stage to 128 GiB of address space.
    /usr/bin/time -v prlimit --as=137438953472 -- "$@"
}

# Check all generator blocks and the retained checkpoints mksol will consume.
# No large input is copied, deleted or replaced. File sizes are in bytes.
coeff_count=
for ((s=0; s<BWC_N; s+=64)); do
    for ((v=0; v<BWC_N; v+=64)); do
        file="$wdir/F.sols$s-$((s+64)).$v-$((v+64))"
        [ -f "$file" ] || { echo "Missing generator $file" >&2; exit 1; }
        bytes=$(stat -c %s "$file")
        [ "$bytes" -gt 0 ] && [ $((bytes % 512)) -eq 0 ] || exit 1
        count=$((bytes / 512))
        if [ -z "$coeff_count" ]; then coeff_count=$count; fi
        [ "$count" -eq "$coeff_count" ] || { echo "Inconsistent generator lengths" >&2; exit 1; }
    done
done
for ((v=0; v<BWC_N; v+=64)); do
    for ((iteration=0; iteration<coeff_count; iteration+=precious)); do
        file="$wdir/V$v-$((v+64)).$iteration"
        [ -f "$file" ] || { echo "Missing checkpoint $file" >&2; exit 1; }
        [ "$(stat -c %s "$file")" -eq $((EXPECTED_ROWS * 8)) ] || {
            echo "Wrong checkpoint size: $file" >&2; exit 1;
        }
    done
done

common=(nullspace=RIGHT n="$BWC_N" m="$BWC_M" prime=2 thr="$grid"
    interval="$interval" checkpoint_precious="$precious" seed="$seed"
    skip_online_checks=1 balancing_options=reorder=columns
    matrix="$SQUARE" wdir="$wdir")
stage "$ROOT/../bin/cado_rank_from_lingen_f2" "$BWC_N" "$wdir/F" \
    --max-order 32 --max-mib 8192 | tee "$wdir/lingen-rank.txt"
degree=$(sed -n 's/^determinant_degree=//p' "$wdir/lingen-rank.txt")
case $degree in ''|*[!0-9]*) echo "Missing generator degree" >&2; exit 1;; esac
target=$((EXPECTED_ROWS-degree))
[ "$target" -gt 0 ] || { echo "Unexpected nullity bound $target" >&2; exit 1; }
solutions=()
for ((s=0; s<BWC_N; s+=256)); do
    end=$((s+256))
    complete=1
    for ((v=s; v<end; v+=64)); do
        [ -s "$wdir/W.sols$v-$((v+64))" ] || complete=0
    done
    if [ "$complete" -eq 0 ]; then
        # Direct mksol avoids bwc.pl attempting secure/prep after their inputs
        # were intentionally compacted. Recalculate partial S files if needed.
        stage "$BWC/mksol" "${common[@]}" start=0 solutions="$s-$end"
        ranges=$(cado_output_ranges 256)
        if [ "$s" -ne 0 ]; then
            ranges=256-320,320-384,384-448,448-512
        fi
        stage "$BWC/bwc.pl" gather "${common[@]}" solutions="$ranges"
        stage "$BWC/bwc.pl" cleanup "${common[@]}" solutions="$ranges"
    fi
    for ((v=s; v<end; v+=64)); do
        file="$wdir/W.sols$v-$((v+64))"
        [ -f "$file" ] || { echo "Missing cleaned candidate $file" >&2; exit 1; }
        solutions+=("$file")
    done
    stage "$ROOT/../bin/cado_solution_check_f2" "$SQUARE" "${solutions[@]}" \
        | tee "$wdir/square-candidates.txt"
    summary=$(grep '^mode=verify ' "$wdir/square-candidates.txt" | tail -n 1)
    rank=$(printf '%s\n' "$summary" | field_from_line candidate_rank)
    bad=$(printf '%s\n' "$summary" | field_from_line bad_rows)
    case $rank:$bad in *[!0-9:]*|:*|*:) echo "Missing exact verification summary" >&2; exit 1;; esac
    [ "$bad" -eq 0 ] && [ "$rank" -le "$target" ] || {
        echo "Candidate verification or rank-bound consistency failed" >&2; exit 1;
    }
    if [ "$rank" -eq "$target" ]; then
        echo "EXACT_SEED_KERNEL_COMPLETE rank=$rank after_candidates=$end"
        break
    fi
done
[ "$rank" -gt 0 ] && [ "$bad" -eq 0 ] || { echo "Candidate verification failed" >&2; exit 1; }
printf '%s\n' "${solutions[@]##*/}" >"$wdir/recovered-candidates.txt"
(
    cd "$wdir"
    find . -maxdepth 1 -type f \( -name 'F.sols*' -o -name 'W.sols*' \
        -o -name 'lingen-rank.txt' -o -name 'square-candidates.txt' \
        -o -name 'recovered-candidates.txt' \) \
        -print0 | sort -z | xargs -0 sha256sum
) >"$wdir/retained.sha256"
date --iso-8601=seconds >"$wdir/SEED_COMPLETE.tmp"
mv "$wdir/SEED_COMPLETE.tmp" "$wdir/SEED_COMPLETE"
echo "SEED_COMPLETE seed=$seed rank=$rank $(date --iso-8601=seconds)"
# Preserve generator/checkpoint files even after success. No cleanup deletion
# is necessary for the recovery's current disk envelope.
