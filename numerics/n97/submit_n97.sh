#!/usr/bin/env bash
set -euo pipefail
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
. "$ROOT/settings.sh"
if [ "$#" -lt 2 ]; then
    echo "Usage: $0 smoke|production /absolute/work/path [I_UNDERSTAND]" >&2
    exit 1
fi
mode=$1
work=$2
case $work in /*) ;; *) echo 'Work path must be absolute.' >&2; exit 1 ;; esac
case $work in *[[:space:],]*) echo 'Work path may not contain whitespace or commas.' >&2; exit 1 ;; esac
: "${CADO_BWC_DIR:?Set the shared CADO build directory before submitting}"
: "${N97_PARTITION:?Set the production Slurm partition}"
command -v sbatch >/dev/null
mkdir -p "$work/logs"
submit() {
    local script=$1
    local partition=$2
    shift 2
    sbatch --parsable --chdir="$ROOT" --partition="$partition" \
        --export="ALL,N97_WORK_ROOT=$work,N97_BUNDLE_ROOT=$ROOT" \
        --output="$work/logs/%x-%A_%a.out" "$@" "$ROOT/slurm/$script"
}
case $mode in
    smoke)
        [ "$#" -eq 2 ] || exit 1
        submit 00_smoke.sbatch "${N97_TEST_PARTITION:-$N97_PARTITION}"
        ;;
    production)
        [ "$#" -eq 3 ] && [ "$3" = I_UNDERSTAND ] || {
            echo 'Large launch requires literal confirmation I_UNDERSTAND.' >&2; exit 1;
        }
        [ -f "$work/SMOKE_PASS" ] || { echo 'Run and complete the smoke test first.' >&2; exit 1; }
        prep=$(submit 10_prepare.sbatch "$N97_PARTITION")
        seeds=$(submit 20_seed_array.sbatch "$N97_PARTITION" \
            --dependency="afterok:$prep" \
            --array="0-$((DEFAULT_SEED_COUNT-1))%${N97_ARRAY_CONCURRENCY:-16}")
        finish=$(submit 40_finish.sbatch "${N97_FINISH_PARTITION:-$N97_PARTITION}" --dependency="afterok:$seeds")
        printf 'Preparation: %s\nSeed array: %s\nExact check and finisher: %s\n' "$prep" "$seeds" "$finish"
        ;;
    *) echo 'Choose smoke or production.' >&2; exit 1 ;;
esac
