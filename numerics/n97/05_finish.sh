#!/usr/bin/env bash
set -euo pipefail

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
. "$ROOT/common.sh"
require_work_root

CERT="$WORK_ROOT/certificate"
[ -f "$MATRIX_DIR/MATRIX_READY" ] || {
    echo "Matrix is not ready." >&2
    exit 1
}
[ -f "$CERT/AUGMENTED_CERTIFICATE_COMPLETE" ] || {
    echo "The exact distributed union certificate is not complete." >&2
    exit 1
}
[ -f "$CERT/candidate-files.txt" ] || {
    echo "Missing candidate-files.txt." >&2
    exit 1
}
[ -f "$CERT/augmented-nullity.txt" ] || {
    echo "Missing augmented-nullity.txt." >&2
    exit 1
}

if [ -f "$CERT/FINISHER_COMPLETE" ]; then
    echo "FINISHER_ALREADY_COMPLETE"
    exit 0
fi

mapfile -t relative_candidates <"$CERT/candidate-files.txt"
[ "${#relative_candidates[@]}" -gt 0 ] || {
    echo "The candidate list is empty." >&2
    exit 1
}

# The 350-GiB envelope below assumes no more than the original sixteen
# width-512 seeds: 16 * 8 cleanup files = 128 files = 8192 candidate lanes.
# More seeds remain mathematically valid but require a separate memory plan.
if [ "${#relative_candidates[@]}" -gt 128 ]; then
    echo "Refusing ${#relative_candidates[@]} cleanup files in the 350-GiB finisher; the audited cap is 128." >&2
    exit 1
fi

candidates=()
for relative in "${relative_candidates[@]}"; do
    case $relative in
        seeds/seed-*/W.sols*) ;;
        *) echo "Unsafe or unexpected candidate path: $relative" >&2; exit 1 ;;
    esac
    case /$relative/ in
        */../*) echo "Candidate path escapes WORK_ROOT: $relative" >&2; exit 1 ;;
    esac
    candidate="$WORK_ROOT/$relative"
    [ -f "$candidate" ] || {
        echo "Missing retained candidate: $candidate" >&2
        exit 1
    }
    candidates+=("$candidate")
done

target=$(tr -d '[:space:]' <"$CERT/augmented-nullity.txt")
case $target in
    ''|*[!0-9]*) echo "Invalid augmented-nullity.txt." >&2; exit 1 ;;
esac
lanes=$((64 * ${#candidates[@]}))
[ "$lanes" -ge "$target" ] || {
    echo "Only $lanes candidate lanes are available for augmented nullity $target." >&2
    exit 1
}

projection_seed=${N97_FINISHER_SEED:-970017}
oversample=${N97_FINISHER_OVERSAMPLE:-2}
hashes=${N97_FINISHER_HASHES:-3}
case $projection_seed:$oversample:$hashes in
    *[!0-9:]*) echo "Invalid finisher projection settings." >&2; exit 1 ;;
esac
[ "$oversample" -gt 0 ] && [ "$hashes" -gt 0 ] || {
    echo "Finisher oversample and hash count must be positive." >&2
    exit 1
}

mkdir -p "$CERT"
lock="$CERT/FINISHER_RUNNING"
if ! mkdir "$lock" 2>/dev/null; then
    echo "Another finisher appears to be running: $lock" >&2
    exit 1
fi
trap 'rmdir "$lock" 2>/dev/null || true' EXIT

report="$CERT/finisher-report.txt"
temporary="$report.tmp.$$"
set +e
run_timed "$ROOT/../bin/spatial_crt_kernel_f2_bw_finish_minor_largeq" \
    "$N_LEVEL" "$Q_TOTAL" "$CORE" "$projection_seed" \
    "$oversample" "$hashes" "${candidates[@]}" 2>&1 | tee "$temporary"
status=${PIPESTATUS[0]}
set -e
mv "$temporary" "$report"

if [ "$status" -ne 0 ]; then
    echo "Finisher exited with status $status; no completion marker written." >&2
    exit "$status"
fi
if ! grep -Eq '^PROJECTION_CERTIFIED .*final_defect=0 ' "$report"; then
    echo "Finisher returned success without the exact full-rank certificate line." >&2
    exit 1
fi

sha256sum "$report" >"$CERT/finisher-report.sha256.tmp"
mv "$CERT/finisher-report.sha256.tmp" "$CERT/finisher-report.sha256"
date --iso-8601=seconds >"$CERT/FINISHER_COMPLETE.tmp"
mv "$CERT/FINISHER_COMPLETE.tmp" "$CERT/FINISHER_COMPLETE"
echo "FINISHER_COMPLETE N=$N_LEVEL Q=$Q_TOTAL candidate_lanes=$lanes"
