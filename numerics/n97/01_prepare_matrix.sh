#!/usr/bin/env bash
set -euo pipefail

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
. "$ROOT/common.sh"
require_work_root

mkdir -p "$WORK_ROOT" "$MATRIX_DIR" "$SEED_ROOT" "$WORK_ROOT/logs"
READY="$MATRIX_DIR/MATRIX_READY"
if [ -f "$READY" ]; then
    echo "Matrix is already prepared: $SQUARE"
    exit 0
fi

final_files=(
    "$CORE" "${CORE%.bin}.rw.bin" "${CORE%.bin}.cw.bin"
    "$SQUARE" "${SQUARE%.bin}.rw.bin" "${SQUARE%.bin}.cw.bin"
)
for path in "${final_files[@]}"; do
    if [ -e "$path" ]; then
        echo "ERROR: partial final matrix set exists without $READY: $path" >&2
        exit 1
    fi
done

available_kib=$(df -Pk "$WORK_ROOT" | awk 'NR==2 {print $4}')
if [ "$available_kib" -lt 20971520 ]; then
    echo "ERROR: matrix preparation requires at least 20 GiB free." >&2
    exit 1
fi

tag=${SLURM_JOB_ID:-local-$$}
STAGE="$WORK_ROOT/.matrix-build-$tag"
if [ -e "$STAGE" ]; then
    echo "ERROR: staging path already exists: $STAGE" >&2
    exit 1
fi
mkdir "$STAGE"
stage_core="$STAGE/$MATRIX_BASENAME.bin"
stage_square="$STAGE/$MATRIX_BASENAME-square.bin"

echo "Exporting the parity-$PARITY common core..."
run_timed "$ROOT/../bin/spatial_crt_bw_export" \
    "$N_LEVEL" "$Q_TOTAL" "$PARITY" "$stage_core" \
    2>&1 | tee "$STAGE/export.log"
for expected_field in \
    "rows=$EXPECTED_ROWS" \
    "columns=$EXPECTED_COLUMNS" \
    "nonzeros=$EXPECTED_NONZEROS"
do
    grep -Eq "(^| )${expected_field}( |$)" "$STAGE/export.log" || {
        echo "ERROR: exported dimensions differ from the audited values: missing ${expected_field}." >&2
        exit 1
    }
done

echo "Adding $EXPECTED_ADDED_COLUMNS sparse unit columns..."
run_timed "$ROOT/../bin/cado_square_complete_f2" \
    "$stage_core" "$COMPLETION_SEED" "$stage_square" \
    2>&1 | tee "$STAGE/square-completion.log"

for suffix in .bin .rw.bin .cw.bin; do
    [ -s "${stage_core%.bin}$suffix" ] || { echo "Missing staged core$suffix" >&2; exit 1; }
    [ -s "${stage_square%.bin}$suffix" ] || { echo "Missing staged square$suffix" >&2; exit 1; }
done

mv "$STAGE"/* "$MATRIX_DIR"/
rmdir "$STAGE"
date --iso-8601=seconds >"$READY.tmp-$tag"
mv "$READY.tmp-$tag" "$READY"
echo "MATRIX_READY $SQUARE"
