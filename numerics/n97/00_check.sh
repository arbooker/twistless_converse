#!/usr/bin/env bash
set -euo pipefail
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
. "$ROOT/settings.sh"
: "${CADO_BWC_DIR:?Set CADO_BWC_DIR to the CADO build linalg/bwc directory}"
for command in perl stat awk sed sha256sum flock taskset lscpu; do
    command -v "$command" >/dev/null || { echo "Missing command: $command" >&2; exit 1; }
done
perl -c "$CADO_BWC_DIR/bwc.pl"
for exe in prep secure krylov lingen_b64 mksol gather cleanup acollect bwccheck mf_bal dispatch random_matrix; do
    [ -x "$CADO_BWC_DIR/$exe" ] || { echo "Missing CADO executable: $exe" >&2; exit 1; }
done
hall=$("$ROOT/../bin/spatial_qorder_hall_screen" "$N_LEVEL" "$Q_TOTAL")
printf '%s\n' "$hall"
printf '%s\n' "$hall" | grep -q 'status=PASS_SCREEN'
estimate=$("$ROOT/../bin/spatial_crt_bw_export" "$N_LEVEL" "$Q_TOTAL" "$PARITY" --estimate)
printf '%s\n' "$estimate"
for field in "rows=$EXPECTED_ROWS" "columns=$EXPECTED_COLUMNS" "nonzeros=$EXPECTED_NONZEROS"; do
    printf '%s\n' "$estimate" | grep -Eq "(^| )${field}( |$)"
done
setup=$("$ROOT/../bin/spatial_crt_kernel_f2_bw_finish_minor_largeq" "$N_LEVEL" "$Q_TOTAL" --setup-only)
printf '%s\n' "$setup"
for field in "M=$MULTIPLIER" "Q=$Q_TOTAL" "global_parity_columns=$EXPECTED_COLUMNS" "full_coprime_rows=$EXPECTED_FULL_COPRIME_ROWS"; do
    printf '%s\n' "$setup" | grep -Eq "(^| )${field}( |$)"
done
printf '%s\n' "$setup" | grep -qx LARGE_Q_SETUP_PASS
echo CHECK_PASS
