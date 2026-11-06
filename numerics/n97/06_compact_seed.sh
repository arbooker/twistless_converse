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
WDIR="$SEED_ROOT/seed-$SEED"
case $WDIR in
    "$WORK_ROOT"/seeds/seed-[0-9]*) ;;
    *) echo "ERROR: unsafe seed path $WDIR" >&2; exit 1 ;;
esac
[ -f "$WDIR/SEED_COMPLETE" ] || {
    echo "ERROR: refusing to compact an incomplete seed." >&2
    exit 1
}
if [ -f "$WDIR/SEED_COMPACTED" ]; then
    echo "Seed $SEED is already compacted."
    exit 0
fi

(cd "$WDIR" && sha256sum -c retained.sha256)

shopt -s nullglob
discard=(
    "$WDIR"/A* "$WDIR"/Cd* "$WDIR"/Cr* "$WDIR"/Ct* "$WDIR"/Cv*
    "$WDIR"/K* "$WDIR"/S* "$WDIR"/V* "$WDIR"/X
)
for file in "${discard[@]}"; do
    [ -f "$file" ] && rm -f -- "$file"
done
for directory in "$WDIR/${MATRIX_BASENAME}-square."*; do
    [ -d "$directory" ] && rm -rf -- "$directory"
done
date --iso-8601=seconds >"$WDIR/SEED_COMPACTED"
echo "Compacted seed $SEED after exact checking; retained F*, W.sols*, reports, logs, and checksums."
