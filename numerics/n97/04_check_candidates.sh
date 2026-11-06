#!/usr/bin/env bash
set -euo pipefail

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
. "$ROOT/common.sh"
require_work_root
[ -f "$MATRIX_DIR/MATRIX_READY" ] || { echo "Matrix is not ready." >&2; exit 1; }

CERT="$WORK_ROOT/certificate"
mkdir -p "$CERT"
command -v flock >/dev/null || {
    echo "flock is required for the union-certificate lock." >&2
    exit 1
}
exec 9>"$CERT/union-check.lock"
flock 9
if [ -f "$CERT/AUGMENTED_CERTIFICATE_COMPLETE" ]; then
    echo "AUGMENTED_CERTIFICATE_ALREADY_COMPLETE"
    exit 0
fi

mapfile -t seed_dirs < <(find "$SEED_ROOT" -mindepth 1 -maxdepth 1 -type d \
    -name 'seed-*' -exec test -f '{}/SEED_COMPLETE' \; -print | sort)
[ "${#seed_dirs[@]}" -gt 0 ] || { echo "No complete seeds found." >&2; exit 1; }

row_bytes=$(stat -Lc %s "${SQUARE%.bin}.rw.bin")
rows=$((row_bytes / 4))
[ $((row_bytes % 4)) -eq 0 ] && [ "$rows" -eq "$EXPECTED_ROWS" ] || {
    echo "Unexpected square matrix dimensions" >&2; exit 1;
}
best_degree=0
best_seed=
solutions=()
declare -A seen_candidates=()

for wdir in "${seed_dirs[@]}"; do
    echo "Verifying retained checksums in $wdir"
    (cd "$wdir" && sha256sum -c retained.sha256)
    report=$("$ROOT/../bin/cado_rank_from_lingen_f2" "$BWC_N" "$wdir/F" \
        --max-order 32 --max-mib 8192)
    printf '%s\n' "$report" >"$wdir/lingen-rank.txt.recheck"
    degree=$(printf '%s\n' "$report" | sed -n 's/^determinant_degree=//p')
    [ -n "$degree" ] || { echo "Could not parse determinant degree." >&2; exit 1; }
    if [ "$degree" -gt "$best_degree" ]; then
        best_degree=$degree
        best_seed=$wdir
    fi
    count_before=${#solutions[@]}
    seed_candidates=()
    if [ -f "$wdir/recovered-candidates.txt" ]; then
        # Recovery can stop after an exactly verified partial seed. The list
        # itself and all referenced candidates belong to retained.sha256.
        grep -Eq '  \./recovered-candidates\.txt$' "$wdir/retained.sha256" || exit 1
        mapfile -t seed_candidates <"$wdir/recovered-candidates.txt"
    else
        for ((start=0; start<BWC_N; start+=64)); do
            seed_candidates+=("W.sols$start-$((start+64))")
        done
    fi
    for name in "${seed_candidates[@]}"; do
        if [[ ! $name =~ ^W\.sols([0-9]+)-([0-9]+)$ ]]; then
            echo "Unsafe candidate name: $name" >&2; exit 1
        fi
        start=$((10#${BASH_REMATCH[1]}))
        end=$((10#${BASH_REMATCH[2]}))
        [ $((start % 64)) -eq 0 ] && [ "$end" -eq $((start+64)) ] && \
            [ "$end" -le "$BWC_N" ] || exit 1
        file="$wdir/$name"
        [ -f "$file" ] || { echo "Missing $file" >&2; exit 1; }
        [ -z "${seen_candidates[$file]:-}" ] || { echo "Duplicate candidate $file" >&2; exit 1; }
        seen_candidates[$file]=1
        # Names are validated above, so this fixed-string test cannot inject
        # path traversal or a regular expression into the checksum lookup.
        grep -Fq "  ./$name" "$wdir/retained.sha256" || exit 1
        solutions+=("$file")
    done
    added=$(( ${#solutions[@]} - count_before ))
    [ "$added" -gt 0 ] && [ "$added" -le $((BWC_N / 64)) ] || exit 1
done

target=$((rows - best_degree))
[ "$target" -ge 0 ] || { echo "Generator degree exceeds matrix dimension" >&2; exit 1; }
lanes=$((64 * ${#solutions[@]}))
echo "square_dimension=$rows best_rank_lower_bound=$best_degree augmented_nullity_upper_bound=$target candidate_lanes=$lanes"
if [ "$lanes" -lt "$target" ]; then
    echo "AUGMENTED_CERTIFICATE_INCOMPLETE: need at least $((target - lanes)) more candidate lanes."
    exit 2
fi

set +e
rank_report=$(run_timed "$ROOT/../bin/cado_solution_check_f2" --rank-only \
    --stop-at "$target" "${solutions[@]}" 2>&1)
rank_status=$?
set -e
printf '%s\n' "$rank_report"
if [ "$rank_status" -ne 0 ]; then
    echo "AUGMENTED_CERTIFICATE_INCOMPLETE: checked candidates have not reached rank $target."
    exit 2
fi
summary=$(printf '%s\n' "$rank_report" | grep '^mode=rank-only ' | tail -n 1)
rank=$(printf '%s\n' "$summary" | field_from_line candidate_rank)
[ "$rank" -eq "$target" ] || { echo "Unexpected union rank $rank" >&2; exit 1; }

: >"$CERT/candidate-files.txt.tmp"
printf '%s\n' "${solutions[@]#"$WORK_ROOT"/}" >>"$CERT/candidate-files.txt.tmp"
mv "$CERT/candidate-files.txt.tmp" "$CERT/candidate-files.txt"
printf '%s\n' "$target" >"$CERT/augmented-nullity.txt.tmp"
mv "$CERT/augmented-nullity.txt.tmp" "$CERT/augmented-nullity.txt"
printf '%s\n' "${best_seed#"$WORK_ROOT"/}/F" >"$CERT/best-lingen-prefix.txt.tmp"
mv "$CERT/best-lingen-prefix.txt.tmp" "$CERT/best-lingen-prefix.txt"
printf '%s\n' "$rank_report" >"$CERT/union-rank.txt"
date --iso-8601=seconds >"$CERT/AUGMENTED_CERTIFICATE_COMPLETE.tmp"
mv "$CERT/AUGMENTED_CERTIFICATE_COMPLETE.tmp" "$CERT/AUGMENTED_CERTIFICATE_COMPLETE"

echo "AUGMENTED_CERTIFICATE_COMPLETE dimension=$rows rank=$best_degree nullity=$target"
echo "The completed-matrix kernel is certified exactly; tail/W injectivity remains for the projected finisher."
