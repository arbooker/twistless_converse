#!/usr/bin/env bash

ROOT=$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
. "$ROOT/settings.sh"

require_work_root() {
    if [ -z "${N97_WORK_ROOT:-}" ]; then
        echo "ERROR: N97_WORK_ROOT is not set." >&2
        exit 1
    fi
    case $N97_WORK_ROOT in
        /*) ;;
        *) echo "ERROR: N97_WORK_ROOT must be an absolute path." >&2; exit 1 ;;
    esac
    case $N97_WORK_ROOT in
        *[[:space:],]*)
            echo "ERROR: N97_WORK_ROOT may not contain whitespace or commas." >&2
            exit 1
            ;;
    esac
    WORK_ROOT=$N97_WORK_ROOT
    MATRIX_DIR="$WORK_ROOT/matrix"
    SEED_ROOT="$WORK_ROOT/seeds"
    CORE="$MATRIX_DIR/$MATRIX_BASENAME.bin"
    SQUARE="$MATRIX_DIR/$MATRIX_BASENAME-square.bin"
}

run_timed() {
    if [ -x /usr/bin/time ]; then
        /usr/bin/time -v "$@"
    else
        "$@"
    fi
}

field_from_line() {
    key=$1
    tr ' ' '\n' | sed -n "s/^$key=//p" | tail -n 1
}

# Return comma-separated ranges aligned to CADO's 64-lane split width.
cado_ranges() {
    width=$1
    maximum=$2
    case $width in
        *[!0-9]*|'') echo "Invalid CADO solution width: $width" >&2; return 1 ;;
    esac
    case $maximum in
        *[!0-9]*|'') echo "Invalid CADO range maximum: $maximum" >&2; return 1 ;;
    esac
    if [ "$width" -lt 64 ] || [ $((width % 64)) -ne 0 ] || \
       [ "$maximum" -lt 64 ] || [ $((maximum % 64)) -ne 0 ]; then
        echo "CADO solution width must be a positive multiple of 64." >&2
        return 1
    fi
    ranges=
    start=0
    while [ "$start" -lt "$width" ]; do
        end=$((start + maximum))
        [ "$end" -le "$width" ] || end=$width
        [ -z "$ranges" ] || ranges="$ranges,"
        ranges="$ranges$start-$end"
        start=$end
    done
    printf '%s\n' "$ranges"
}

# mksol supports widths 64, 128, and 256.  Wider reconstruction reduces
# repeated sparse matrix work.  gather and cleanup require 64-lane ranges.
cado_mksol_ranges() { cado_ranges "$1" 256; }
cado_output_ranges() { cado_ranges "$1" 64; }

# Print one allocated logical CPU number per physical core.  Slurm grants both
# sibling hardware threads when --hint=nomultithread is used on BluePebble;
# pinning to the first sibling makes concurrent CADO process placement explicit.
allocated_primary_cpus() {
    command -v lscpu >/dev/null || { echo "lscpu is required." >&2; return 1; }
    command -v taskset >/dev/null || { echo "taskset is required." >&2; return 1; }
    allowed_spec=$(awk '$1 == "Cpus_allowed_list:" {print $2}' /proc/self/status)
    [ -n "$allowed_spec" ] || { echo "Could not read the allocated CPU list." >&2; return 1; }

    declare -A allowed_cpu=()
    declare -A seen_core=()
    IFS=',' read -r -a allowed_parts <<<"$allowed_spec"
    for part in "${allowed_parts[@]}"; do
        case $part in
            *-*) first=${part%-*}; last=${part#*-} ;;
            *) first=$part; last=$part ;;
        esac
        cpu=$first
        while [ "$cpu" -le "$last" ]; do
            allowed_cpu[$cpu]=1
            cpu=$((cpu + 1))
        done
    done

    while IFS=, read -r cpu core socket; do
        case $cpu in \#*|'') continue ;; esac
        [ -n "${allowed_cpu[$cpu]:-}" ] || continue
        key=$socket:$core
        [ -z "${seen_core[$key]:-}" ] || continue
        seen_core[$key]=1
        printf '%s\n' "$cpu"
    done < <(lscpu -p=CPU,CORE,SOCKET)
}

# Print one comma-separated list of allocated logical CPUs per physical core.
# With --hint=nomultithread each line has one CPU; an SMT allocation normally
# exposes both siblings on each line.
allocated_core_cpu_lists() {
    command -v lscpu >/dev/null || { echo "lscpu is required." >&2; return 1; }
    allowed_spec=$(awk '$1 == "Cpus_allowed_list:" {print $2}' /proc/self/status)
    [ -n "$allowed_spec" ] || { echo "Could not read the allocated CPU list." >&2; return 1; }

    declare -A allowed_cpu=()
    declare -A core_cpus=()
    core_order=()
    IFS=',' read -r -a allowed_parts <<<"$allowed_spec"
    for part in "${allowed_parts[@]}"; do
        case $part in
            *-*) first=${part%-*}; last=${part#*-} ;;
            *) first=$part; last=$part ;;
        esac
        cpu=$first
        while [ "$cpu" -le "$last" ]; do
            allowed_cpu[$cpu]=1
            cpu=$((cpu + 1))
        done
    done

    while IFS=, read -r cpu core socket; do
        case $cpu in \#*|'') continue ;; esac
        [ -n "${allowed_cpu[$cpu]:-}" ] || continue
        key=$socket:$core
        if [ -z "${core_cpus[$key]:-}" ]; then
            core_order+=("$key")
            core_cpus[$key]=$cpu
        else
            core_cpus[$key]="${core_cpus[$key]},$cpu"
        fi
    done < <(lscpu -p=CPU,CORE,SOCKET)

    for key in "${core_order[@]}"; do
        printf '%s\n' "${core_cpus[$key]}"
    done
}

cpu_list_slice() {
    start=$1
    count=$2
    shift 2
    cpus=("$@")
    [ $((start + count)) -le "${#cpus[@]}" ] || {
        echo "Requested CPU slice exceeds the allocation." >&2
        return 1
    }
    result=
    index=$start
    stop=$((start + count))
    while [ "$index" -lt "$stop" ]; do
        [ -z "$result" ] || result="$result,"
        result="$result${cpus[$index]}"
        index=$((index + 1))
    done
    printf '%s\n' "$result"
}
