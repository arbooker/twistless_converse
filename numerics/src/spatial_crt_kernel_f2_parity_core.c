/* Exact large-M prime-level CRT kernel/top-up engine over F_2.
 *
 * This is a non-overwriting, large-memory companion to
 * spatial_crt_kernel_f2.c.  It combines three exact reductions:
 *
 *   (1) coordinates are split by the parity of j; only the even-j block is
 *       computed, and reflection j -> Q-1-j doubles its final defect;
 *   (2) in CRT coordinates j=r+N*t, the even block in sector r has
 *       t == r (mod 2), so it has D=M/2 rather than M columns;
 *   (3) for residues r of one parity, all sector row sets contain a common
 *       core.  A sector differs from that core only by endpoint rows of the
 *       exact legal v-intervals.  The core is reduced once and copied in its
 *       final compressed form for the small endpoint updates.
 *
 * The two common cores use the compressed-RRE layout of
 * spatial_qorder_f2_parity_rre.c.  Their compact snapshots are staged before
 * the translated sector kernels are inserted into a capacity-bounded dense
 * output echelon basis.  Thus only one large compressed arena is live at a
 * time.  XOR loops are compiled to AVX2/AVX-512 by -march=native (and have
 * explicit intrinsics as a backstop); BMI2 PEXT performs pivot-column
 * compaction.
 *
 * Assumptions checked at startup:
 *   - N is an odd prime;
 *   - Q=N*M, gcd(N,M)=1, and M is even.
 *
 * Compile:
 *   gcc -std=gnu11 -O3 -march=native -mbmi2 -fopenmp \
 *       -Wall -Wextra -Werror \
 *       -o spatial_crt_kernel_f2_parity_core \
 *       spatial_crt_kernel_f2_parity_core.c
 * Usage:
 *   ./spatial_crt_kernel_f2_parity_core N Q [--estimate|--force]
 *
 * --estimate prints the staged core allocation bound and exact row-count
 * gate without allocating the large arena.  Each later allocation phase is
 * guarded from fresh MemAvailable data, always reserving 512 MiB;
 * --force overrides only those guards.
 */

#include <errno.h>
#include <immintrin.h>
#include <limits.h>
#if defined(_OPENMP)
#include <omp.h>
#endif
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t u64;
typedef int64_t i64;
typedef __int128 i128;

#define BATCH 512
#define SAFETY_RESERVE_BYTES (UINT64_C(512) << 20)

typedef struct {
    int d;
    int max_words;
    int frozen;
    int frozen_words;
    int rank;
    int last_rank;

    u64 *arena;
    size_t arena_cap_u64;
    size_t peak_used_bytes;

    int *nonpivot_cols;
    int *npidx_for_col;
    int *basis_pivots;
    int *pivot_to_row;

    u64 *new_pivot_mask;
    u64 *work_pivot_bits;
    u64 *work_nonpivot;
    u64 *repack_temp;
    u64 *drop_mask;
    int *drop;
} Crref;

typedef struct {
    int d;
    int rank;
    int nullity;
    int words;
    u64 *arena;
    int *nonpivot_cols;
    int *npidx_for_col;
    int *basis_pivots;
    int *pivot_to_row;
} Snapshot;

typedef struct {
    int d;
    int words;
    int capacity;
    int rank;
    u64 *rows;
    int *pivots;
    int *pivot_to_row;
} DenseOutput;

typedef struct {
    int q;
    int count;
    int *values;
    int h;
} DivisorData;

static void die(const char *message) {
    fprintf(stderr, "%s\n", message);
    exit(EXIT_FAILURE);
}

static void *xcalloc(size_t count, size_t size) {
    if (size != 0 && count > SIZE_MAX / size)
        die("allocation-size overflow");
    void *result = calloc(count, size);
    if (!result && count != 0 && size != 0)
        die("out of memory");
    return result;
}

static void *xmalloc(size_t size) {
    void *result = malloc(size);
    if (!result && size != 0)
        die("out of memory");
    return result;
}

static int parse_positive_int(const char *text, const char *name) {
    char *end = NULL;
    errno = 0;
    long value = strtol(text, &end, 10);
    if (errno != 0 || end == text || *end != '\0' || value <= 0 ||
        value > INT_MAX) {
        fprintf(stderr, "%s must be an integer in [1,%d]\n", name, INT_MAX);
        exit(EXIT_FAILURE);
    }
    return (int)value;
}

static int gcd_int(int a, int b) {
    while (b != 0) {
        int next = a % b;
        a = b;
        b = next;
    }
    return a < 0 ? -a : a;
}

static int is_odd_prime(int n) {
    if (n < 3 || (n & 1) == 0)
        return 0;
    for (int p = 3; p <= n / p; p += 2)
        if (n % p == 0)
            return 0;
    return 1;
}

static int inverse_mod(int a, int modulus) {
    i64 old_r = a;
    i64 r = modulus;
    i64 old_s = 1;
    i64 s = 0;
    while (r != 0) {
        i64 quotient = old_r / r;
        i64 next_r = old_r - quotient * r;
        i64 next_s = old_s - quotient * s;
        old_r = r;
        r = next_r;
        old_s = s;
        s = next_s;
    }
    if (old_r != 1)
        die("internal error: modular inverse does not exist");
    i64 answer = old_s % modulus;
    if (answer < 0)
        answer += modulus;
    return (int)answer;
}

static i64 floor_div(i64 numerator, i64 denominator) {
    i64 quotient = numerator / denominator;
    i64 remainder = numerator % denominator;
    if (remainder < 0)
        quotient--;
    return quotient;
}

static i64 ceil_div(i64 numerator, i64 denominator) {
    return -floor_div(-numerator, denominator);
}

static int positive_mod_i64(i64 value, int modulus) {
    i64 result = value % modulus;
    if (result < 0)
        result += modulus;
    return (int)result;
}

/* h=min{h>=0:h^2 q^2 >= M^2 N}; exact in 128-bit arithmetic. */
static int buffered_radius(int n_level, int multiplier, int q,
                           int q_total) {
    i128 target = (i128)multiplier * multiplier * n_level;
    i128 q_squared = (i128)q * q;
    int low = 0;
    int high = q_total / q;
    if (q_total % q != 0)
        high++;
    while (low < high) {
        int middle = low + (high - low) / 2;
        if ((i128)middle * middle * q_squared >= target)
            high = middle;
        else
            low = middle + 1;
    }
    return low;
}

static int compare_ints(const void *left, const void *right) {
    int a = *(const int *)left;
    int b = *(const int *)right;
    return (a > b) - (a < b);
}

static int *make_divisors(int n, int *count_out) {
    int count = 0;
    for (int d = 1; d <= n / d; d++) {
        if (n % d == 0)
            count += (d == n / d) ? 1 : 2;
    }
    int *divisors = xmalloc((size_t)count * sizeof(*divisors));
    int at = 0;
    for (int d = 1; d <= n / d; d++) {
        if (n % d != 0)
            continue;
        divisors[at++] = d;
        if (d != n / d)
            divisors[at++] = n / d;
    }
    qsort(divisors, (size_t)count, sizeof(*divisors), compare_ints);
    *count_out = count;
    return divisors;
}

static uint64_t available_memory_bytes(void) {
    FILE *file = fopen("/proc/meminfo", "r");
    if (!file)
        return 0;
    char label[64];
    unsigned long long kib = 0;
    char unit[32];
    uint64_t answer = 0;
    while (fscanf(file, "%63s %llu %31s", label, &kib, unit) == 3) {
        if (strcmp(label, "MemAvailable:") == 0) {
            answer = (uint64_t)kib << 10;
            break;
        }
    }
    fclose(file);
    return answer;
}

static void guard_additional_allocation(uint64_t bytes, int force,
                                        const char *label) {
    uint64_t available = available_memory_bytes();
    if (!force && available != 0 &&
        bytes + SAFETY_RESERVE_BYTES > (available / 4) * 3) {
        fprintf(stderr,
                "refusing %s: %.3f GiB allocation plus reserve exceeds "
                "75%% of %.3f GiB MemAvailable\n",
                label,
                (double)bytes / (double)(UINT64_C(1) << 30),
                (double)available / (double)(UINT64_C(1) << 30));
        exit(EXIT_FAILURE);
    }
}

static uint64_t crref_auxiliary_bytes(int d) {
    int words = (d + 63) / 64;
    return UINT64_C(4) * (uint64_t)d * sizeof(int) +
           UINT64_C(5) * (uint64_t)words * sizeof(u64) +
           (uint64_t)BATCH * sizeof(int);
}

static size_t compressed_arena_u64(int d) {
    size_t maximum = 0;
    int max_words = (d + 63) / 64;
    for (int k = 1; (i64)(k - 1) * BATCH <= d; k++) {
        int rank = k * BATCH;
        if (rank > d)
            rank = d;
        int remaining = d - (k - 1) * BATCH;
        if (remaining < 0)
            remaining = 0;
        int words = (remaining + 63) / 64;
        size_t needed = (size_t)rank * words;
        if (needed > maximum)
            maximum = needed;
        if (rank == d)
            break;
    }
    maximum += (size_t)BATCH * max_words;
    return maximum;
}

static inline void xor_words(u64 *restrict destination,
                             const u64 *restrict source, int words) {
    int word = 0;
#if defined(__AVX512F__)
    for (; word + 8 <= words; word += 8) {
        __m512i a = _mm512_loadu_si512((const void *)(destination + word));
        __m512i b = _mm512_loadu_si512((const void *)(source + word));
        _mm512_storeu_si512((void *)(destination + word),
                            _mm512_xor_si512(a, b));
    }
#elif defined(__AVX2__)
    for (; word + 4 <= words; word += 4) {
        __m256i a = _mm256_loadu_si256((const __m256i *)(destination + word));
        __m256i b = _mm256_loadu_si256((const __m256i *)(source + word));
        _mm256_storeu_si256((__m256i *)(destination + word),
                            _mm256_xor_si256(a, b));
    }
#endif
    for (; word < words; word++)
        destination[word] ^= source[word];
}

static inline int first_bit_from(const u64 *row, int start, int words,
                                 int limit) {
    int first_word = start >> 6;
    if (first_word >= words)
        return -1;
    u64 value = row[first_word] & (~UINT64_C(0) << (start & 63));
    if (value != 0) {
        int bit = 64 * first_word + __builtin_ctzll(value);
        return bit < limit ? bit : -1;
    }
    for (int word = first_word + 1; word < words; word++) {
        if (row[word] != 0) {
            int bit = 64 * word + __builtin_ctzll(row[word]);
            return bit < limit ? bit : -1;
        }
    }
    return -1;
}

static DenseOutput dense_output_create(int d, int capacity) {
    if (capacity < 0 || capacity > d)
        die("invalid dense-output capacity");
    DenseOutput result;
    result.d = d;
    result.words = (d + 63) / 64;
    result.capacity = capacity;
    result.rank = 0;
    result.rows =
        xcalloc((size_t)capacity * result.words, sizeof(u64));
    result.pivots = xmalloc((size_t)capacity * sizeof(int));
    result.pivot_to_row = xmalloc((size_t)d * sizeof(int));
    for (int column = 0; column < d; column++)
        result.pivot_to_row[column] = -1;
    return result;
}

static void dense_output_destroy(DenseOutput *basis) {
    free(basis->rows);
    free(basis->pivots);
    free(basis->pivot_to_row);
    memset(basis, 0, sizeof(*basis));
}

static int dense_output_insert(DenseOutput *basis, u64 *work) {
    int start = 0;
    for (;;) {
        int pivot = first_bit_from(work, start, basis->words, basis->d);
        if (pivot < 0)
            return 0;
        int row_index = basis->pivot_to_row[pivot];
        if (row_index < 0) {
            if (basis->rank >= basis->capacity)
                die("dense-output capacity exhausted");
            u64 *destination =
                basis->rows + (size_t)basis->rank * basis->words;
            memcpy(destination, work,
                   (size_t)basis->words * sizeof(u64));
            basis->pivots[basis->rank] = pivot;
            basis->pivot_to_row[pivot] = basis->rank;
            basis->rank++;
            return 1;
        }
        const u64 *source =
            basis->rows + (size_t)row_index * basis->words;
        xor_words(work + (pivot >> 6), source + (pivot >> 6),
                  basis->words - (pivot >> 6));
        start = pivot + 1;
    }
}

static inline int first_bit(const u64 *buffer, int words, int limit) {
    for (int word = 0; word < words; word++) {
        if (buffer[word] != 0) {
            int bit = 64 * word + __builtin_ctzll(buffer[word]);
            return bit < limit ? bit : -1;
        }
    }
    return -1;
}

static inline int first_bit_and(const u64 *left, const u64 *right,
                                int words, int limit) {
    for (int word = 0; word < words; word++) {
        u64 value = left[word] & right[word];
        if (value != 0) {
            int bit = 64 * word + __builtin_ctzll(value);
            return bit < limit ? bit : -1;
        }
    }
    return -1;
}

static Crref crref_create(int d, size_t arena_cap_u64) {
    Crref result;
    memset(&result, 0, sizeof(result));
    result.d = d;
    result.max_words = (d + 63) / 64;
    result.frozen = d;
    result.frozen_words = result.max_words;
    result.arena_cap_u64 = arena_cap_u64;
    result.arena = xcalloc(arena_cap_u64, sizeof(u64));
    result.nonpivot_cols = xmalloc((size_t)d * sizeof(int));
    result.npidx_for_col = xmalloc((size_t)d * sizeof(int));
    result.basis_pivots = xmalloc((size_t)d * sizeof(int));
    result.pivot_to_row = xmalloc((size_t)d * sizeof(int));
    result.new_pivot_mask = xcalloc((size_t)result.max_words, sizeof(u64));
    result.work_pivot_bits = xcalloc((size_t)result.max_words, sizeof(u64));
    result.work_nonpivot = xcalloc((size_t)result.max_words, sizeof(u64));
    result.repack_temp = xcalloc((size_t)result.max_words, sizeof(u64));
    result.drop_mask = xcalloc((size_t)result.max_words, sizeof(u64));
    result.drop = xmalloc((size_t)BATCH * sizeof(int));
    for (int column = 0; column < d; column++) {
        result.nonpivot_cols[column] = column;
        result.npidx_for_col[column] = column;
        result.pivot_to_row[column] = -1;
    }
    return result;
}

static void crref_destroy(Crref *basis) {
    free(basis->arena);
    free(basis->nonpivot_cols);
    free(basis->npidx_for_col);
    free(basis->basis_pivots);
    free(basis->pivot_to_row);
    free(basis->new_pivot_mask);
    free(basis->work_pivot_bits);
    free(basis->work_nonpivot);
    free(basis->repack_temp);
    free(basis->drop_mask);
    free(basis->drop);
    memset(basis, 0, sizeof(*basis));
}

static void crref_zero_work(Crref *basis) {
    memset(basis->work_pivot_bits, 0,
           (size_t)basis->max_words * sizeof(u64));
    memset(basis->work_nonpivot, 0,
           (size_t)basis->frozen_words * sizeof(u64));
}

static void crref_toggle_global(Crref *basis, int column) {
    int npidx = basis->npidx_for_col[column];
    if (npidx >= 0)
        basis->work_nonpivot[npidx >> 6] ^=
            UINT64_C(1) << (npidx & 63);
    else
        basis->work_pivot_bits[column >> 6] ^=
            UINT64_C(1) << (column & 63);
}

static inline void crref_xor_into_work(Crref *basis, int row_index) {
    const u64 *source =
        basis->arena + (size_t)row_index * basis->frozen_words;
    xor_words(basis->work_nonpivot, source, basis->frozen_words);
}

static inline void crref_xor_rows(Crref *basis, int destination_index,
                                  int source_index) {
    u64 *destination =
        basis->arena + (size_t)destination_index * basis->frozen_words;
    const u64 *source =
        basis->arena + (size_t)source_index * basis->frozen_words;
    xor_words(destination, source, basis->frozen_words);
}

/* Reduce work by every existing pivot.  Absorbed pivot bits are immutable
 * during this reduction, because compacted rows contain only nonpivot
 * coordinates, so they can be traversed wordwise once. */
static int crref_reduce_work(Crref *basis, int *npidx_out) {
    for (int word = 0; word < basis->max_words; word++) {
        u64 remaining = basis->work_pivot_bits[word];
        while (remaining != 0) {
            int bit = __builtin_ctzll(remaining);
            int pivot = 64 * word + bit;
            if (pivot >= basis->d)
                die("internal pivot bit beyond dimension");
            int row_index = basis->pivot_to_row[pivot];
            if (row_index < 0)
                die("internal missing absorbed pivot");
            crref_xor_into_work(basis, row_index);
            remaining &= remaining - 1;
        }
        basis->work_pivot_bits[word] = 0;
    }

    int npidx;
    while ((npidx = first_bit_and(basis->work_nonpivot,
                                  basis->new_pivot_mask,
                                  basis->frozen_words,
                                  basis->frozen)) >= 0) {
        int pivot = basis->nonpivot_cols[npidx];
        int row_index = basis->pivot_to_row[pivot];
        if (row_index < 0)
            die("internal missing current-epoch pivot");
        crref_xor_into_work(basis, row_index);
    }

    npidx = first_bit(basis->work_nonpivot, basis->frozen_words,
                      basis->frozen);
    if (npidx < 0)
        return -1;
    if (npidx_out)
        *npidx_out = npidx;
    return basis->nonpivot_cols[npidx];
}

static int crref_append(Crref *basis, int pivot, int npidx) {
    size_t needed = (size_t)(basis->rank + 1) * basis->frozen_words;
    if (needed > basis->arena_cap_u64) {
        fprintf(stderr,
                "compressed arena exhausted: rank=%d words=%d need=%zu "
                "capacity=%zu\n",
                basis->rank, basis->frozen_words, needed,
                basis->arena_cap_u64);
        return 0;
    }
    u64 *destination =
        basis->arena + (size_t)basis->rank * basis->frozen_words;
    memcpy(destination, basis->work_nonpivot,
           (size_t)basis->frozen_words * sizeof(u64));
    basis->basis_pivots[basis->rank] = pivot;
    basis->pivot_to_row[pivot] = basis->rank;
    basis->new_pivot_mask[npidx >> 6] |=
        UINT64_C(1) << (npidx & 63);
    basis->rank++;
    size_t used = needed * sizeof(u64);
    if (used > basis->peak_used_bytes)
        basis->peak_used_bytes = used;
    return 1;
}

#if !defined(__BMI2__)
static u64 compress_bits_fallback(u64 value, u64 mask) {
    u64 result = 0;
    unsigned int output = 0;
    while (mask != 0) {
        int bit = __builtin_ctzll(mask);
        if ((value >> bit) & UINT64_C(1))
            result |= UINT64_C(1) << output;
        output++;
        mask &= mask - 1;
    }
    return result;
}
#endif

static inline u64 compress_bits(u64 value, u64 mask) {
#if defined(__BMI2__)
    return _pext_u64(value, mask);
#else
    return compress_bits_fallback(value, mask);
#endif
}

static void crref_compact(Crref *basis) {
    int new_count = basis->rank - basis->last_rank;
    if (new_count == 0)
        return;

#if defined(_OPENMP)
    if (basis->rank >= 8192 && basis->frozen_words >= 64) {
#pragma omp parallel
        {
            /* Every source_index is completed before the next begins.  For
             * one source the destination rows are disjoint, while the source
             * itself is read-only.  The implicit omp-for barrier preserves
             * the sequential back-substitution dependence between sources. */
            for (int source_index = basis->last_rank;
                 source_index < basis->rank; source_index++) {
                int pivot = basis->basis_pivots[source_index];
                int npidx = basis->npidx_for_col[pivot];
                int word = npidx >> 6;
                u64 mask = UINT64_C(1) << (npidx & 63);
#pragma omp for schedule(static)
                for (int destination_index = 0;
                     destination_index < basis->rank; destination_index++) {
                    if (destination_index == source_index)
                        continue;
                    u64 *row = basis->arena +
                               (size_t)destination_index *
                                   basis->frozen_words;
                    if (row[word] & mask)
                        crref_xor_rows(basis, destination_index,
                                       source_index);
                }
            }
        }
    } else
#endif
    {
        for (int source_index = basis->last_rank;
             source_index < basis->rank; source_index++) {
            int pivot = basis->basis_pivots[source_index];
            int npidx = basis->npidx_for_col[pivot];
            int word = npidx >> 6;
            u64 mask = UINT64_C(1) << (npidx & 63);
            for (int destination_index = 0;
                 destination_index < basis->rank; destination_index++) {
                if (destination_index == source_index)
                    continue;
                u64 *row = basis->arena +
                           (size_t)destination_index * basis->frozen_words;
                if (row[word] & mask)
                    crref_xor_rows(basis, destination_index, source_index);
            }
        }
    }

    if (new_count > BATCH)
        die("internal compaction batch overflow");
    memset(basis->drop_mask, 0,
           (size_t)basis->frozen_words * sizeof(u64));
    for (int index = 0; index < new_count; index++)
        basis->drop[index] =
            basis->npidx_for_col[
                basis->basis_pivots[basis->last_rank + index]];
    qsort(basis->drop, (size_t)new_count, sizeof(int), compare_ints);
    for (int index = 0; index < new_count; index++)
        basis->drop_mask[basis->drop[index] >> 6] |=
            UINT64_C(1) << (basis->drop[index] & 63);

    int new_frozen = basis->frozen - new_count;
    int new_words = (new_frozen + 63) / 64;
    for (int row_index = 0; row_index < basis->rank; row_index++) {
        u64 *row =
            basis->arena + (size_t)row_index * basis->frozen_words;
        memset(basis->repack_temp, 0, (size_t)new_words * sizeof(u64));
        int output_bits = 0;
        for (int word = 0; word < basis->frozen_words; word++) {
            u64 keep = ~basis->drop_mask[word];
            if (word == basis->frozen_words - 1) {
                int valid_bits = basis->frozen - 64 * word;
                if (valid_bits < 64)
                    keep &= valid_bits == 0
                                ? 0
                                : (UINT64_C(1) << valid_bits) - 1;
            }
            int kept = __builtin_popcountll(keep);
            if (kept == 0)
                continue;
            u64 extracted = compress_bits(row[word], keep);
            int output_word = output_bits >> 6;
            int output_offset = output_bits & 63;
            if (new_words > 0)
                basis->repack_temp[output_word] |=
                    extracted << output_offset;
            if (output_offset != 0 && output_offset + kept > 64 &&
                output_word + 1 < new_words)
                basis->repack_temp[output_word + 1] |=
                    extracted >> (64 - output_offset);
            output_bits += kept;
        }
        u64 *new_row =
            basis->arena + (size_t)row_index * new_words;
        if (new_words > 0)
            memcpy(new_row, basis->repack_temp,
                   (size_t)new_words * sizeof(u64));
    }

    int dropped = 0;
    int output = 0;
    for (int input = 0; input < basis->frozen; input++) {
        if (dropped < new_count && input == basis->drop[dropped])
            dropped++;
        else
            basis->nonpivot_cols[output++] =
                basis->nonpivot_cols[input];
    }
    for (int index = 0; index < new_count; index++)
        basis->npidx_for_col[
            basis->basis_pivots[basis->last_rank + index]] = -1;
    for (int index = 0; index < new_frozen; index++)
        basis->npidx_for_col[basis->nonpivot_cols[index]] = index;

    memset(basis->new_pivot_mask, 0,
           (size_t)basis->max_words * sizeof(u64));
    basis->frozen = new_frozen;
    basis->frozen_words = new_words;
    basis->last_rank = basis->rank;
}

static int crref_insert_current_work(Crref *basis) {
    int npidx = -1;
    int pivot = crref_reduce_work(basis, &npidx);
    if (pivot < 0)
        return 0;
    if (!crref_append(basis, pivot, npidx))
        die("compressed basis capacity calculation failed");
    if (basis->rank - basis->last_rank >= BATCH)
        crref_compact(basis);
    return 1;
}

static Snapshot snapshot_from_crref(Crref *basis) {
    crref_compact(basis);
    Snapshot result;
    result.d = basis->d;
    result.rank = basis->rank;
    result.nullity = basis->frozen;
    result.words = basis->frozen_words;
    size_t arena_u64 = (size_t)result.rank * result.words;
    result.arena = xmalloc(arena_u64 * sizeof(u64));
    if (arena_u64 > 0)
        memcpy(result.arena, basis->arena, arena_u64 * sizeof(u64));
    result.nonpivot_cols =
        xmalloc((size_t)result.nullity * sizeof(int));
    if (result.nullity > 0)
        memcpy(result.nonpivot_cols, basis->nonpivot_cols,
               (size_t)result.nullity * sizeof(int));
    result.npidx_for_col = xmalloc((size_t)result.d * sizeof(int));
    result.basis_pivots = xmalloc((size_t)result.rank * sizeof(int));
    result.pivot_to_row = xmalloc((size_t)result.d * sizeof(int));
    memcpy(result.npidx_for_col, basis->npidx_for_col,
           (size_t)result.d * sizeof(int));
    memcpy(result.basis_pivots, basis->basis_pivots,
           (size_t)result.rank * sizeof(int));
    memcpy(result.pivot_to_row, basis->pivot_to_row,
           (size_t)result.d * sizeof(int));
    return result;
}

static uint64_t snapshot_storage_bytes(int d, int rank, int nullity) {
    int words = (nullity + 63) / 64;
    return (uint64_t)rank * (uint64_t)words * sizeof(u64) +
           (uint64_t)nullity * sizeof(int) +
           (uint64_t)d * sizeof(int) +
           (uint64_t)rank * sizeof(int) +
           (uint64_t)d * sizeof(int);
}

static size_t restored_sector_arena_u64(const Snapshot *snapshot,
                                        int maximum_extra_rank) {
    int maximum_words = (snapshot->d + 63) / 64;
    size_t capacity =
        (size_t)(snapshot->rank + maximum_extra_rank + 1) *
        (size_t)(snapshot->words > 0 ? snapshot->words : 1);
    capacity += (size_t)BATCH * maximum_words;
    return capacity;
}

static void snapshot_destroy(Snapshot *snapshot) {
    free(snapshot->arena);
    free(snapshot->nonpivot_cols);
    free(snapshot->npidx_for_col);
    free(snapshot->basis_pivots);
    free(snapshot->pivot_to_row);
    memset(snapshot, 0, sizeof(*snapshot));
}

static Crref crref_from_snapshot(const Snapshot *snapshot,
                                 int maximum_extra_rank) {
    size_t capacity =
        restored_sector_arena_u64(snapshot, maximum_extra_rank);
    Crref result = crref_create(snapshot->d, capacity);
    result.rank = snapshot->rank;
    result.last_rank = snapshot->rank;
    result.frozen = snapshot->nullity;
    result.frozen_words = snapshot->words;
    size_t arena_u64 = (size_t)snapshot->rank * snapshot->words;
    if (arena_u64 > 0)
        memcpy(result.arena, snapshot->arena, arena_u64 * sizeof(u64));
    if (snapshot->nullity > 0)
        memcpy(result.nonpivot_cols, snapshot->nonpivot_cols,
               (size_t)snapshot->nullity * sizeof(int));
    memcpy(result.npidx_for_col, snapshot->npidx_for_col,
           (size_t)snapshot->d * sizeof(int));
    memcpy(result.basis_pivots, snapshot->basis_pivots,
           (size_t)snapshot->rank * sizeof(int));
    memcpy(result.pivot_to_row, snapshot->pivot_to_row,
           (size_t)snapshot->d * sizeof(int));
    result.peak_used_bytes = arena_u64 * sizeof(u64);
    return result;
}

static int selected_v_parity(int residue_parity, int step) {
    return residue_parity ^ (step & 1);
}

static i64 first_with_parity(i64 lower, int parity) {
    if ((lower & 1) != parity)
        lower++;
    return lower;
}

/* Build the even-j row in the D=M/2 compressed coordinates. */
static void build_row(Crref *basis, int multiplier, int residue_parity,
                      const DivisorData *divisor, i64 v) {
    crref_zero_work(basis);
    int step = multiplier / divisor->q;
    for (int index = 0; index < divisor->count; index++) {
        int a = divisor->values[index];
        int t = positive_mod_i64(v + (i64)a * step, multiplier);
        if (((t + residue_parity) & 1) != 0)
            die("internal parity error in compressed CRT row");
        int column = (t - residue_parity) / 2;
        crref_toggle_global(basis, column);
    }
}

static void legal_interval(int n_level, int residue, int h,
                           i64 *lower, i64 *upper) {
    *lower = ceil_div(1 - (i64)h - residue, n_level);
    *upper = floor_div((i64)h - 2 - residue, n_level);
}

static void core_interval(int n_level, int residue_parity, int h,
                          i64 *lower, i64 *upper) {
    int first_residue = residue_parity;
    int last_residue = n_level - 1;
    if ((last_residue & 1) != residue_parity)
        last_residue--;
    i64 unused_upper;
    i64 unused_lower;
    /* Both endpoints decrease with r.  Hence the largest lower endpoint
     * occurs at the first residue and the smallest upper endpoint at the
     * last residue. */
    legal_interval(n_level, first_residue, h, lower, &unused_upper);
    legal_interval(n_level, last_residue, h, &unused_lower, upper);
}

static i64 count_selected(i64 lower, i64 upper, int parity) {
    i64 first = first_with_parity(lower, parity);
    if (first > upper)
        return 0;
    return (upper - first) / 2 + 1;
}

static int count_sector_exceptions(int n_level, int multiplier,
                                   int residue, const DivisorData *data,
                                   int divisor_count) {
    int residue_parity = residue & 1;
    i64 count = 0;
    for (int index = 0; index < divisor_count; index++) {
        int step = multiplier / data[index].q;
        int parity = selected_v_parity(residue_parity, step);
        i64 lower;
        i64 upper;
        i64 core_lower;
        i64 core_upper;
        legal_interval(n_level, residue, data[index].h, &lower, &upper);
        core_interval(n_level, residue_parity, data[index].h,
                      &core_lower, &core_upper);
        count += count_selected(lower, core_lower - 1, parity);
        count += count_selected(core_upper + 1, upper, parity);
    }
    if (count > INT_MAX)
        die("too many endpoint rows for int indexing");
    return (int)count;
}

static i64 build_common_core(Crref *core, int n_level, int multiplier,
                             int residue_parity, const DivisorData *data,
                             int divisor_count) {
    i64 rows = 0;
    i64 next_report = 50000;
    for (int index = 0; index < divisor_count; index++) {
        int step = multiplier / data[index].q;
        int parity = selected_v_parity(residue_parity, step);
        i64 lower;
        i64 upper;
        core_interval(n_level, residue_parity, data[index].h,
                      &lower, &upper);
        for (i64 v = first_with_parity(lower, parity); v <= upper; v += 2) {
            build_row(core, multiplier, residue_parity, &data[index], v);
            (void)crref_insert_current_work(core);
            rows++;
            if (rows >= next_report) {
                printf("core parity=%d progress rows=%lld rank=%d/%d "
                       "nullity=%d peak_basis=%zu\n",
                       residue_parity, (long long)rows, core->rank,
                       core->d, core->d - core->rank,
                       core->peak_used_bytes);
                fflush(stdout);
                next_report += 50000;
            }
        }
    }
    crref_compact(core);
    return rows;
}

static int add_sector_exceptions(Crref *sector, int n_level, int multiplier,
                                 int residue, const DivisorData *data,
                                 int divisor_count) {
    int residue_parity = residue & 1;
    int rows = 0;
    for (int index = 0; index < divisor_count; index++) {
        int step = multiplier / data[index].q;
        int parity = selected_v_parity(residue_parity, step);
        i64 lower;
        i64 upper;
        i64 core_lower;
        i64 core_upper;
        legal_interval(n_level, residue, data[index].h, &lower, &upper);
        core_interval(n_level, residue_parity, data[index].h,
                      &core_lower, &core_upper);
        i64 left_upper = core_lower - 1;
        for (i64 v = first_with_parity(lower, parity);
             v <= left_upper && v <= upper; v += 2) {
            build_row(sector, multiplier, residue_parity, &data[index], v);
            (void)crref_insert_current_work(sector);
            rows++;
        }
        i64 right_lower = core_upper + 1;
        if (right_lower < lower)
            right_lower = lower;
        for (i64 v = first_with_parity(right_lower, parity);
             v <= upper; v += 2) {
            build_row(sector, multiplier, residue_parity, &data[index], v);
            (void)crref_insert_current_work(sector);
            rows++;
        }
    }
    crref_compact(sector);
    return rows;
}

/* Insert the translate of one sector-kernel basis vector into output.
 * The final sector RREF expresses a free coordinate plus those pivot
 * coordinates whose stored row has the corresponding free bit. */
static void insert_kernel_column(DenseOutput *output, u64 *output_work,
                                 const Crref *sector, int free_index,
                                 int shift) {
    memset(output_work, 0, (size_t)output->words * sizeof(u64));
    int free_column = sector->nonpivot_cols[free_index];
    int translated = free_column + shift;
    if (translated >= output->d)
        translated -= output->d;
    output_work[translated >> 6] ^=
        UINT64_C(1) << (translated & 63);

    int word = free_index >> 6;
    u64 mask = UINT64_C(1) << (free_index & 63);
    for (int row_index = 0; row_index < sector->rank; row_index++) {
        const u64 *row =
            sector->arena + (size_t)row_index * sector->frozen_words;
        if ((row[word] & mask) == 0)
            continue;
        int column = sector->basis_pivots[row_index] + shift;
        if (column >= output->d)
            column -= output->d;
        output_work[column >> 6] ^= UINT64_C(1) << (column & 63);
    }
    (void)dense_output_insert(output, output_work);
}

int main(int argc, char **argv) {
    if (argc < 3 || argc > 4) {
        fprintf(stderr, "Usage: %s N Q [--estimate|--force]\n", argv[0]);
        return EXIT_FAILURE;
    }
    int estimate_only = 0;
    int force = 0;
    if (argc == 4) {
        if (strcmp(argv[3], "--estimate") == 0)
            estimate_only = 1;
        else if (strcmp(argv[3], "--force") == 0)
            force = 1;
        else {
            fprintf(stderr, "unknown option: %s\n", argv[3]);
            return EXIT_FAILURE;
        }
    }

    int n_level = parse_positive_int(argv[1], "N");
    int q_total = parse_positive_int(argv[2], "Q");
    if (!is_odd_prime(n_level))
        die("require N to be an odd prime");
    if (q_total % n_level != 0)
        die("require N|Q");
    int multiplier = q_total / n_level;
    if (gcd_int(n_level, multiplier) != 1)
        die("require gcd(N,Q/N)=1");
    if ((multiplier & 1) != 0)
        die("require even M=Q/N");
    int d = multiplier / 2;

    int divisor_count = 0;
    int *divisors = make_divisors(multiplier, &divisor_count);
    DivisorData *data = xcalloc((size_t)divisor_count, sizeof(*data));
    i64 expected_full_rows = 0;
    for (int index = 0; index < divisor_count; index++) {
        int q = divisors[index];
        data[index].q = q;
        data[index].values = xmalloc((size_t)q * sizeof(int));
        for (int a = 0; a < q; a++)
            if (gcd_int(a, q) == 1)
                data[index].values[data[index].count++] = a;
        data[index].h = buffered_radius(n_level, multiplier, q, q_total);
        expected_full_rows += 2 * (i64)data[index].h - 2;
    }

    size_t arena_u64 = compressed_arena_u64(d);
    uint64_t one_arena_bytes = (uint64_t)arena_u64 * sizeof(u64);
    uint64_t core_stage_bytes =
        one_arena_bytes + crref_auxiliary_bytes(d);
    uint64_t available = available_memory_bytes();
    i64 equation_margin = expected_full_rows + multiplier - (i64)q_total;
    printf("N=%d M=%d Q=%d parity_columns=%d divisors=%d "
           "full_coprime_rows=%lld equation_margin_after_W=%lld\n",
           n_level, multiplier, q_total, d, divisor_count,
           (long long)expected_full_rows, (long long)equation_margin);
    printf("MEMORY one_compressed_arena=%llu_bytes=%.3f_GiB "
           "staged_core_plus_reserve=%llu_bytes=%.3f_GiB "
           "MemAvailable=%.3f_GiB\n",
           (unsigned long long)one_arena_bytes,
           (double)one_arena_bytes / (double)(UINT64_C(1) << 30),
           (unsigned long long)(core_stage_bytes + SAFETY_RESERVE_BYTES),
           (double)(core_stage_bytes + SAFETY_RESERVE_BYTES) /
               (double)(UINT64_C(1) << 30),
           (double)available / (double)(UINT64_C(1) << 30));
    if (equation_margin < 0) {
        printf("DIMENSION_OBSTRUCTION shortfall=%lld; no elimination run\n",
               (long long)-equation_margin);
        estimate_only = 1;
    }
    if (estimate_only)
        goto cleanup_data;

    int inverse_n = inverse_mod(n_level % multiplier, multiplier);
    if ((inverse_n & 1) == 0)
        die("internal error: inverse of odd N modulo even M is not odd");

    Snapshot snapshots[2];
    memset(snapshots, 0, sizeof(snapshots));
    size_t peak_core_bytes = 0;

    /* Stage both common-core snapshots first.  The first snapshot is tiny
     * when the common core is nearly full rank, and its resident pages are
     * reflected in the fresh MemAvailable guard before the second core. */
    for (int residue_parity = 0; residue_parity <= 1;
         residue_parity++) {
        guard_additional_allocation(core_stage_bytes, force,
                                    "compressed common core");
        Crref core = crref_create(d, arena_u64);
        i64 core_rows = build_common_core(&core, n_level, multiplier,
                                          residue_parity, data,
                                          divisor_count);
        if (core.peak_used_bytes > peak_core_bytes)
            peak_core_bytes = core.peak_used_bytes;
        uint64_t snapshot_bytes = snapshot_storage_bytes(
            d, core.rank, core.frozen);
        guard_additional_allocation(snapshot_bytes, force,
                                    "compact common-core snapshot");
        snapshots[residue_parity] = snapshot_from_crref(&core);
        printf("core parity=%d rows=%lld rank=%d/%d nullity=%d "
               "peak_basis=%zu snapshot=%llu_bytes\n",
               residue_parity, (long long)core_rows, core.rank, d,
               core.frozen, core.peak_used_bytes,
               (unsigned long long)snapshot_bytes);
        fflush(stdout);
        crref_destroy(&core);
    }

    i64 output_capacity_i64 =
        (i64)((n_level + 1) / 2) * snapshots[0].nullity +
        (i64)((n_level - 1) / 2) * snapshots[1].nullity;
    if (output_capacity_i64 > d)
        output_capacity_i64 = d;
    int output_capacity = (int)output_capacity_i64;
    int output_words = (d + 63) / 64;
    uint64_t output_bytes =
        (uint64_t)output_capacity * output_words * sizeof(u64) +
        (uint64_t)output_capacity * sizeof(int) +
        (uint64_t)d * sizeof(int);
    uint64_t maximum_sector_bytes = 0;
    for (int residue = 0; residue < n_level; residue++) {
        int residue_parity = residue & 1;
        int exceptions = count_sector_exceptions(
            n_level, multiplier, residue, data, divisor_count);
        uint64_t sector_bytes =
            (uint64_t)restored_sector_arena_u64(
                &snapshots[residue_parity], exceptions) *
                sizeof(u64) +
            crref_auxiliary_bytes(d);
        if (sector_bytes > maximum_sector_bytes)
            maximum_sector_bytes = sector_bytes;
    }
    uint64_t output_work_bytes =
        (uint64_t)output_words * sizeof(u64);
    /* These allocations coexist.  Guard their sum before calloc so lazy
     * page commitment cannot hide a later unsafe peak. */
    guard_additional_allocation(output_bytes + maximum_sector_bytes +
                                    output_work_bytes,
                                force,
                                "output plus restored-sector storage");
    DenseOutput output = dense_output_create(d, output_capacity);
    u64 *output_work = xcalloc((size_t)output_words, sizeof(u64));
    printf("OUTPUT capacity=%d/%d allocation=%llu_bytes=%.3f_GiB "
           "max_restored_sector=%.3f_GiB\n",
           output_capacity, d, (unsigned long long)output_bytes,
           (double)output_bytes / (double)(UINT64_C(1) << 30),
           (double)maximum_sector_bytes /
               (double)(UINT64_C(1) << 30));
    fflush(stdout);

    i64 total_even_rows = 0;
    i64 total_even_kernel = 0;
    size_t peak_sector_bytes = 0;

    for (int residue_parity = 0; residue_parity <= 1;
         residue_parity++) {
        const Snapshot *snapshot = &snapshots[residue_parity];

        for (int residue = residue_parity; residue < n_level; residue += 2) {
            int exceptions = count_sector_exceptions(
                n_level, multiplier, residue, data, divisor_count);
            Crref sector =
                crref_from_snapshot(snapshot, exceptions);
            int added_rows = add_sector_exceptions(
                &sector, n_level, multiplier, residue, data, divisor_count);
            if (added_rows != exceptions)
                die("internal endpoint-row count mismatch");
            int kernel_dimension = sector.frozen;
            int old_output_rank = output.rank;
            i64 numerator = (i64)(residue & 1) +
                            (i64)inverse_n * residue;
            if (numerator & 1)
                die("internal half-shift is not integral");
            int shift = positive_mod_i64(numerator / 2, d);
            for (int free_index = 0; free_index < kernel_dimension;
                 free_index++)
                insert_kernel_column(&output, output_work, &sector,
                                     free_index, shift);
            int output_gain = output.rank - old_output_rank;

            i64 lower_rows = 0;
            for (int index = 0; index < divisor_count; index++) {
                int step = multiplier / data[index].q;
                int parity = selected_v_parity(residue_parity, step);
                i64 lower;
                i64 upper;
                legal_interval(n_level, residue, data[index].h,
                               &lower, &upper);
                lower_rows += count_selected(lower, upper, parity);
            }
            total_even_rows += lower_rows;
            total_even_kernel += kernel_dimension;
            if (sector.peak_used_bytes > peak_sector_bytes)
                peak_sector_bytes = sector.peak_used_bytes;
            printf("sector r=%d even_rows=%lld endpoints=%d rank=%d/%d "
                   "kernel_dim=%d output_shift=%d W_gain=%d W_rank=%d/%d\n",
                   residue, (long long)lower_rows, exceptions,
                   sector.rank, d, kernel_dimension, shift, output_gain,
                   output.rank, d);
            fflush(stdout);
            crref_destroy(&sector);
        }
        snapshot_destroy(&snapshots[residue_parity]);
    }

    if (2 * total_even_rows != expected_full_rows)
        die("internal parity blocks do not partition the legal rows");
    i64 full_kernel_dimension = 2 * total_even_kernel;
    i64 full_coprime_rank = (i64)q_total - full_kernel_dimension;
    i64 full_w_gain = 2 * (i64)output.rank;
    i64 full_defect = full_kernel_dimension - full_w_gain;
    i64 assisted_rank = (i64)q_total - full_defect;
    printf("TOTAL even_coprime_rows=%lld full_coprime_rank=%lld/%d "
           "full_coprime_kernel_dim=%lld W_gain=%lld/%lld "
           "final_defect=%lld assisted_rank=%lld/%d "
           "peak_core=%zu peak_sector=%zu output_allocation=%llu\n",
           (long long)total_even_rows, (long long)full_coprime_rank,
           q_total, (long long)full_kernel_dimension,
           (long long)full_w_gain, (long long)full_kernel_dimension,
           (long long)full_defect, (long long)assisted_rank, q_total,
           peak_core_bytes, peak_sector_bytes,
           (unsigned long long)output_bytes);
    free(output_work);
    dense_output_destroy(&output);

cleanup_data:
    for (int index = 0; index < divisor_count; index++)
        free(data[index].values);
    free(data);
    free(divisors);
    return EXIT_SUCCESS;

}
