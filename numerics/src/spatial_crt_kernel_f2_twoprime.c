/* Exact two-stage CRT kernel/top-up engine over F_2.
 *
 * This is a new, non-overwriting implementation for prime level N and an
 * auxiliary odd prime P which divides M=Q/N exactly once.  In the even-j
 * parity block, write
 *
 *     j = r + N t,        t = s + P z,
 *
 * with r mod N and s mod P.  Rows with P not dividing q preserve (r,s).
 * Rows with P dividing q preserve r and couple the P values of s.  The
 * program performs those two eliminations in that order, then tests the
 * q=N orbit map.  Reflection j -> Q-1-j supplies the odd-j block.
 *
 * The program is intended first as an exact reference and validation path.
 * Its final orbit test can use either all M/2 coordinates or an explicit
 * reproducible hash projection.  A successful projected test is rigorous:
 * rank(RP)=number_of_rows implies that the unprojected R has full row rank.
 * A failed projection is reported only as inconclusive.
 *
 * The implementation reuses the audited compressed-RRE and endpoint code
 * from spatial_crt_kernel_f2_parity_core.c.  It does not modify that source.
 *
 * Compile:
 *   gcc -std=gnu11 -O3 -march=native -mbmi2 -fopenmp \
 *       -Wall -Wextra -Werror -o spatial_crt_kernel_f2_twoprime \
 *       spatial_crt_kernel_f2_twoprime.c
 *
 * Usage:
 *   ./spatial_crt_kernel_f2_twoprime N M P [--estimate] [--force]
 *   ./spatial_crt_kernel_f2_twoprime N M P \
 *       --project SEED OVERSAMPLE HASHES [--block-finish] [--force]
 *   ./spatial_crt_kernel_f2_twoprime N M P \
 *       --save-core PREFIX --core-only [--force]
 *   ./spatial_crt_kernel_f2_twoprime N M P \
 *       --load-core PREFIX --sector R [--force]
 *   ./spatial_crt_kernel_f2_twoprime N M P \
 *       --load-core PREFIX --profile-sector R ROWS [--force]
 *   ./spatial_crt_kernel_f2_twoprime N M P --count-only \
 *       --sector-workers K [--force]
 *   ./spatial_crt_kernel_f2_twoprime N M P \
 *       --project-slack SEED EXTRA HASHES --block-finish \
 *       --sector-workers K --peak-budget-gib G [--force]
 */

#include <inttypes.h>
#include <time.h>

#ifndef TWOP_FINISH_BLOCK_BITS
#define TWOP_FINISH_BLOCK_BITS 10
#endif
#if TWOP_FINISH_BLOCK_BITS < 1 || TWOP_FINISH_BLOCK_BITS > 12
#error "TWOP_FINISH_BLOCK_BITS must be between 1 and 12"
#endif

#define main spatial_crt_kernel_f2_parity_core_embedded_main
#include "spatial_crt_kernel_f2_parity_core.c"
#undef main

typedef struct {
    int direct;
    u64 seed;
    int bucket_count;
    int hash_count;
} TwopProjection;

typedef struct {
    int d;
    int words;
    int capacity;
    int count;
    u64 *rows;
} TwopRowMatrix;

typedef struct {
    char magic[8];
    uint32_t version;
    uint32_t n_level;
    uint32_t multiplier;
    uint32_t split_prime;
    uint32_t parity;
    uint32_t d;
    uint32_t rank;
    uint32_t nullity;
    uint32_t words;
    uint64_t row_count;
} TwopCoreHeader;

static double twop_now_seconds(void) {
    struct timespec value;
    if (clock_gettime(CLOCK_MONOTONIC, &value) != 0)
        die("clock_gettime failed");
    return (double)value.tv_sec + 1e-9 * (double)value.tv_nsec;
}

static TwopRowMatrix twop_row_matrix_create(int d, int capacity) {
    if (d < 0 || capacity < 0)
        die("invalid two-prime row-matrix dimensions");
    TwopRowMatrix result;
    result.d = d;
    result.words = (d + 63) / 64;
    result.capacity = capacity;
    result.count = 0;
    result.rows = xcalloc((size_t)capacity * result.words, sizeof(u64));
    return result;
}

static void twop_row_matrix_destroy(TwopRowMatrix *matrix) {
    free(matrix->rows);
    memset(matrix, 0, sizeof(*matrix));
}

static inline unsigned int twop_extract_bits(const u64 *row, int column,
                                              int width) {
    int word = column >> 6;
    int offset = column & 63;
    u64 value = row[word] >> offset;
    if (offset + width > 64)
        value |= row[word + 1] << (64 - offset);
    return (unsigned int)value & ((UINT32_C(1) << width) - 1U);
}

static void twop_swap_packed_rows(u64 *left, u64 *right, int words) {
    if (left == right)
        return;
    for (int word = 0; word < words; word++) {
        u64 temporary = left[word];
        left[word] = right[word];
        right[word] = temporary;
    }
}

static inline void twop_xor_words_from(u64 *restrict destination,
                                       const u64 *restrict source,
                                       int first_word, int words) {
    int word = first_word;
#if defined(__AVX512F__)
    for (; word + 8 <= words; word += 8) {
        __m512i left =
            _mm512_loadu_si512((const void *)(destination + word));
        __m512i right = _mm512_loadu_si512((const void *)(source + word));
        _mm512_storeu_si512((void *)(destination + word),
                            _mm512_xor_si512(left, right));
    }
#elif defined(__AVX2__)
    for (; word + 4 <= words; word += 4) {
        __m256i left =
            _mm256_loadu_si256((const __m256i *)(destination + word));
        __m256i right =
            _mm256_loadu_si256((const __m256i *)(source + word));
        _mm256_storeu_si256((__m256i *)(destination + word),
                            _mm256_xor_si256(left, right));
    }
#endif
    for (; word < words; word++)
        destination[word] ^= source[word];
}

/* Exact M4RI-style row rank.  Each block selects an independent basis for
 * ten adjacent columns, tabulates all basis combinations, then updates the
 * active row tail in parallel. */
static int twop_block_rank(TwopRowMatrix *matrix) {
    enum {
        BLOCK_BITS = TWOP_FINISH_BLOCK_BITS,
        TABLE_SIZE = 1 << TWOP_FINISH_BLOCK_BITS
    };
    int words = matrix->words;
    int row_count = matrix->count;
    u64 *pivot_rows = xcalloc((size_t)BLOCK_BITS * words, sizeof(u64));
    u64 *combinations = xcalloc((size_t)TABLE_SIZE * words, sizeof(u64));
    int lookup[TABLE_SIZE];
    int selected[BLOCK_BITS];
    unsigned int pivot_patterns[BLOCK_BITS];
    int basis_for_bit[BLOCK_BITS];
    unsigned int combination_patterns[TABLE_SIZE];
    double started = twop_now_seconds();
    int rank = 0;

    fprintf(stderr,
            "TWOP_BLOCK_FINISH rows=%d columns=%d words=%d block_bits=%d "
            "threads=%d table_bytes=%zu\n",
            row_count, matrix->d, words, BLOCK_BITS,
#if defined(_OPENMP)
            omp_get_max_threads(),
#else
            1,
#endif
            (size_t)TABLE_SIZE * words * sizeof(u64));
    fflush(stderr);

    for (int column = 0; column < matrix->d && rank < row_count;
         column += BLOCK_BITS) {
        int width = matrix->d - column;
        if (width > BLOCK_BITS)
            width = BLOCK_BITS;
        int pattern_count = 1 << width;
        for (int bit = 0; bit < BLOCK_BITS; bit++)
            basis_for_bit[bit] = -1;
        int pivots = 0;

        for (int row_index = rank; row_index < row_count; row_index++) {
            const u64 *candidate =
                matrix->rows + (size_t)row_index * words;
            unsigned int reduced =
                twop_extract_bits(candidate, column, width);
            unsigned int combination = 0;
            while (reduced != 0) {
                int bit = __builtin_ctz(reduced);
                int prior = basis_for_bit[bit];
                if (prior < 0)
                    break;
                reduced ^= pivot_patterns[prior];
                combination ^= UINT32_C(1) << prior;
            }
            if (reduced == 0)
                continue;

            int pivot_index = pivots++;
            int pivot_bit = __builtin_ctz(reduced);
            selected[pivot_index] = row_index;
            pivot_patterns[pivot_index] = reduced;
            basis_for_bit[pivot_bit] = pivot_index;
            u64 *destination =
                pivot_rows + (size_t)pivot_index * words;
            memcpy(destination, candidate, (size_t)words * sizeof(u64));
            while (combination != 0) {
                int prior = __builtin_ctz(combination);
                twop_xor_words_from(
                    destination, pivot_rows + (size_t)prior * words,
                    column >> 6, words);
                combination &= combination - 1;
            }
            if (pivots == width)
                break;
        }
        if (pivots == 0)
            continue;

        for (int pivot = 0; pivot < pivots; pivot++) {
            int front = rank + pivot;
            int source = selected[pivot];
            if (source != front) {
                twop_swap_packed_rows(
                    matrix->rows + (size_t)front * words,
                    matrix->rows + (size_t)source * words, words);
                for (int later = pivot + 1; later < pivots; later++) {
                    if (selected[later] == front)
                        selected[later] = source;
                    else if (selected[later] == source)
                        selected[later] = front;
                }
            }
        }
        for (int pivot = 0; pivot < pivots; pivot++)
            memcpy(matrix->rows + (size_t)(rank + pivot) * words,
                   pivot_rows + (size_t)pivot * words,
                   (size_t)words * sizeof(u64));

        for (int pattern = 0; pattern < pattern_count; pattern++)
            lookup[pattern] = -1;
        lookup[0] = 0;
        combination_patterns[0] = 0;
        memset(combinations, 0, (size_t)words * sizeof(u64));
        int combinations_used = 1 << pivots;
        for (int mask = 1; mask < combinations_used; mask++) {
            int pivot = __builtin_ctz((unsigned int)mask);
            int previous = mask & (mask - 1);
            combination_patterns[mask] =
                combination_patterns[previous] ^ pivot_patterns[pivot];
            u64 *destination = combinations + (size_t)mask * words;
            memcpy(destination,
                   combinations + (size_t)previous * words,
                   (size_t)words * sizeof(u64));
            twop_xor_words_from(destination,
                                pivot_rows + (size_t)pivot * words,
                                column >> 6, words);
            lookup[combination_patterns[mask]] = mask;
        }

        int active_start = rank + pivots;
#if defined(_OPENMP)
#pragma omp parallel for schedule(static)
#endif
        for (int row_index = active_start; row_index < row_count;
             row_index++) {
            u64 *row = matrix->rows + (size_t)row_index * words;
            unsigned int pattern = twop_extract_bits(row, column, width);
            int mask = lookup[pattern];
            if (mask < 0)
                die("internal two-prime block lookup failure");
            if (mask != 0)
                twop_xor_words_from(
                    row, combinations + (size_t)mask * words,
                    column >> 6, words);
        }
        rank += pivots;

        if ((column & 4095) == 0 || rank == row_count) {
            fprintf(stderr,
                    "TWOP_BLOCK_PROGRESS columns=%d/%d rank=%d/%d "
                    "elapsed=%.3f_s\n",
                    column + width, matrix->d, rank, row_count,
                    twop_now_seconds() - started);
            fflush(stderr);
        }
    }

    fprintf(stderr, "TWOP_BLOCK_DONE rank=%d/%d elapsed=%.3f_s\n",
            rank, row_count, twop_now_seconds() - started);
    fflush(stderr);
    free(combinations);
    free(pivot_rows);
    return rank;
}

static uint64_t twop_snapshot_nnz(const Snapshot *snapshot) {
    uint64_t nonzeros = 0;
    size_t count = (size_t)snapshot->rank * snapshot->words;
    for (size_t index = 0; index < count; index++)
        nonzeros += (uint64_t)__builtin_popcountll(snapshot->arena[index]);
    return nonzeros;
}

static void twop_core_path(char *path, size_t capacity,
                           const char *prefix, int parity) {
    int length = snprintf(path, capacity, "%s.p%d.core", prefix, parity);
    if (length < 0 || (size_t)length >= capacity)
        die("core checkpoint path is too long");
}

static void twop_write_exact(FILE *file, const void *data, size_t size,
                             const char *what) {
    if (size > 0 && fwrite(data, 1, size, file) != size) {
        fprintf(stderr, "failed to write %s\n", what);
        exit(EXIT_FAILURE);
    }
}

static void twop_read_exact(FILE *file, void *data, size_t size,
                            const char *what) {
    if (size > 0 && fread(data, 1, size, file) != size) {
        fprintf(stderr, "failed to read %s\n", what);
        exit(EXIT_FAILURE);
    }
}

static void twop_save_core(const char *prefix, int n_level, int multiplier,
                           int prime, int parity, i64 row_count,
                           const Snapshot *snapshot) {
    char path[4096];
    twop_core_path(path, sizeof(path), prefix, parity);
    FILE *file = fopen(path, "wb");
    if (!file) {
        fprintf(stderr, "cannot create core checkpoint %s: %s\n", path,
                strerror(errno));
        exit(EXIT_FAILURE);
    }
    TwopCoreHeader header;
    memset(&header, 0, sizeof(header));
    memcpy(header.magic, "2PCRT01", 7);
    header.version = 1;
    header.n_level = (uint32_t)n_level;
    header.multiplier = (uint32_t)multiplier;
    header.split_prime = (uint32_t)prime;
    header.parity = (uint32_t)parity;
    header.d = (uint32_t)snapshot->d;
    header.rank = (uint32_t)snapshot->rank;
    header.nullity = (uint32_t)snapshot->nullity;
    header.words = (uint32_t)snapshot->words;
    header.row_count = (uint64_t)row_count;
    twop_write_exact(file, &header, sizeof(header), "core header");
    twop_write_exact(file, snapshot->arena,
                     (size_t)snapshot->rank * snapshot->words * sizeof(u64),
                     "core arena");
    twop_write_exact(file, snapshot->nonpivot_cols,
                     (size_t)snapshot->nullity * sizeof(int),
                     "core nonpivot columns");
    twop_write_exact(file, snapshot->npidx_for_col,
                     (size_t)snapshot->d * sizeof(int),
                     "core nonpivot map");
    twop_write_exact(file, snapshot->basis_pivots,
                     (size_t)snapshot->rank * sizeof(int),
                     "core pivots");
    twop_write_exact(file, snapshot->pivot_to_row,
                     (size_t)snapshot->d * sizeof(int),
                     "core pivot map");
    if (fclose(file) != 0) {
        fprintf(stderr, "failed to close core checkpoint %s\n", path);
        exit(EXIT_FAILURE);
    }
    printf("CORE_SAVED parity=%d path=%s bytes=%" PRIu64 "\n", parity,
           path, snapshot_storage_bytes(snapshot->d, snapshot->rank,
                                        snapshot->nullity) +
                     (uint64_t)sizeof(header));
}

static Snapshot twop_load_core(const char *prefix, int n_level,
                               int multiplier, int prime, int parity,
                               i64 expected_rows) {
    char path[4096];
    twop_core_path(path, sizeof(path), prefix, parity);
    FILE *file = fopen(path, "rb");
    if (!file) {
        fprintf(stderr, "cannot open core checkpoint %s: %s\n", path,
                strerror(errno));
        exit(EXIT_FAILURE);
    }
    TwopCoreHeader header;
    twop_read_exact(file, &header, sizeof(header), "core header");
    if (memcmp(header.magic, "2PCRT01", 7) != 0 || header.version != 1 ||
        header.n_level != (uint32_t)n_level ||
        header.multiplier != (uint32_t)multiplier ||
        header.split_prime != (uint32_t)prime ||
        header.parity != (uint32_t)parity ||
        header.d != (uint32_t)(multiplier / (2 * prime)) ||
        header.rank > header.d || header.nullity > header.d ||
        header.rank + header.nullity != header.d ||
        header.words != (header.nullity + 63U) / 64U ||
        header.row_count != (uint64_t)expected_rows) {
        fprintf(stderr, "core checkpoint %s does not match this run\n", path);
        exit(EXIT_FAILURE);
    }
    Snapshot snapshot;
    snapshot.d = (int)header.d;
    snapshot.rank = (int)header.rank;
    snapshot.nullity = (int)header.nullity;
    snapshot.words = (int)header.words;
    snapshot.arena = xmalloc((size_t)snapshot.rank * snapshot.words *
                             sizeof(u64));
    snapshot.nonpivot_cols =
        xmalloc((size_t)snapshot.nullity * sizeof(int));
    snapshot.npidx_for_col = xmalloc((size_t)snapshot.d * sizeof(int));
    snapshot.basis_pivots = xmalloc((size_t)snapshot.rank * sizeof(int));
    snapshot.pivot_to_row = xmalloc((size_t)snapshot.d * sizeof(int));
    twop_read_exact(file, snapshot.arena,
                    (size_t)snapshot.rank * snapshot.words * sizeof(u64),
                    "core arena");
    twop_read_exact(file, snapshot.nonpivot_cols,
                    (size_t)snapshot.nullity * sizeof(int),
                    "core nonpivot columns");
    twop_read_exact(file, snapshot.npidx_for_col,
                    (size_t)snapshot.d * sizeof(int),
                    "core nonpivot map");
    twop_read_exact(file, snapshot.basis_pivots,
                    (size_t)snapshot.rank * sizeof(int), "core pivots");
    twop_read_exact(file, snapshot.pivot_to_row,
                    (size_t)snapshot.d * sizeof(int), "core pivot map");
    if (fgetc(file) != EOF)
        die("core checkpoint has trailing data");
    if (fclose(file) != 0)
        die("failed to close core checkpoint");
    for (int column = 0; column < snapshot.d; column++) {
        int free_index = snapshot.npidx_for_col[column];
        int row_index = snapshot.pivot_to_row[column];
        if ((free_index >= 0) == (row_index >= 0))
            die("core checkpoint has an invalid coordinate partition");
        if (free_index >= snapshot.nullity || row_index >= snapshot.rank)
            die("core checkpoint has an out-of-range coordinate map");
    }
    printf("CORE_LOADED parity=%d path=%s rank=%d/%d nullity=%d\n",
           parity, path, snapshot.rank, snapshot.d, snapshot.nullity);
    return snapshot;
}

static u64 twop_parse_u64(const char *text, const char *name) {
    char *end = NULL;
    errno = 0;
    unsigned long long value = strtoull(text, &end, 10);
    if (errno != 0 || end == text || *end != '\0' || text[0] == '-') {
        fprintf(stderr, "%s must be a nonnegative integer\n", name);
        exit(EXIT_FAILURE);
    }
    return (u64)value;
}

static int twop_buffered_radius(int n_level, int multiplier, int q) {
    i128 target = (i128)multiplier * multiplier * n_level;
    i128 q_squared = (i128)q * q;
    i64 low = 0;
    i64 high = (i64)(multiplier / q) * n_level;
    while (low < high) {
        i64 middle = low + (high - low) / 2;
        if ((i128)middle * middle * q_squared >= target)
            high = middle;
        else
            low = middle + 1;
    }
    if (low > INT_MAX)
        die("buffered radius exceeds int range");
    return (int)low;
}

static int twop_totient(int value) {
    int result = value;
    int remaining = value;
    for (int prime = 2; prime <= remaining / prime;
         prime += prime == 2 ? 1 : 2) {
        if (remaining % prime != 0)
            continue;
        result -= result / prime;
        do {
            remaining /= prime;
        } while (remaining % prime == 0);
    }
    if (remaining > 1)
        result -= result / remaining;
    return result;
}

static DivisorData *twop_make_data(int n_level, int multiplier, int prime,
                                   int want_divisible, int with_units,
                                   int *count_out, i64 *even_rows_out,
                                   i64 *nonzeros_out) {
    int raw_count = 0;
    int *divisors = make_divisors(multiplier, &raw_count);
    DivisorData *data = xcalloc((size_t)raw_count, sizeof(*data));
    int count = 0;
    i64 even_rows = 0;
    i64 nonzeros = 0;
    for (int index = 0; index < raw_count; index++) {
        int q = divisors[index];
        if ((q % prime == 0) != want_divisible)
            continue;
        int h = twop_buffered_radius(n_level, multiplier, q);
        if (h < 2)
            continue;
        data[count].q = q;
        data[count].h = h;
        int phi = twop_totient(q);
        even_rows += h - 1;
        nonzeros += (i64)(h - 1) * phi;
        if (with_units) {
            data[count].values = xmalloc((size_t)q * sizeof(int));
            for (int a = 0; a < q; a++)
                if (gcd_int(a, q) == 1)
                    data[count].values[data[count].count++] = a;
            if (data[count].count != phi)
                die("internal totient/unit-count mismatch");
        } else {
            data[count].count = phi;
        }
        count++;
    }
    free(divisors);
    *count_out = count;
    *even_rows_out = even_rows;
    *nonzeros_out = nonzeros;
    return data;
}

static void twop_destroy_data(DivisorData *data, int count) {
    if (!data)
        return;
    for (int index = 0; index < count; index++)
        free(data[index].values);
    free(data);
}

/* Add the restriction of one physical coordinate in a P-free subsector to
 * a row on the subsector-kernel coefficient space. */
static void twop_snapshot_toggle(const Snapshot *snapshot, int offset,
                                 int column, Crref *target) {
    if (column < 0 || column >= snapshot->d)
        die("internal P-free subsector column out of range");
    int free_index = snapshot->npidx_for_col[column];
    if (free_index >= 0) {
        crref_toggle_global(target, offset + free_index);
        return;
    }
    int row_index = snapshot->pivot_to_row[column];
    if (row_index < 0 || row_index >= snapshot->rank)
        die("internal P-free pivot row missing");
    const u64 *row =
        snapshot->arena + (size_t)row_index * snapshot->words;
    for (int word = 0; word < snapshot->words; word++) {
        u64 bits = row[word];
        while (bits != 0) {
            int bit = __builtin_ctzll(bits);
            int local = 64 * word + bit;
            if (local < snapshot->nullity)
                crref_toggle_global(target, offset + local);
            bits &= bits - 1;
        }
    }
}

static Snapshot twop_build_subsector(const Snapshot common[2], int n_level,
                                     int multiplier, int prime, int residue,
                                     int subresidue,
                                     const DivisorData *pfree,
                                     int pfree_count) {
    int local_multiplier = multiplier / prime;
    int combined_residue = residue + n_level * subresidue;
    int local_parity = combined_residue & 1;
    int exceptions = count_sector_exceptions(
        n_level * prime, local_multiplier, combined_residue,
        pfree, pfree_count);
    Crref sector = crref_from_snapshot(&common[local_parity], exceptions);
    int added = add_sector_exceptions(
        &sector, n_level * prime, local_multiplier, combined_residue,
        pfree, pfree_count);
    if (added != exceptions)
        die("internal P-free endpoint count mismatch");
    Snapshot answer = snapshot_from_crref(&sector);
    crref_destroy(&sector);
    return answer;
}

/* Form and reduce all rows whose modulus is divisible by P in one fixed
 * residue class modulo N.  The returned RREF acts on the direct sum of the
 * P-free subsector kernels. */
static Crref twop_build_coupling(int n_level, int multiplier, int prime,
                                 int residue, const Snapshot *subsectors,
                                 const int *offsets, int coefficient_count,
                                 const DivisorData *pdiv, int pdiv_count,
                                 i64 *rows_out) {
    size_t arena = compressed_arena_u64(coefficient_count);
    Crref coupling = crref_create(coefficient_count, arena);
    i64 rows = 0;
    for (int index = 0; index < pdiv_count; index++) {
        int q = pdiv[index].q;
        int step = multiplier / q;
        int parity = selected_v_parity(residue & 1, step);
        i64 lower;
        i64 upper;
        legal_interval(n_level, residue, pdiv[index].h, &lower, &upper);
        for (i64 v = first_with_parity(lower, parity);
             v <= upper; v += 2) {
            crref_zero_work(&coupling);
            for (int unit_index = 0; unit_index < pdiv[index].count;
                 unit_index++) {
                int a = pdiv[index].values[unit_index];
                int t = positive_mod_i64(v + (i64)a * step, multiplier);
                int subresidue = t % prime;
                int z = (t - subresidue) / prime;
                int local_parity = (residue + subresidue) & 1;
                if ((z & 1) != local_parity)
                    die("internal two-prime parity mismatch");
                int column = (z - local_parity) / 2;
                twop_snapshot_toggle(&subsectors[subresidue],
                                     offsets[subresidue], column,
                                     &coupling);
            }
            (void)crref_insert_current_work(&coupling);
            rows++;
        }
    }
    crref_compact(&coupling);
    *rows_out = rows;
    return coupling;
}

static void twop_snapshot_toggle_dense(const Snapshot *snapshot, int offset,
                                       int column, u64 *target,
                                       int target_words) {
    if (column < 0 || column >= snapshot->d)
        die("internal sampled subsector column out of range");
    int free_index = snapshot->npidx_for_col[column];
    if (free_index >= 0) {
        int output = offset + free_index;
        target[output >> 6] ^= UINT64_C(1) << (output & 63);
        return;
    }
    int row_index = snapshot->pivot_to_row[column];
    if (row_index < 0 || row_index >= snapshot->rank)
        die("internal sampled subsector pivot row missing");
    const u64 *source =
        snapshot->arena + (size_t)row_index * snapshot->words;
    int output_word = offset >> 6;
    int output_shift = offset & 63;
    for (int word = 0; word < snapshot->words; word++) {
        u64 value = source[word];
        if (value == 0)
            continue;
        if (output_word + word < target_words)
            target[output_word + word] ^= value << output_shift;
        if (output_shift != 0 && output_word + word + 1 < target_words)
            target[output_word + word + 1] ^=
                value >> (64 - output_shift);
    }
}

/* Measure raw rows after the first CRT elimination but before the expensive
 * second elimination.  This decides whether an explicit sparse export is
 * sensible; it does not make or report a rank claim. */
static void twop_profile_sector_rows(
    const Snapshot common[2], int n_level, int multiplier, int prime,
    int residue, const DivisorData *pfree, int pfree_count,
    const DivisorData *pdiv, int pdiv_count, i64 requested_rows) {
    Snapshot *subs = xcalloc((size_t)prime, sizeof(*subs));
    int *offsets = xcalloc((size_t)prime + 1, sizeof(*offsets));
    uint64_t subsector_bytes = 0;
    for (int subresidue = 0; subresidue < prime; subresidue++) {
        subs[subresidue] = twop_build_subsector(
            common, n_level, multiplier, prime, residue, subresidue,
            pfree, pfree_count);
        offsets[subresidue + 1] =
            offsets[subresidue] + subs[subresidue].nullity;
        subsector_bytes += snapshot_storage_bytes(
            subs[subresidue].d, subs[subresidue].rank,
            subs[subresidue].nullity);
    }
    int coefficient_count = offsets[prime];
    int words = (coefficient_count + 63) / 64;
    u64 *row = xcalloc((size_t)words, sizeof(*row));
    i64 sampled = 0;
    uint64_t minimum = UINT64_MAX;
    uint64_t maximum = 0;
    __uint128_t total = 0;
    for (int index = 0;
         index < pdiv_count && sampled < requested_rows; index++) {
        int q = pdiv[index].q;
        int step = multiplier / q;
        int parity = selected_v_parity(residue & 1, step);
        i64 lower;
        i64 upper;
        legal_interval(n_level, residue, pdiv[index].h, &lower, &upper);
        for (i64 v = first_with_parity(lower, parity);
             v <= upper && sampled < requested_rows; v += 2) {
            memset(row, 0, (size_t)words * sizeof(*row));
            for (int unit_index = 0; unit_index < pdiv[index].count;
                 unit_index++) {
                int a = pdiv[index].values[unit_index];
                int t = positive_mod_i64(
                    v + (i64)a * step, multiplier);
                int subresidue = t % prime;
                int z = (t - subresidue) / prime;
                int local_parity = (residue + subresidue) & 1;
                if ((z & 1) != local_parity)
                    die("internal sampled two-prime parity mismatch");
                int column = (z - local_parity) / 2;
                twop_snapshot_toggle_dense(
                    &subs[subresidue], offsets[subresidue], column,
                    row, words);
            }
            if ((coefficient_count & 63) != 0)
                row[words - 1] &=
                    (UINT64_C(1) << (coefficient_count & 63)) - 1;
            uint64_t weight = 0;
            for (int word = 0; word < words; word++)
                weight += (uint64_t)__builtin_popcountll(row[word]);
            if (weight < minimum)
                minimum = weight;
            if (weight > maximum)
                maximum = weight;
            total += weight;
            sampled++;
        }
    }
    if (sampled == 0)
        die("row profile found no P-divisible rows");
    double average = (double)total / (double)sampled;
    printf("ROW_PROFILE residue=%d sampled=%lld coefficients=%d "
           "weight_min=%" PRIu64 " weight_mean=%.3f "
           "weight_max=%" PRIu64 " density_mean=%.8f "
           "subsector_snapshots=%.3f_GiB\n",
           residue, (long long)sampled, coefficient_count, minimum,
           average, maximum, average / (double)coefficient_count,
           (double)subsector_bytes / (double)(UINT64_C(1) << 30));
    free(row);
    for (int subresidue = 0; subresidue < prime; subresidue++)
        snapshot_destroy(&subs[subresidue]);
    free(offsets);
    free(subs);
}

static uint64_t twop_snapshot_upper_after_rows(const Snapshot *common,
                                                int exceptions) {
    int maximum_rank = common->rank + exceptions;
    if (maximum_rank > common->d)
        maximum_rank = common->d;
    int candidate = common->rank;
    int half = common->d / 2;
    if (candidate < half) {
        candidate = half;
        if (candidate > maximum_rank)
            candidate = maximum_rank;
    }
    return snapshot_storage_bytes(common->d, candidate,
                                  common->d - candidate);
}

/* Given measured common-core ranks, bound every allocation made while one
 * residue is processed.  Endpoint constraints can only increase rank, so
 * their possible snapshot sizes lie on a known interval. */
static uint64_t twop_sector_dynamic_upper(
    const Snapshot common[2], int n_level, int multiplier, int prime,
    const DivisorData *pfree, int pfree_count) {
    int local_multiplier = multiplier / prime;
    int coefficient_upper = 0;
    for (int residue_parity = 0; residue_parity <= 1;
         residue_parity++) {
        int count = 0;
        for (int subresidue = 0; subresidue < prime; subresidue++) {
            int parity = residue_parity ^ (subresidue & 1);
            if (common[parity].nullity > INT_MAX - count)
                die("sector coefficient upper bound exceeds int range");
            count += common[parity].nullity;
        }
        if (count > coefficient_upper)
            coefficient_upper = count;
    }
    uint64_t coupling_upper =
        (uint64_t)compressed_arena_u64(coefficient_upper) * sizeof(u64) +
        crref_auxiliary_bytes(coefficient_upper);
    uint64_t maximum = 0;
    for (int residue = 0; residue < n_level; residue++) {
        uint64_t completed_snapshots = 0;
        uint64_t build_peak = 0;
        for (int subresidue = 0; subresidue < prime; subresidue++) {
            int combined_residue = residue + n_level * subresidue;
            int parity = combined_residue & 1;
            int exceptions = count_sector_exceptions(
                n_level * prime, local_multiplier, combined_residue,
                pfree, pfree_count);
            uint64_t snapshot_upper = twop_snapshot_upper_after_rows(
                &common[parity], exceptions);
            uint64_t active =
                (uint64_t)restored_sector_arena_u64(
                    &common[parity], exceptions) * sizeof(u64) +
                crref_auxiliary_bytes(common[parity].d);
            uint64_t simultaneous = completed_snapshots + active +
                                    snapshot_upper;
            if (simultaneous > build_peak)
                build_peak = simultaneous;
            completed_snapshots += snapshot_upper;
        }
        uint64_t coupling_peak = completed_snapshots + coupling_upper;
        uint64_t residue_peak =
            build_peak > coupling_peak ? build_peak : coupling_peak;
        if (residue_peak > maximum)
            maximum = residue_peak;
    }
    return maximum;
}

static u64 twop_mix64(u64 value) {
    value = (value ^ (value >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    value = (value ^ (value >> 27)) * UINT64_C(0x94d049bb133111eb);
    return value ^ (value >> 31);
}

static int twop_hash_bucket(int coordinate, int hash_index, u64 seed,
                            int bucket_count) {
    u64 value = seed ^
                ((u64)(unsigned int)coordinate *
                 UINT64_C(0x9e3779b97f4a7c15)) ^
                ((u64)(unsigned int)(hash_index + 1) *
                 UINT64_C(0xd1b54a32d192ed03));
    u64 random_value = twop_mix64(value);
    return (int)(((__uint128_t)random_value * (u64)bucket_count) >> 64);
}

static void twop_toggle_output(u64 *work, int coordinate,
                               const TwopProjection *projection) {
    if (projection->direct) {
        work[coordinate >> 6] ^= UINT64_C(1) << (coordinate & 63);
        return;
    }
    for (int hash_index = 0; hash_index < projection->hash_count;
         hash_index++) {
        int bucket = twop_hash_bucket(coordinate, hash_index,
                                      projection->seed,
                                      projection->bucket_count);
        work[bucket >> 6] ^= UINT64_C(1) << (bucket & 63);
    }
}

static void twop_toggle_subkernel(u64 *work,
                                  const TwopProjection *projection,
                                  const Snapshot *subsector,
                                  int local_free_index, int residue,
                                  int subresidue, int prime,
                                  int local_multiplier, int global_d,
                                  int output_shift) {
    int local_parity = (residue + subresidue) & 1;
    int free_column = subsector->nonpivot_cols[local_free_index];
    int z = 2 * free_column + local_parity;
    int t = subresidue + prime * z;
    if (((t + residue) & 1) != 0 || t < 0 ||
        t >= prime * local_multiplier)
        die("internal physical-coordinate reconstruction error");
    int coordinate = (t - (residue & 1)) / 2;
    coordinate += output_shift;
    if (coordinate >= global_d)
        coordinate -= global_d;
    twop_toggle_output(work, coordinate, projection);

    int word = local_free_index >> 6;
    u64 mask = UINT64_C(1) << (local_free_index & 63);
    for (int row_index = 0; row_index < subsector->rank; row_index++) {
        const u64 *row = subsector->arena +
                         (size_t)row_index * subsector->words;
        if ((row[word] & mask) == 0)
            continue;
        int local_column = subsector->basis_pivots[row_index];
        z = 2 * local_column + local_parity;
        t = subresidue + prime * z;
        coordinate = (t - (residue & 1)) / 2 + output_shift;
        if (coordinate >= global_d)
            coordinate -= global_d;
        twop_toggle_output(work, coordinate, projection);
    }
}

static void twop_toggle_coefficient(u64 *work,
                                    const TwopProjection *projection,
                                    int coefficient, const Snapshot *subs,
                                    const int *offsets, int prime,
                                    int residue, int local_multiplier,
                                    int global_d, int output_shift) {
    int subresidue = 0;
    while (subresidue + 1 < prime &&
           coefficient >= offsets[subresidue + 1])
        subresidue++;
    int local = coefficient - offsets[subresidue];
    if (local < 0 || local >= subs[subresidue].nullity)
        die("internal coefficient/subsector lookup failure");
    twop_toggle_subkernel(work, projection, &subs[subresidue], local,
                          residue, subresidue, prime, local_multiplier,
                          global_d, output_shift);
}

static void twop_toggle_local_column(u64 *work,
                                     const TwopProjection *projection,
                                     int local_column, int residue,
                                     int subresidue, int prime,
                                     int local_multiplier, int global_d,
                                     int output_shift) {
    int local_parity = (residue + subresidue) & 1;
    int z = 2 * local_column + local_parity;
    int t = subresidue + prime * z;
    if (((t + residue) & 1) != 0 || t < 0 ||
        t >= prime * local_multiplier)
        die("internal physical-coordinate reconstruction error");
    int coordinate = (t - (residue & 1)) / 2 + output_shift;
    if (coordinate >= global_d)
        coordinate -= global_d;
    twop_toggle_output(work, coordinate, projection);
}

static void twop_toggle_coefficient_bit(u64 *coefficient_rows,
                                        const int *word_offsets,
                                        const int *offsets, int prime,
                                        int coefficient) {
    int subresidue = 0;
    while (subresidue + 1 < prime &&
           coefficient >= offsets[subresidue + 1])
        subresidue++;
    int local = coefficient - offsets[subresidue];
    if (local < 0 || local >= offsets[subresidue + 1] - offsets[subresidue])
        die("internal coefficient/subsector lookup failure");
    coefficient_rows[word_offsets[subresidue] + (local >> 6)] ^=
        UINT64_C(1) << (local & 63);
}

/* Apply all coefficients belonging to one common-core nullspace at once.
 * This is algebraically the same reconstruction as
 * twop_toggle_subkernel, but computes every pivot coefficient as a single
 * dot product.  The previous coefficient-at-a-time implementation scanned
 * every snapshot row once per set coefficient, which is prohibitive near a
 * Hall cliff. */
static void twop_expand_subkernel_combination(
    u64 *work, const TwopProjection *projection,
    const Snapshot *subsector, const u64 *coefficients, int residue,
    int subresidue, int prime, int local_multiplier, int global_d,
    int output_shift) {
    for (int word = 0; word < subsector->words; word++) {
        u64 bits = coefficients[word];
        while (bits != 0) {
            int bit = __builtin_ctzll(bits);
            int local_free_index = 64 * word + bit;
            if (local_free_index >= subsector->nullity)
                die("internal padded coefficient bit is nonzero");
            twop_toggle_local_column(
                work, projection,
                subsector->nonpivot_cols[local_free_index], residue,
                subresidue, prime, local_multiplier, global_d,
                output_shift);
            bits &= bits - 1;
        }
    }

    for (int row_index = 0; row_index < subsector->rank; row_index++) {
        const u64 *row = subsector->arena +
                         (size_t)row_index * subsector->words;
        u64 parity_bits = 0;
#if defined(_OPENMP)
#pragma omp simd reduction(^ : parity_bits)
#endif
        for (int word = 0; word < subsector->words; word++)
            parity_bits ^= row[word] & coefficients[word];
        if (__builtin_parityll(parity_bits))
            twop_toggle_local_column(
                work, projection, subsector->basis_pivots[row_index],
                residue, subresidue, prime, local_multiplier, global_d,
                output_shift);
    }
}

static void twop_insert_sector_kernel(DenseOutput *output, u64 *work,
                                      const TwopProjection *projection,
                                      const Crref *coupling,
                                      const Snapshot *subs,
                                      const int *offsets, int prime,
                                      int residue, int local_multiplier,
                                      int global_d, int output_shift) {
    for (int free_index = 0; free_index < coupling->frozen; free_index++) {
        memset(work, 0, (size_t)output->words * sizeof(*work));
        twop_toggle_coefficient(
            work, projection, coupling->nonpivot_cols[free_index], subs,
            offsets, prime, residue, local_multiplier, global_d,
            output_shift);
        int word = free_index >> 6;
        u64 mask = UINT64_C(1) << (free_index & 63);
        for (int row_index = 0; row_index < coupling->rank; row_index++) {
            const u64 *row = coupling->arena +
                             (size_t)row_index * coupling->frozen_words;
            if ((row[word] & mask) == 0)
                continue;
            twop_toggle_coefficient(
                work, projection, coupling->basis_pivots[row_index], subs,
                offsets, prime, residue, local_multiplier, global_d,
                output_shift);
        }
        (void)dense_output_insert(output, work);
    }
}

static void twop_append_sector_kernel(TwopRowMatrix *matrix, u64 *work,
                                      const TwopProjection *projection,
                                      const Crref *coupling,
                                      const Snapshot *subs,
                                      const int *offsets, int prime,
                                      int residue, int local_multiplier,
                                      int global_d, int output_shift) {
    (void)work;
    int first_row = matrix->count;
    if (coupling->frozen > matrix->capacity - first_row)
        die("two-prime raw-row capacity exhausted");

    int *word_offsets = xcalloc((size_t)prime + 1,
                                sizeof(*word_offsets));
    for (int subresidue = 0; subresidue < prime; subresidue++)
        word_offsets[subresidue + 1] =
            word_offsets[subresidue] + subs[subresidue].words;
    int coefficient_words = word_offsets[prime];
#if defined(_OPENMP)
    int thread_count = omp_get_max_threads();
#else
    int thread_count = 1;
#endif
    u64 *thread_coefficients =
        xcalloc((size_t)thread_count * coefficient_words,
                sizeof(*thread_coefficients));

    /* Each expanded kernel row has its own final destination in the raw
     * matrix.  Expanding the rows serially is catastrophically slow near a
     * Hall cliff (for N=83 there are 302985 such rows), while the rows share
     * no writable state.  First-touching the destinations here also places
     * the large matrix pages on the NUMA nodes of the workers that build
     * them. */
#if defined(_OPENMP)
#pragma omp parallel for schedule(dynamic, 1)
#endif
    for (int free_index = 0; free_index < coupling->frozen; free_index++) {
#if defined(_OPENMP)
        int thread_index = omp_get_thread_num();
#else
        int thread_index = 0;
#endif
        u64 *coefficient_rows =
            thread_coefficients + (size_t)thread_index * coefficient_words;
        memset(coefficient_rows, 0,
               (size_t)coefficient_words * sizeof(*coefficient_rows));
        u64 *destination = matrix->rows +
                           (size_t)(first_row + free_index) * matrix->words;
        memset(destination, 0,
               (size_t)matrix->words * sizeof(*destination));
        twop_toggle_coefficient_bit(
            coefficient_rows, word_offsets, offsets, prime,
            coupling->nonpivot_cols[free_index]);
        int word = free_index >> 6;
        u64 mask = UINT64_C(1) << (free_index & 63);
        for (int row_index = 0; row_index < coupling->rank; row_index++) {
            const u64 *row = coupling->arena +
                             (size_t)row_index * coupling->frozen_words;
            if ((row[word] & mask) == 0)
                continue;
            twop_toggle_coefficient_bit(
                coefficient_rows, word_offsets, offsets, prime,
                coupling->basis_pivots[row_index]);
        }
        for (int subresidue = 0; subresidue < prime; subresidue++)
            twop_expand_subkernel_combination(
                destination, projection, &subs[subresidue],
                coefficient_rows + word_offsets[subresidue], residue,
                subresidue, prime, local_multiplier, global_d,
                output_shift);
    }
    matrix->count = first_row + coupling->frozen;
    free(thread_coefficients);
    free(word_offsets);
}

/* Build one complete residue-mod-N sector.  When OUTPUT is null this is the
 * first counting pass; otherwise its kernel is inserted into the W image. */
static int twop_process_sector(const Snapshot common[2], int n_level,
                               int multiplier, int prime, int residue,
                               const DivisorData *pfree, int pfree_count,
                               const DivisorData *pdiv, int pdiv_count,
                               DenseOutput *output, u64 *output_work,
                               TwopRowMatrix *raw_output,
                               const TwopProjection *projection,
                               int output_shift, i64 *pdiv_rows_out,
                               size_t *peak_coupling_out) {
    int local_multiplier = multiplier / prime;
    Snapshot *subs = xcalloc((size_t)prime, sizeof(*subs));
    int *offsets = xcalloc((size_t)prime + 1, sizeof(*offsets));
    for (int subresidue = 0; subresidue < prime; subresidue++) {
        subs[subresidue] = twop_build_subsector(
            common, n_level, multiplier, prime, residue, subresidue,
            pfree, pfree_count);
        offsets[subresidue + 1] =
            offsets[subresidue] + subs[subresidue].nullity;
    }
    int coefficient_count = offsets[prime];
    i64 pdiv_rows = 0;
    Crref coupling = twop_build_coupling(
        n_level, multiplier, prime, residue, subs, offsets,
        coefficient_count, pdiv, pdiv_count, &pdiv_rows);
    int kernel_dimension = coupling.frozen;
    if (coupling.peak_used_bytes > *peak_coupling_out)
        *peak_coupling_out = coupling.peak_used_bytes;
    if (output)
        twop_insert_sector_kernel(
            output, output_work, projection, &coupling, subs, offsets,
            prime, residue, local_multiplier, multiplier / 2,
            output_shift);
    else if (raw_output)
        twop_append_sector_kernel(
            raw_output, output_work, projection, &coupling, subs, offsets,
            prime, residue, local_multiplier, multiplier / 2,
            output_shift);
    printf("sector r=%d P_free_kernel_coefficients=%d P_divisible_rows=%lld "
           "P_divisible_rank=%d/%d sector_kernel_dim=%d%s\n",
           residue, coefficient_count, (long long)pdiv_rows,
           coupling.rank, coefficient_count, kernel_dimension,
           (output || raw_output) ? " projected" : "");
    fflush(stdout);
    crref_destroy(&coupling);
    for (int subresidue = 0; subresidue < prime; subresidue++)
        snapshot_destroy(&subs[subresidue]);
    free(offsets);
    free(subs);
    *pdiv_rows_out = pdiv_rows;
    return kernel_dimension;
}

int main(int argc, char **argv) {
    if (argc < 4) {
        fprintf(stderr,
                "Usage: %s N M P [--estimate] [--force] "
                "[--project SEED OVERSAMPLE HASHES] "
                "[--project-slack SEED EXTRA HASHES] [--block-finish] "
                "[--save-core PREFIX] [--load-core PREFIX] "
                "[--core-only] [--sector R] [--profile-sector R ROWS] "
                "[--sector-workers K] [--count-only] "
                "[--peak-budget-gib G]\n"
                "  --sector R --block-finish also materializes and ranks "
                "that sector's direct W image\n"
                "  --sector-workers K runs K residue sectors concurrently; "
                "requires --block-finish\n",
                argv[0]);
        return EXIT_FAILURE;
    }
    int n_level = parse_positive_int(argv[1], "N");
    int multiplier = parse_positive_int(argv[2], "M");
    int prime = parse_positive_int(argv[3], "P");
    int estimate_only = 0;
    int force = 0;
    int use_projection = 0;
    int use_block_finish = 0;
    u64 projection_seed = 0;
    int oversample = 0;
    int projection_slack = -1;
    int hash_count = 0;
    const char *save_core_prefix = NULL;
    const char *load_core_prefix = NULL;
    int core_only = 0;
    int selected_sector = -1;
    int profile_sector = -1;
    i64 profile_rows = 0;
    int sector_workers = 1;
    int count_only = 0;
    int peak_budget_gib = 0;
    for (int argument = 4; argument < argc; argument++) {
        if (strcmp(argv[argument], "--estimate") == 0) {
            estimate_only = 1;
        } else if (strcmp(argv[argument], "--force") == 0) {
            force = 1;
        } else if (strcmp(argv[argument], "--project") == 0) {
            if (use_projection || argument + 3 >= argc)
                die("--project requires SEED OVERSAMPLE HASHES");
            projection_seed = twop_parse_u64(argv[++argument], "SEED");
            oversample = parse_positive_int(argv[++argument], "OVERSAMPLE");
            hash_count = parse_positive_int(argv[++argument], "HASHES");
            use_projection = 1;
        } else if (strcmp(argv[argument], "--project-slack") == 0) {
            if (use_projection || argument + 3 >= argc)
                die("--project-slack requires SEED EXTRA HASHES");
            projection_seed = twop_parse_u64(argv[++argument], "SEED");
            projection_slack =
                parse_positive_int(argv[++argument], "EXTRA");
            hash_count = parse_positive_int(argv[++argument], "HASHES");
            use_projection = 1;
        } else if (strcmp(argv[argument], "--block-finish") == 0) {
            use_block_finish = 1;
        } else if (strcmp(argv[argument], "--save-core") == 0) {
            if (save_core_prefix || argument + 1 >= argc)
                die("--save-core requires one PREFIX");
            save_core_prefix = argv[++argument];
        } else if (strcmp(argv[argument], "--load-core") == 0) {
            if (load_core_prefix || argument + 1 >= argc)
                die("--load-core requires one PREFIX");
            load_core_prefix = argv[++argument];
        } else if (strcmp(argv[argument], "--core-only") == 0) {
            core_only = 1;
        } else if (strcmp(argv[argument], "--sector") == 0) {
            if (selected_sector >= 0 || argument + 1 >= argc)
                die("--sector requires one residue R");
            u64 value = twop_parse_u64(argv[++argument], "R");
            if (value > INT_MAX)
                die("--sector R exceeds int range");
            selected_sector = (int)value;
        } else if (strcmp(argv[argument], "--profile-sector") == 0) {
            if (profile_sector >= 0 || argument + 2 >= argc)
                die("--profile-sector requires R and ROWS");
            u64 residue_value =
                twop_parse_u64(argv[++argument], "profile R");
            u64 rows_value =
                twop_parse_u64(argv[++argument], "profile ROWS");
            if (residue_value > INT_MAX || rows_value == 0 ||
                rows_value > INT64_MAX)
                die("--profile-sector argument out of range");
            profile_sector = (int)residue_value;
            profile_rows = (i64)rows_value;
        } else if (strcmp(argv[argument], "--sector-workers") == 0) {
            if (sector_workers != 1 || argument + 1 >= argc)
                die("--sector-workers requires one positive K");
            sector_workers =
                parse_positive_int(argv[++argument], "sector workers");
        } else if (strcmp(argv[argument], "--count-only") == 0) {
            count_only = 1;
        } else if (strcmp(argv[argument], "--peak-budget-gib") == 0) {
            if (peak_budget_gib != 0 || argument + 1 >= argc)
                die("--peak-budget-gib requires one positive G");
            peak_budget_gib =
                parse_positive_int(argv[++argument], "peak budget GiB");
            if (peak_budget_gib > 16384)
                die("peak budget exceeds implementation limit");
        } else {
            fprintf(stderr, "unknown option: %s\n", argv[argument]);
            return EXIT_FAILURE;
        }
    }
    if (!is_odd_prime(n_level))
        die("require N to be an odd prime");
    if (!is_odd_prime(prime))
        die("require P to be an odd prime");
    if (gcd_int(n_level, multiplier) != 1)
        die("require gcd(N,M)=1");
    if ((multiplier & 1) != 0)
        die("require even M");
    if (multiplier % prime != 0 || (multiplier / prime) % prime == 0)
        die("require P to divide M exactly once");
    if ((i64)n_level * prime > INT_MAX)
        die("N*P exceeds local sector indexing range");
    int local_multiplier = multiplier / prime;
    if ((local_multiplier & 1) != 0)
        die("require even M/P");
    if (save_core_prefix && load_core_prefix)
        die("--save-core and --load-core are mutually exclusive");
    if (core_only && !save_core_prefix)
        die("--core-only requires --save-core");
    if (core_only && selected_sector >= 0)
        die("--core-only and --sector are mutually exclusive");
    if (core_only && profile_sector >= 0)
        die("--core-only and --profile-sector are mutually exclusive");
    if (selected_sector >= n_level)
        die("--sector R requires 0 <= R < N");
    if (profile_sector >= n_level)
        die("--profile-sector R requires 0 <= R < N");
    if (selected_sector >= 0 && use_projection)
        die("--sector cannot be combined with --project");
    if (profile_sector >= 0 &&
        (selected_sector >= 0 || use_projection))
        die("--profile-sector cannot be combined with --sector/--project");
    if (sector_workers > 1 && !use_block_finish)
        if (!count_only)
            die("--sector-workers requires --block-finish or --count-only");
    if (sector_workers > 1 &&
        (core_only || selected_sector >= 0 || profile_sector >= 0))
        die("--sector-workers is only for a complete run");
    if (count_only &&
        (core_only || selected_sector >= 0 || profile_sector >= 0 ||
         use_projection))
        die("--count-only cannot be combined with another terminal mode");
    if (sector_workers > n_level)
        sector_workers = n_level;
#if !defined(_OPENMP)
    if (sector_workers > 1)
        die("--sector-workers requires an OpenMP build");
#endif
    u64 q_total = (u64)(unsigned int)n_level *
                  (u64)(unsigned int)multiplier;

    int pfree_count = 0;
    int pdiv_count = 0;
    i64 pfree_even_rows = 0;
    i64 pdiv_even_rows = 0;
    i64 pfree_nonzeros = 0;
    i64 pdiv_nonzeros = 0;
    DivisorData *pfree = twop_make_data(
        n_level, multiplier, prime, 0, !estimate_only, &pfree_count,
        &pfree_even_rows, &pfree_nonzeros);
    DivisorData *pdiv = twop_make_data(
        n_level, multiplier, prime, 1, !estimate_only, &pdiv_count,
        &pdiv_even_rows, &pdiv_nonzeros);

    int local_d = local_multiplier / 2;
    int global_d = multiplier / 2;
    size_t local_arena_u64 = compressed_arena_u64(local_d);
    uint64_t local_arena_bytes =
        (uint64_t)local_arena_u64 * sizeof(u64);
    i64 common_rows[2] = {0, 0};
    for (int parity = 0; parity <= 1; parity++) {
        for (int index = 0; index < pfree_count; index++) {
            int step = local_multiplier / pfree[index].q;
            int row_parity = selected_v_parity(parity, step);
            i64 lower;
            i64 upper;
            core_interval(n_level * prime, parity, pfree[index].h,
                          &lower, &upper);
            common_rows[parity] +=
                count_selected(lower, upper, row_parity);
        }
    }
    printf("N=%d M=%d Q=%" PRIu64 " split_prime=%d L=%d "
           "global_parity_columns=%d local_columns=%d\n",
           n_level, multiplier, q_total, prime, local_multiplier,
           global_d, local_d);
    printf("ROWS even_P_free=%lld even_P_divisible=%lld "
           "even_total=%lld equation_margin_after_W=%lld\n",
           (long long)pfree_even_rows, (long long)pdiv_even_rows,
           (long long)(pfree_even_rows + pdiv_even_rows),
           (long long)(pfree_even_rows + pdiv_even_rows + global_d -
                       (i64)n_level * global_d));
    printf("COMMON P_free_rows parity0=%lld parity1=%lld "
           "row_defect_lower_bounds=%lld,%lld\n",
           (long long)common_rows[0], (long long)common_rows[1],
           (long long)(local_d - common_rows[0]),
           (long long)(local_d - common_rows[1]));
    printf("WORK P_free_nnz=%lld P_divisible_nnz=%lld "
           "one_local_compressed_arena=%.3f_GiB MemAvailable=%.3f_GiB\n",
           (long long)pfree_nonzeros, (long long)pdiv_nonzeros,
           (double)local_arena_bytes /
               (double)(UINT64_C(1) << 30),
           (double)available_memory_bytes() /
               (double)(UINT64_C(1) << 30));

    /* This is a planning scenario, not a bound: it assumes every P-free
     * common and endpoint row adds rank.  The checkpoint and --sector modes
     * replace these figures by measurements before a large full run. */
    uint64_t unit_bytes =
        (uint64_t)(pfree_count + pdiv_count) * sizeof(DivisorData);
    for (int index = 0; index < pfree_count; index++)
        unit_bytes += (uint64_t)pfree[index].q * sizeof(int);
    for (int index = 0; index < pdiv_count; index++)
        unit_bytes += (uint64_t)pdiv[index].q * sizeof(int);
    uint64_t assumed_common_snapshot_bytes[2];
    uint64_t assumed_common_total = 0;
    for (int parity = 0; parity <= 1; parity++) {
        i64 rank64 = common_rows[parity];
        if (rank64 > local_d)
            rank64 = local_d;
        int rank = (int)rank64;
        int nullity = local_d - rank;
        assumed_common_snapshot_bytes[parity] =
            snapshot_storage_bytes(local_d, rank, nullity);
        assumed_common_total += assumed_common_snapshot_bytes[parity];
    }
    uint64_t assumed_sector_peak = 0;
    int assumed_coefficient_min = INT_MAX;
    int assumed_coefficient_max = 0;
    i64 sector_pdiv_min = INT64_MAX;
    i64 sector_pdiv_max = 0;
    for (int residue = 0; residue < n_level; residue++) {
        uint64_t subsector_snapshots = 0;
        uint64_t maximum_active_restore = 0;
        i64 coefficient_count64 = 0;
        for (int subresidue = 0; subresidue < prime; subresidue++) {
            int combined_residue = residue + n_level * subresidue;
            int parity = combined_residue & 1;
            int exceptions = count_sector_exceptions(
                n_level * prime, local_multiplier, combined_residue,
                pfree, pfree_count);
            i64 rank64 = common_rows[parity] + exceptions;
            if (rank64 > local_d)
                rank64 = local_d;
            int rank = (int)rank64;
            int nullity = local_d - rank;
            coefficient_count64 += nullity;
            subsector_snapshots +=
                snapshot_storage_bytes(local_d, rank, nullity);
            Snapshot assumed;
            memset(&assumed, 0, sizeof(assumed));
            assumed.d = local_d;
            i64 assumed_rank64 = common_rows[parity];
            if (assumed_rank64 > local_d)
                assumed_rank64 = local_d;
            assumed.rank = (int)assumed_rank64;
            assumed.nullity = local_d - assumed.rank;
            assumed.words = (assumed.nullity + 63) / 64;
            uint64_t active =
                (uint64_t)restored_sector_arena_u64(&assumed, exceptions) *
                    sizeof(u64) +
                crref_auxiliary_bytes(local_d);
            if (active > maximum_active_restore)
                maximum_active_restore = active;
        }
        if (coefficient_count64 > INT_MAX)
            die("independence-scenario coefficient count exceeds int range");
        int coefficient_count = (int)coefficient_count64;
        if (coefficient_count < assumed_coefficient_min)
            assumed_coefficient_min = coefficient_count;
        if (coefficient_count > assumed_coefficient_max)
            assumed_coefficient_max = coefficient_count;
        uint64_t coupling =
            (uint64_t)compressed_arena_u64(coefficient_count) *
                sizeof(u64) +
            crref_auxiliary_bytes(coefficient_count);
        uint64_t build_peak = assumed_common_total + unit_bytes +
                              subsector_snapshots + maximum_active_restore;
        uint64_t coupling_peak = assumed_common_total + unit_bytes +
                                 subsector_snapshots + coupling;
        uint64_t sector_peak =
            build_peak > coupling_peak ? build_peak : coupling_peak;
        if (sector_peak > assumed_sector_peak)
            assumed_sector_peak = sector_peak;

        i64 rows = 0;
        for (int index = 0; index < pdiv_count; index++) {
            int step = multiplier / pdiv[index].q;
            int parity = selected_v_parity(residue & 1, step);
            i64 lower;
            i64 upper;
            legal_interval(n_level, residue, pdiv[index].h,
                           &lower, &upper);
            rows += count_selected(lower, upper, parity);
        }
        if (rows < sector_pdiv_min)
            sector_pdiv_min = rows;
        if (rows > sector_pdiv_max)
            sector_pdiv_max = rows;
    }
    uint64_t assumed_core_peak = local_arena_bytes +
                                 crref_auxiliary_bytes(local_d) +
                                 assumed_common_total + unit_bytes;
    printf("INDEPENDENCE_SCENARIO common_snapshots=%.3f_GiB "
           "checkpoint_files=%.3f_GiB coefficient_range=%d..%d "
           "P_divisible_rows_per_sector=%lld..%lld "
           "core_stage_peak=%.3f_GiB sector_stage_peak=%.3f_GiB "
           "unit_tables=%.3f_GiB\n",
           (double)assumed_common_total /
               (double)(UINT64_C(1) << 30),
           (double)(assumed_common_total +
                    2 * (uint64_t)sizeof(TwopCoreHeader)) /
               (double)(UINT64_C(1) << 30),
           assumed_coefficient_min, assumed_coefficient_max,
           (long long)sector_pdiv_min, (long long)sector_pdiv_max,
           (double)assumed_core_peak /
               (double)(UINT64_C(1) << 30),
           (double)assumed_sector_peak /
               (double)(UINT64_C(1) << 30),
           (double)unit_bytes / (double)(UINT64_C(1) << 30));
    if (estimate_only) {
        twop_destroy_data(pfree, pfree_count);
        twop_destroy_data(pdiv, pdiv_count);
        return EXIT_SUCCESS;
    }

    Snapshot common[2];
    memset(common, 0, sizeof(common));
    double total_started = twop_now_seconds();
    for (int parity = 0; parity <= 1; parity++) {
        double core_started = twop_now_seconds();
        if (load_core_prefix) {
            common[parity] = twop_load_core(
                load_core_prefix, n_level, multiplier, prime, parity,
                common_rows[parity]);
        } else {
            guard_additional_allocation(
                local_arena_bytes + crref_auxiliary_bytes(local_d), force,
                "two-prime P-free common core");
            Crref core = crref_create(local_d, local_arena_u64);
            i64 rows = build_common_core(
                &core, n_level * prime, local_multiplier, parity,
                pfree, pfree_count);
            if (rows != common_rows[parity])
                die("internal P-free common-row count mismatch");
            common[parity] = snapshot_from_crref(&core);
            uint64_t snapshot_nnz = twop_snapshot_nnz(&common[parity]);
            uint64_t snapshot_bits =
                (uint64_t)common[parity].rank *
                (uint64_t)common[parity].nullity;
            printf("P_FREE_CORE parity=%d rows=%lld rank=%d/%d nullity=%d "
                   "snapshot=%.3f_GiB density=%.6f peak=%.3f_GiB\n",
                   parity, (long long)rows, common[parity].rank, local_d,
                   common[parity].nullity,
                   (double)snapshot_storage_bytes(
                       local_d, common[parity].rank,
                       common[parity].nullity) /
                       (double)(UINT64_C(1) << 30),
                   snapshot_bits == 0
                       ? 0.0
                       : (double)snapshot_nnz / (double)snapshot_bits,
                   (double)core.peak_used_bytes /
                       (double)(UINT64_C(1) << 30));
            fflush(stdout);
            crref_destroy(&core);
        }
        if (save_core_prefix)
            twop_save_core(save_core_prefix, n_level, multiplier, prime,
                            parity, common_rows[parity], &common[parity]);
        printf("CORE_STAGE parity=%d elapsed=%.3f_s\n", parity,
               twop_now_seconds() - core_started);
    }

    if (core_only) {
        printf("CORE_ONLY_COMPLETE prefix=%s elapsed=%.3f_s\n",
               save_core_prefix, twop_now_seconds() - total_started);
        for (int parity = 0; parity <= 1; parity++)
            snapshot_destroy(&common[parity]);
        twop_destroy_data(pfree, pfree_count);
        twop_destroy_data(pdiv, pdiv_count);
        return EXIT_SUCCESS;
    }

    uint64_t actual_common_bytes = 0;
    for (int parity = 0; parity <= 1; parity++)
        actual_common_bytes += snapshot_storage_bytes(
            common[parity].d, common[parity].rank,
            common[parity].nullity);
    uint64_t sector_dynamic_upper = twop_sector_dynamic_upper(
        common, n_level, multiplier, prime, pfree, pfree_count);
    printf("MEASURED_CORE_PLAN common_snapshots=%.3f_GiB "
           "one_sector_additional_upper=%.3f_GiB "
           "one_sector_total_upper=%.3f_GiB\n",
           (double)actual_common_bytes /
               (double)(UINT64_C(1) << 30),
           (double)sector_dynamic_upper /
               (double)(UINT64_C(1) << 30),
           (double)(actual_common_bytes + unit_bytes +
                    sector_dynamic_upper) /
               (double)(UINT64_C(1) << 30));
    uint64_t peak_budget_bytes =
        (uint64_t)peak_budget_gib << 30;
    if (peak_budget_bytes != 0) {
        uint64_t fixed_sector_bytes = actual_common_bytes + unit_bytes;
        int requested_workers = sector_workers;
        while (sector_workers > 1 &&
               fixed_sector_bytes +
                       (uint64_t)sector_workers * sector_dynamic_upper >
                   peak_budget_bytes)
            sector_workers--;
        uint64_t pass_peak =
            fixed_sector_bytes +
            (uint64_t)sector_workers * sector_dynamic_upper;
        if (pass_peak > peak_budget_bytes)
            die("one residue sector exceeds the explicit peak budget");
        printf("PEAK_BUDGET budget=%.3f_GiB requested_workers=%d "
               "count_workers=%d count_peak_upper=%.3f_GiB\n",
               (double)peak_budget_bytes /
                   (double)(UINT64_C(1) << 30),
               requested_workers, sector_workers,
               (double)pass_peak / (double)(UINT64_C(1) << 30));
    }
    guard_additional_allocation(sector_dynamic_upper, force,
                                "one two-prime residue stage");

    if (selected_sector >= 0) {
        double sector_started = twop_now_seconds();
        i64 rows = 0;
        size_t peak_coupling = 0;
        int kernel_dimension = twop_process_sector(
            common, n_level, multiplier, prime, selected_sector,
            pfree, pfree_count, pdiv, pdiv_count, NULL, NULL, NULL, NULL,
            0,
            &rows, &peak_coupling);
        printf("SECTOR_BENCHMARK_COMPLETE residue=%d rows=%lld "
               "kernel_dim=%d peak_coupling=%.3f_GiB elapsed=%.3f_s\n",
               selected_sector, (long long)rows, kernel_dimension,
               (double)peak_coupling / (double)(UINT64_C(1) << 30),
               twop_now_seconds() - sector_started);
        if (use_block_finish) {
            int output_words = (global_d + 63) / 64;
            uint64_t output_bytes =
                (uint64_t)kernel_dimension * (uint64_t)output_words *
                sizeof(u64);
            uint64_t block_table_bytes =
                (uint64_t)((1 << TWOP_FINISH_BLOCK_BITS) +
                           TWOP_FINISH_BLOCK_BITS) *
                (uint64_t)output_words * sizeof(u64);
            guard_additional_allocation(output_bytes + block_table_bytes +
                                            sector_dynamic_upper,
                                        force,
                                        "one materialized two-prime sector");
            TwopProjection direct_projection;
            direct_projection.direct = 1;
            direct_projection.seed = 0;
            direct_projection.hash_count = 0;
            direct_projection.bucket_count = global_d;
            TwopRowMatrix materialized =
                twop_row_matrix_create(global_d, kernel_dimension);
            u64 *unused_work =
                xcalloc((size_t)output_words, sizeof(*unused_work));
            int inverse_n = inverse_mod(n_level % multiplier, multiplier);
            i64 numerator =
                (i64)(selected_sector & 1) +
                (i64)inverse_n * selected_sector;
            if (numerator & 1)
                die("internal W half-shift is not integral");
            int shift = positive_mod_i64(numerator / 2, global_d);
            i64 second_rows = 0;
            double materialize_started = twop_now_seconds();
            int second_kernel_dimension = twop_process_sector(
                common, n_level, multiplier, prime, selected_sector,
                pfree, pfree_count, pdiv, pdiv_count, NULL, unused_work,
                &materialized, &direct_projection, shift,
                &second_rows, &peak_coupling);
            double materialize_elapsed =
                twop_now_seconds() - materialize_started;
            if (second_rows != rows ||
                second_kernel_dimension != kernel_dimension ||
                materialized.count != kernel_dimension)
                die("materialized sector does not match counting pass");
            double rank_started = twop_now_seconds();
            int image_rank = twop_block_rank(&materialized);
            printf("SECTOR_MATERIALIZE_COMPLETE residue=%d rows=%d "
                   "image_rank=%d/%d allocation=%.3f_GiB "
                   "materialize_elapsed=%.3f_s rank_elapsed=%.3f_s\n",
                   selected_sector, materialized.count, image_rank,
                   kernel_dimension,
                   (double)(output_bytes + block_table_bytes) /
                       (double)(UINT64_C(1) << 30),
                   materialize_elapsed,
                   twop_now_seconds() - rank_started);
            free(unused_work);
            twop_row_matrix_destroy(&materialized);
        }
        for (int parity = 0; parity <= 1; parity++)
            snapshot_destroy(&common[parity]);
        twop_destroy_data(pfree, pfree_count);
        twop_destroy_data(pdiv, pdiv_count);
        return EXIT_SUCCESS;
    }

    if (profile_sector >= 0) {
        double profile_started = twop_now_seconds();
        twop_profile_sector_rows(
            common, n_level, multiplier, prime, profile_sector,
            pfree, pfree_count, pdiv, pdiv_count, profile_rows);
        printf("ROW_PROFILE_COMPLETE elapsed=%.3f_s\n",
               twop_now_seconds() - profile_started);
        for (int parity = 0; parity <= 1; parity++)
            snapshot_destroy(&common[parity]);
        twop_destroy_data(pfree, pfree_count);
        twop_destroy_data(pdiv, pdiv_count);
        return EXIT_SUCCESS;
    }

    /* Pass 1 determines the exact number of rows in the final W image. */
    int *sector_kernel_dimensions =
        xcalloc((size_t)n_level, sizeof(*sector_kernel_dimensions));
    i64 *sector_pdiv_rows =
        xcalloc((size_t)n_level, sizeof(*sector_pdiv_rows));
    size_t *sector_coupling_peaks =
        xcalloc((size_t)n_level, sizeof(*sector_coupling_peaks));
    i64 total_even_kernel = 0;
    i64 checked_pdiv_rows = 0;
    size_t peak_coupling = 0;
    double pass1_started = twop_now_seconds();
#if defined(_OPENMP)
    int outer_thread_budget = omp_get_max_threads();
    int inner_threads = outer_thread_budget / sector_workers;
    if (inner_threads < 1)
        inner_threads = 1;
    if (sector_workers > 1)
        omp_set_max_active_levels(2);
#else
    int outer_thread_budget = 1;
    int inner_threads = 1;
#endif
    printf("SECTOR_PARALLELISM workers=%d inner_threads=%d "
           "thread_budget=%d\n",
           sector_workers, inner_threads, outer_thread_budget);
    fflush(stdout);
#if defined(_OPENMP)
#pragma omp parallel num_threads(sector_workers) if(sector_workers > 1)
    {
        omp_set_num_threads(inner_threads);
#pragma omp for schedule(dynamic, 1)
#endif
        for (int residue = 0; residue < n_level; residue++) {
            sector_kernel_dimensions[residue] = twop_process_sector(
                common, n_level, multiplier, prime, residue,
                pfree, pfree_count, pdiv, pdiv_count, NULL, NULL, NULL,
                NULL, 0, &sector_pdiv_rows[residue],
                &sector_coupling_peaks[residue]);
        }
#if defined(_OPENMP)
    }
#endif
    for (int residue = 0; residue < n_level; residue++) {
        total_even_kernel += sector_kernel_dimensions[residue];
        checked_pdiv_rows += sector_pdiv_rows[residue];
        if (sector_coupling_peaks[residue] > peak_coupling)
            peak_coupling = sector_coupling_peaks[residue];
    }
    if (checked_pdiv_rows != pdiv_even_rows)
        die("P-divisible rows did not partition across N sectors");
    if (total_even_kernel > global_d)
        die("coprime kernel exceeds W codomain; full rank impossible");
    printf("PASS1_COMPLETE elapsed=%.3f_s\n",
           twop_now_seconds() - pass1_started);

    if (count_only) {
        printf("COUNT_ONLY_COMPLETE even_kernel_rows=%lld elapsed=%.3f_s\n",
               (long long)total_even_kernel,
               twop_now_seconds() - total_started);
        free(sector_coupling_peaks);
        free(sector_pdiv_rows);
        free(sector_kernel_dimensions);
        for (int parity = 0; parity <= 1; parity++)
            snapshot_destroy(&common[parity]);
        twop_destroy_data(pfree, pfree_count);
        twop_destroy_data(pdiv, pdiv_count);
        return EXIT_SUCCESS;
    }

    TwopProjection projection;
    projection.direct = !use_projection;
    projection.seed = projection_seed;
    projection.hash_count = use_projection ? hash_count : 0;
    if (use_projection) {
        if (projection_slack >= 0) {
            if (total_even_kernel > INT_MAX - projection_slack)
                die("projection bucket-count overflow");
            projection.bucket_count =
                (int)total_even_kernel + projection_slack;
        } else {
            if (total_even_kernel > INT_MAX / oversample)
                die("projection bucket-count overflow");
            projection.bucket_count =
                (int)total_even_kernel * oversample;
        }
    } else {
        projection.bucket_count = global_d;
    }
    int row_count = (int)total_even_kernel;
    uint64_t output_bytes =
        (uint64_t)row_count *
            (uint64_t)((projection.bucket_count + 63) / 64) *
            sizeof(u64) +
        (uint64_t)row_count * sizeof(int) +
        (uint64_t)projection.bucket_count * sizeof(int);
    uint64_t block_table_bytes =
        use_block_finish
            ? (uint64_t)((1 << TWOP_FINISH_BLOCK_BITS) +
                         TWOP_FINISH_BLOCK_BITS) *
                  (uint64_t)((projection.bucket_count + 63) / 64) *
                  sizeof(u64)
            : 0;
    int materialize_workers = sector_workers;
    if (peak_budget_bytes != 0) {
        uint64_t fixed_output_bytes = actual_common_bytes + unit_bytes +
                                      output_bytes + block_table_bytes;
        while (materialize_workers > 1 &&
               fixed_output_bytes +
                       (uint64_t)materialize_workers *
                           sector_dynamic_upper >
                   peak_budget_bytes)
            materialize_workers--;
        uint64_t pass_peak =
            fixed_output_bytes +
            (uint64_t)materialize_workers * sector_dynamic_upper;
        if (pass_peak > peak_budget_bytes)
            die("W image plus one residue sector exceeds the explicit "
                "peak budget");
        printf("W_MEMORY_PLAN budget=%.3f_GiB materialize_workers=%d "
               "peak_upper=%.3f_GiB\n",
               (double)peak_budget_bytes /
                   (double)(UINT64_C(1) << 30),
               materialize_workers,
               (double)pass_peak / (double)(UINT64_C(1) << 30));
    }
    guard_additional_allocation(output_bytes + block_table_bytes +
                                    (uint64_t)materialize_workers *
                                        sector_dynamic_upper,
                                force,
                                "two-prime W image");
    DenseOutput output;
    TwopRowMatrix raw_output;
    memset(&output, 0, sizeof(output));
    memset(&raw_output, 0, sizeof(raw_output));
    if (use_block_finish)
        raw_output = twop_row_matrix_create(projection.bucket_count,
                                             row_count);
    else
        output = dense_output_create(projection.bucket_count, row_count);
    int output_words = (projection.bucket_count + 63) / 64;
    u64 *output_work =
        xcalloc((size_t)output_words, sizeof(*output_work));
    printf("W_SETUP even_kernel_rows=%d mode=%s finish=%s columns=%d "
           "allocation=%.3f_GiB block_table=%.3f_GiB "
           "peak_coupling_pass1=%.3f_GiB\n",
           row_count, use_projection ? "projected" : "direct",
           use_block_finish ? "parallel_block" : "serial_incremental",
           projection.bucket_count,
           (double)output_bytes / (double)(UINT64_C(1) << 30),
           (double)block_table_bytes / (double)(UINT64_C(1) << 30),
           (double)peak_coupling / (double)(UINT64_C(1) << 30));

    int inverse_n = inverse_mod(n_level % multiplier, multiplier);
    int inserted = 0;
    checked_pdiv_rows = 0;
    double pass2_started = twop_now_seconds();
    if (use_block_finish) {
        int *sector_row_offsets =
            xcalloc((size_t)n_level + 1, sizeof(*sector_row_offsets));
        for (int residue = 0; residue < n_level; residue++)
            sector_row_offsets[residue + 1] =
                sector_row_offsets[residue] +
                sector_kernel_dimensions[residue];
        if (sector_row_offsets[n_level] != row_count)
            die("internal sector row-offset mismatch");
#if defined(_OPENMP)
#pragma omp parallel num_threads(materialize_workers) if(materialize_workers > 1)
        {
            int materialize_inner_threads =
                outer_thread_budget / materialize_workers;
            if (materialize_inner_threads < 1)
                materialize_inner_threads = 1;
            omp_set_num_threads(materialize_inner_threads);
#pragma omp for schedule(dynamic, 1)
#endif
            for (int residue = 0; residue < n_level; residue++) {
                i64 numerator = (i64)(residue & 1) +
                                (i64)inverse_n * residue;
                if (numerator & 1)
                    die("internal W half-shift is not integral");
                int shift = positive_mod_i64(numerator / 2, global_d);
                TwopRowMatrix sector_output = raw_output;
                sector_output.rows =
                    raw_output.rows +
                    (size_t)sector_row_offsets[residue] * raw_output.words;
                sector_output.capacity = sector_kernel_dimensions[residue];
                sector_output.count = 0;
                size_t second_peak = 0;
                int kernel_dimension = twop_process_sector(
                    common, n_level, multiplier, prime, residue,
                    pfree, pfree_count, pdiv, pdiv_count, NULL, NULL,
                    &sector_output, &projection, shift,
                    &sector_pdiv_rows[residue], &second_peak);
                if (kernel_dimension != sector_kernel_dimensions[residue] ||
                    sector_output.count != kernel_dimension)
                    die("parallel second-pass sector count mismatch");
                sector_coupling_peaks[residue] = second_peak;
                printf("W sector=%d rows_appended=%d row_range=%d..%d/%d\n",
                       residue, sector_output.count,
                       sector_row_offsets[residue],
                       sector_row_offsets[residue + 1], row_count);
                fflush(stdout);
            }
#if defined(_OPENMP)
        }
#endif
        raw_output.count = row_count;
        free(sector_row_offsets);
        inserted = row_count;
        for (int residue = 0; residue < n_level; residue++) {
            checked_pdiv_rows += sector_pdiv_rows[residue];
            if (sector_coupling_peaks[residue] > peak_coupling)
                peak_coupling = sector_coupling_peaks[residue];
        }
    } else {
        for (int residue = 0; residue < n_level; residue++) {
            i64 numerator = (i64)(residue & 1) +
                            (i64)inverse_n * residue;
            if (numerator & 1)
                die("internal W half-shift is not integral");
            int shift = positive_mod_i64(numerator / 2, global_d);
            int old_rank = output.rank;
            size_t second_peak = 0;
            int kernel_dimension = twop_process_sector(
                common, n_level, multiplier, prime, residue,
                pfree, pfree_count, pdiv, pdiv_count, &output,
                output_work, NULL, &projection, shift,
                &sector_pdiv_rows[residue], &second_peak);
            inserted += kernel_dimension;
            checked_pdiv_rows += sector_pdiv_rows[residue];
            if (second_peak > peak_coupling)
                peak_coupling = second_peak;
            printf("W sector=%d image_gain=%d image_rank=%d/%d\n",
                   residue, output.rank - old_rank, output.rank,
                   row_count);
        }
    }
    if (inserted != row_count || checked_pdiv_rows != pdiv_even_rows)
        die("second-pass count mismatch");
    printf("PASS2_COMPLETE elapsed=%.3f_s total_elapsed=%.3f_s\n",
           twop_now_seconds() - pass2_started,
           twop_now_seconds() - total_started);

    int output_rank =
        use_block_finish ? twop_block_rank(&raw_output) : output.rank;
    i64 full_coprime_kernel = 2 * total_even_kernel;
    i64 full_coprime_rank = (i64)q_total - full_coprime_kernel;
    int certified = output_rank == row_count;
    if (certified) {
        printf("TWO_PRIME_CERTIFIED even_W_rank=%d/%d "
               "full_coprime_rank=%lld/%" PRIu64 " W_gain=%lld/%lld "
               "final_defect=0 assisted_rank=%" PRIu64 "/%" PRIu64 "\n",
               output_rank, row_count, (long long)full_coprime_rank,
               q_total, (long long)full_coprime_kernel,
               (long long)full_coprime_kernel, q_total, q_total);
    } else if (use_projection) {
        printf("TWO_PRIME_PROJECTION_INCONCLUSIVE image_rank=%d/%d "
               "retry_seed_or_increase_oversample=1\n",
               output_rank, row_count);
    } else {
        i64 full_defect = 2 * (total_even_kernel - output_rank);
        printf("TWO_PRIME_EXACT_DEFECT even_W_rank=%d/%d "
               "full_coprime_rank=%lld/%" PRIu64 " final_defect=%lld\n",
               output_rank, row_count, (long long)full_coprime_rank,
               q_total, (long long)full_defect);
    }

    free(output_work);
    if (use_block_finish)
        twop_row_matrix_destroy(&raw_output);
    else
        dense_output_destroy(&output);
    free(sector_coupling_peaks);
    free(sector_pdiv_rows);
    free(sector_kernel_dimensions);
    for (int parity = 0; parity <= 1; parity++)
        snapshot_destroy(&common[parity]);
    twop_destroy_data(pfree, pfree_count);
    twop_destroy_data(pdiv, pdiv_count);
    return certified ? EXIT_SUCCESS : (use_projection ? 2 : EXIT_SUCCESS);
}
