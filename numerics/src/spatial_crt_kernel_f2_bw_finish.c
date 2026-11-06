/* Finish the exact prime-level CRT calculation from one CADO-NFS GF(2)
 * Block Wiedemann common-core calculation.
 *
 * This is a non-overwriting companion to
 * spatial_crt_kernel_f2_parity_core.c.  The input core is the residue-parity
 * zero common core inside the global even-j block.  CADO cleanup files may
 * contain solutions in added square-completion coordinates; those tail
 * coordinates are eliminated exactly before the core kernel is used.
 *
 * Only one expensive common-core solve is needed.  If x is the compressed
 * coordinate in Z/(M/2)Z, the map
 *
 *     v -> -1-v,       x -> -1-x
 *
 * sends every residue-parity zero core row to a residue-parity one core row.
 * The latter has one additional row precisely for each q|M whose exact
 * buffered radius H_q is divisible by N.  These sparse exceptional rows are
 * imposed directly on the reflected kernel.  Every literal sector endpoint
 * and the W_N top-up are then handled by the audited routines in
 * spatial_crt_kernel_f2_parity_core.c.  Reflection j -> Q-1-j supplies the
 * other global coordinate-parity block at the end.
 *
 * Compile:
 *   gcc -std=gnu11 -O3 -march=native -mbmi2 -fopenmp \
 *       -Wall -Wextra -Werror -o spatial_crt_kernel_f2_bw_finish \
 *       spatial_crt_kernel_f2_bw_finish.c
 *
 * Usage:
 *   ./spatial_crt_kernel_f2_bw_finish N Q CORE0.bin W1 [W2 ...]
 *
 * CORE0.bin must be the matrix exported by spatial_crt_bw_export with
 * PARITY=0.  Each W file stores 64 CADO cleanup lanes as one little-endian
 * uint64 per coordinate.
 */

#include <inttypes.h>
#include <sys/stat.h>

/* Reuse the exact CRT/endpoints/RRE implementation without changing the
 * historical source.  Its command-line entry point is retained under a
 * private name; this file supplies the public main below. */
#define main spatial_crt_kernel_f2_parity_core_original_main
#include "spatial_crt_kernel_f2_parity_core.c"
#undef main

typedef struct {
    int d;
    int kernel_dimension;
    int kernel_words;
    u64 *coordinate_masks;
    size_t candidate_lanes;
    size_t full_solution_rank;
    size_t projected_rank;
    size_t tail_rank;
    size_t cleaned_candidate_lanes;
    i64 matrix_rows;
    i64 matrix_nonzeros;
} BwKernel;

static uint64_t bw_file_size(const char *name) {
    struct stat information;
    if (stat(name, &information) != 0) {
        fprintf(stderr, "cannot stat %s: %s\n", name, strerror(errno));
        exit(EXIT_FAILURE);
    }
    if (information.st_size < 0)
        die("negative file size");
    return (uint64_t)information.st_size;
}

static char *bw_companion_name(const char *matrix_name, const char *kind) {
    size_t length = strlen(matrix_name);
    if (length < 4 || strcmp(matrix_name + length - 4, ".bin") != 0)
        die("CORE0 matrix name must end in .bin");
    size_t kind_length = strlen(kind);
    char *result = xmalloc(length + kind_length + 1);
    memcpy(result, matrix_name, length - 4);
    result[length - 4] = '\0';
    strcat(result, kind);
    strcat(result, ".bin");
    return result;
}

static uint32_t bw_read_u32_le(FILE *file) {
    unsigned char bytes[4];
    if (fread(bytes, sizeof(bytes), 1, file) != 1)
        die("unexpected end of matrix or read error");
    return (uint32_t)bytes[0] | ((uint32_t)bytes[1] << 8) |
           ((uint32_t)bytes[2] << 16) | ((uint32_t)bytes[3] << 24);
}

static u64 bw_read_u64_le(FILE *file) {
    unsigned char bytes[8];
    if (fread(bytes, sizeof(bytes), 1, file) != 1)
        die("unexpected end of solution file or read error");
    u64 value = 0;
    for (unsigned int index = 0; index < 8; index++)
        value |= (u64)bytes[index] << (8 * index);
    return value;
}

static int bw_vector_is_zero(const u64 *vector, size_t words) {
    for (size_t word = 0; word < words; word++)
        if (vector[word] != 0)
            return 0;
    return 1;
}

static size_t bw_highest_set_bit(const u64 *vector, size_t words) {
    for (size_t word = words; word-- > 0;) {
        if (vector[word] != 0)
            return 64 * word + 63U -
                   (size_t)__builtin_clzll(vector[word]);
    }
    die("internal request for pivot of zero vector");
    return 0;
}

/* Insert a row into a highest-pivot echelon basis.  There is one possible
 * pivot slot per bit; each stored row occupies WORDS uint64s. */
static int bw_insert_row(u64 *basis, unsigned char *has_pivot, u64 *value,
                         size_t words) {
    while (!bw_vector_is_zero(value, words)) {
        size_t pivot = bw_highest_set_bit(value, words);
        u64 *pivot_vector = basis + pivot * words;
        if (!has_pivot[pivot]) {
            memcpy(pivot_vector, value, words * sizeof(*value));
            has_pivot[pivot] = 1;
            return 1;
        }
        for (size_t word = 0; word < words; word++)
            value[word] ^= pivot_vector[word];
    }
    return 0;
}

static unsigned int bw_parity_dot(const u64 *left, const u64 *right,
                                  size_t words) {
    unsigned int parity = 0;
    for (size_t word = 0; word < words; word++)
        parity ^= (unsigned int)__builtin_parityll(left[word] & right[word]);
    return parity & 1U;
}

static size_t bw_rank_rows(const u64 *rows, size_t row_count,
                           size_t bit_count, size_t words,
                           unsigned char *final_has_pivot) {
    if (bit_count > SIZE_MAX / words || bit_count * words > SIZE_MAX / 8)
        die("small echelon allocation overflow");
    u64 *basis = xcalloc(bit_count * words, sizeof(*basis));
    unsigned char *has_pivot = xcalloc(bit_count, sizeof(*has_pivot));
    u64 *work = xmalloc(words * sizeof(*work));
    size_t rank = 0;
    for (size_t row = 0; row < row_count; row++) {
        memcpy(work, rows + row * words, words * sizeof(*work));
        rank += (size_t)bw_insert_row(basis, has_pivot, work, words);
    }
    if (final_has_pivot)
        memcpy(final_has_pivot, has_pivot, bit_count);
    free(work);
    free(has_pivot);
    free(basis);
    return rank;
}

static BwKernel bw_load_clean_kernel(const char *matrix_name,
                                     char **solution_names,
                                     size_t solution_count, int expected_d) {
    if (solution_count == 0)
        die("at least one CADO cleanup file is required");
    if (solution_count > SIZE_MAX / 64)
        die("too many CADO cleanup files");

    char *row_weight_name = bw_companion_name(matrix_name, ".rw");
    char *column_weight_name = bw_companion_name(matrix_name, ".cw");
    uint64_t row_weight_bytes = bw_file_size(row_weight_name);
    uint64_t column_weight_bytes = bw_file_size(column_weight_name);
    if ((row_weight_bytes & 3U) != 0 || (column_weight_bytes & 3U) != 0)
        die("matrix companion size is not a multiple of four");
    uint64_t row_count = row_weight_bytes / 4;
    uint64_t column_count = column_weight_bytes / 4;
    if (column_count != (uint64_t)expected_d)
        die("CORE0 column count does not equal M/2");

    uint64_t first_solution_bytes = bw_file_size(solution_names[0]);
    if ((first_solution_bytes & 7U) != 0)
        die("solution file size is not a multiple of eight");
    uint64_t coordinate_count = first_solution_bytes / 8;
    if (coordinate_count < column_count)
        die("solution has fewer coordinates than CORE0 columns");
    for (size_t file = 1; file < solution_count; file++)
        if (bw_file_size(solution_names[file]) != first_solution_bytes)
            die("CADO cleanup files have different sizes");
    if (coordinate_count > SIZE_MAX / sizeof(u64))
        die("solution file is too large for this machine");

    u64 **solutions = xmalloc(solution_count * sizeof(*solutions));
    for (size_t file = 0; file < solution_count; file++) {
        FILE *input = fopen(solution_names[file], "rb");
        if (!input) {
            fprintf(stderr, "cannot open %s: %s\n", solution_names[file],
                    strerror(errno));
            exit(EXIT_FAILURE);
        }
        solutions[file] =
            xmalloc((size_t)coordinate_count * sizeof(*solutions[file]));
        for (uint64_t coordinate = 0; coordinate < coordinate_count;
             coordinate++)
            solutions[file][coordinate] = bw_read_u64_le(input);
        if (fgetc(input) != EOF || ferror(input) || fclose(input) != 0)
            die("error finishing CADO cleanup file");
    }

    size_t lane_count = 64 * solution_count;
    size_t lane_words = solution_count;
    if (lane_count > SIZE_MAX / lane_words)
        die("lane echelon allocation overflow");
    u64 *basis = xcalloc(lane_count * lane_words, sizeof(*basis));
    unsigned char *has_pivot = xcalloc(lane_count, sizeof(*has_pivot));
    u64 *value = xmalloc(lane_words * sizeof(*value));

    size_t full_solution_rank = 0;
    for (uint64_t coordinate = 0; coordinate < coordinate_count;
         coordinate++) {
        for (size_t file = 0; file < solution_count; file++)
            value[file] = solutions[file][coordinate];
        full_solution_rank +=
            (size_t)bw_insert_row(basis, has_pivot, value, lane_words);
    }

    memset(basis, 0, lane_count * lane_words * sizeof(*basis));
    memset(has_pivot, 0, lane_count * sizeof(*has_pivot));
    size_t projected_rank = 0;
    for (uint64_t coordinate = 0; coordinate < column_count; coordinate++) {
        for (size_t file = 0; file < solution_count; file++)
            value[file] = solutions[file][coordinate];
        projected_rank +=
            (size_t)bw_insert_row(basis, has_pivot, value, lane_words);
    }

    memset(basis, 0, lane_count * lane_words * sizeof(*basis));
    memset(has_pivot, 0, lane_count * sizeof(*has_pivot));
    size_t tail_rank = 0;
    uint64_t tail_nonzero_coordinates = 0;
    uint64_t tail_hamming_weight = 0;
    for (uint64_t coordinate = column_count; coordinate < coordinate_count;
         coordinate++) {
        int nonzero = 0;
        for (size_t file = 0; file < solution_count; file++) {
            value[file] = solutions[file][coordinate];
            nonzero |= value[file] != 0;
            tail_hamming_weight +=
                (uint64_t)__builtin_popcountll(value[file]);
        }
        tail_nonzero_coordinates += (uint64_t)nonzero;
        tail_rank +=
            (size_t)bw_insert_row(basis, has_pivot, value, lane_words);
    }

    /* The tail rows now span the constraints on lane coefficients.  With
     * highest pivots, solve those equations in increasing pivot order. */
    size_t clean_count = lane_count - tail_rank;
    if (clean_count == 0)
        die("square-completion tail leaves no candidate vector");
    if (clean_count > SIZE_MAX / lane_words)
        die("tail-nullspace allocation overflow");
    u64 *clean_coefficients =
        xcalloc(clean_count * lane_words, sizeof(*clean_coefficients));
    size_t clean_index = 0;
    for (size_t free_position = 0; free_position < lane_count;
         free_position++) {
        if (has_pivot[free_position])
            continue;
        u64 *coefficient =
            clean_coefficients + clean_index * lane_words;
        coefficient[free_position / 64] |=
            UINT64_C(1) << (free_position & 63U);
        for (size_t pivot = 0; pivot < lane_count; pivot++) {
            if (!has_pivot[pivot])
                continue;
            const u64 *pivot_vector = basis + pivot * lane_words;
            if (bw_parity_dot(pivot_vector, coefficient, lane_words))
                coefficient[pivot / 64] ^=
                    UINT64_C(1) << (pivot & 63U);
        }
        clean_index++;
    }
    if (clean_index != clean_count)
        die("internal tail-nullspace dimension mismatch");

    size_t clean_words = (clean_count + 63) / 64;
    if (column_count > SIZE_MAX / clean_words)
        die("clean projected solution allocation overflow");
    u64 *clean_solutions =
        xcalloc((size_t)column_count * clean_words,
                sizeof(*clean_solutions));
    for (uint64_t coordinate = 0; coordinate < column_count; coordinate++) {
        for (size_t file = 0; file < solution_count; file++)
            value[file] = solutions[file][coordinate];
        u64 *clean_value =
            clean_solutions + (size_t)coordinate * clean_words;
        for (size_t clean = 0; clean < clean_count; clean++) {
            const u64 *coefficient =
                clean_coefficients + clean * lane_words;
            if (bw_parity_dot(value, coefficient, lane_words))
                clean_value[clean / 64] |=
                    UINT64_C(1) << (clean & 63U);
        }
    }

    unsigned char *clean_has_pivot =
        xcalloc(clean_count, sizeof(*clean_has_pivot));
    size_t cleaned_rank = bw_rank_rows(
        clean_solutions, (size_t)column_count, clean_count, clean_words,
        clean_has_pivot);
    if (cleaned_rank > (size_t)INT_MAX)
        die("cleaned kernel dimension does not fit int");
    int kernel_dimension = (int)cleaned_rank;
    int kernel_words = (kernel_dimension + 63) / 64;
    if (kernel_dimension == 0)
        die("Block Wiedemann output contains no core-kernel vector");
    if (column_count > SIZE_MAX / (size_t)kernel_words)
        die("kernel-coordinate allocation overflow");
    u64 *kernel_masks =
        xcalloc((size_t)column_count * (size_t)kernel_words,
                sizeof(*kernel_masks));
    size_t *selected_lanes =
        xmalloc((size_t)kernel_dimension * sizeof(*selected_lanes));
    int selected = 0;
    for (size_t lane = 0; lane < clean_count; lane++)
        if (clean_has_pivot[lane]) {
            if (selected >= kernel_dimension)
                die("too many selected independent cleaned lanes");
            selected_lanes[selected++] = lane;
        }
    if (selected != kernel_dimension)
        die("independent cleaned-lane count mismatch");
    for (uint64_t coordinate = 0; coordinate < column_count; coordinate++) {
        const u64 *clean_value =
            clean_solutions + (size_t)coordinate * clean_words;
        u64 *kernel_value =
            kernel_masks + (size_t)coordinate * (size_t)kernel_words;
        for (int vector = 0; vector < kernel_dimension; vector++) {
            size_t lane = selected_lanes[vector];
            if ((clean_value[lane / 64] >> (lane & 63U)) & UINT64_C(1))
                kernel_value[vector / 64] |=
                    UINT64_C(1) << (vector & 63);
        }
    }

    /* Verify every selected vector against every literal CORE0 row. */
    FILE *matrix = fopen(matrix_name, "rb");
    if (!matrix) {
        fprintf(stderr, "cannot open %s: %s\n", matrix_name,
                strerror(errno));
        exit(EXIT_FAILURE);
    }
    u64 *accumulator = xmalloc((size_t)kernel_words * sizeof(*accumulator));
    uint64_t bad_rows = 0;
    uint64_t bad_lane_products = 0;
    uint64_t nonzero_count = 0;
    for (uint64_t row = 0; row < row_count; row++) {
        uint32_t weight = bw_read_u32_le(matrix);
        nonzero_count += weight;
        memset(accumulator, 0, (size_t)kernel_words * sizeof(*accumulator));
        for (uint32_t entry = 0; entry < weight; entry++) {
            uint32_t column = bw_read_u32_le(matrix);
            if ((uint64_t)column >= column_count)
                die("CORE0 contains an out-of-range column");
            const u64 *mask =
                kernel_masks + (size_t)column * (size_t)kernel_words;
            for (int word = 0; word < kernel_words; word++)
                accumulator[word] ^= mask[word];
        }
        int bad = 0;
        for (int word = 0; word < kernel_words; word++) {
            bad |= accumulator[word] != 0;
            bad_lane_products +=
                (uint64_t)__builtin_popcountll(accumulator[word]);
        }
        bad_rows += (uint64_t)bad;
    }
    if (fgetc(matrix) != EOF || ferror(matrix) || fclose(matrix) != 0)
        die("error finishing CORE0 matrix");
    if (bad_rows != 0 || bad_lane_products != 0)
        die("cleaned Block Wiedemann vectors fail CORE0 row checks");

    printf("BW core_rows=%" PRIu64 " core_columns=%" PRIu64
           " core_nonzeros=%" PRIu64
           " solution_coordinates=%" PRIu64
           " candidate_lanes=%zu full_solution_rank=%zu"
           " projected_rank=%zu tail_nonzero_coordinates=%" PRIu64
           " tail_hamming_weight=%" PRIu64 " tail_rank=%zu"
           " cleaned_candidate_lanes=%zu cleaned_kernel_rank=%zu"
           " cleaned_bad_rows=%" PRIu64
           " cleaned_bad_lane_products=%" PRIu64 "\n",
           row_count, column_count, nonzero_count, coordinate_count,
           lane_count, full_solution_rank, projected_rank,
           tail_nonzero_coordinates, tail_hamming_weight, tail_rank,
           clean_count, cleaned_rank, bad_rows, bad_lane_products);

    free(accumulator);
    free(selected_lanes);
    free(clean_has_pivot);
    free(clean_solutions);
    free(clean_coefficients);
    free(value);
    free(has_pivot);
    free(basis);
    for (size_t file = 0; file < solution_count; file++)
        free(solutions[file]);
    free(solutions);
    free(column_weight_name);
    free(row_weight_name);

    BwKernel result;
    result.d = expected_d;
    result.kernel_dimension = kernel_dimension;
    result.kernel_words = kernel_words;
    result.coordinate_masks = kernel_masks;
    result.candidate_lanes = lane_count;
    result.full_solution_rank = full_solution_rank;
    result.projected_rank = projected_rank;
    result.tail_rank = tail_rank;
    result.cleaned_candidate_lanes = clean_count;
    result.matrix_rows = (i64)row_count;
    result.matrix_nonzeros = (i64)nonzero_count;
    return result;
}

static inline const u64 *bw_kernel_coordinate(const BwKernel *kernel,
                                              int coordinate,
                                              int reflected) {
    int source = reflected ? kernel->d - 1 - coordinate : coordinate;
    return kernel->coordinate_masks +
           (size_t)source * (size_t)kernel->kernel_words;
}

/* Construct the exact RREF Snapshot of K^perp from a full-rank coordinate
 * mask matrix for K.  Pivot coordinates P are selected so K_P is invertible,
 * then K is changed to the systematic basis K K_P^{-1}.  Every non-P
 * coordinate c supplies the RREF row e_c + sum_f K'_(c,f)e_(P_f). */
static Snapshot bw_snapshot_from_kernel(const BwKernel *kernel,
                                        int reflected) {
    int d = kernel->d;
    int k = kernel->kernel_dimension;
    int words = kernel->kernel_words;
    if (k <= 0 || words <= 0)
        die("cannot construct snapshot from an empty kernel");

    u64 *selection_basis =
        xcalloc((size_t)k * (size_t)words, sizeof(*selection_basis));
    unsigned char *selection_has = xcalloc((size_t)k, sizeof(*selection_has));
    u64 *work = xmalloc((size_t)words * sizeof(*work));
    int *free_columns = xmalloc((size_t)k * sizeof(*free_columns));
    int selected = 0;
    for (int coordinate = 0; coordinate < d && selected < k; coordinate++) {
        memcpy(work, bw_kernel_coordinate(kernel, coordinate, reflected),
               (size_t)words * sizeof(*work));
        if (bw_insert_row(selection_basis, selection_has, work,
                          (size_t)words))
            free_columns[selected++] = coordinate;
    }
    if (selected != k)
        die("cleaned coordinate masks have smaller rank than reported");

    u64 *left = xmalloc((size_t)k * (size_t)words * sizeof(*left));
    u64 *inverse = xcalloc((size_t)k * (size_t)words, sizeof(*inverse));
    for (int row = 0; row < k; row++) {
        memcpy(left + (size_t)row * (size_t)words,
               bw_kernel_coordinate(kernel, free_columns[row], reflected),
               (size_t)words * sizeof(*left));
        inverse[(size_t)row * (size_t)words + (size_t)(row / 64)] |=
            UINT64_C(1) << (row & 63);
    }

    for (int column = 0; column < k; column++) {
        int pivot_row = column;
        while (pivot_row < k &&
               ((left[(size_t)pivot_row * (size_t)words +
                      (size_t)(column / 64)] >>
                 (column & 63)) &
                UINT64_C(1)) == 0)
            pivot_row++;
        if (pivot_row == k)
            die("selected kernel-coordinate minor is singular");
        if (pivot_row != column) {
            for (int word = 0; word < words; word++) {
                u64 temporary =
                    left[(size_t)column * (size_t)words + (size_t)word];
                left[(size_t)column * (size_t)words + (size_t)word] =
                    left[(size_t)pivot_row * (size_t)words + (size_t)word];
                left[(size_t)pivot_row * (size_t)words + (size_t)word] =
                    temporary;
                temporary =
                    inverse[(size_t)column * (size_t)words + (size_t)word];
                inverse[(size_t)column * (size_t)words + (size_t)word] =
                    inverse[(size_t)pivot_row * (size_t)words +
                            (size_t)word];
                inverse[(size_t)pivot_row * (size_t)words + (size_t)word] =
                    temporary;
            }
        }
        for (int row = 0; row < k; row++) {
            if (row == column)
                continue;
            if (((left[(size_t)row * (size_t)words +
                       (size_t)(column / 64)] >>
                  (column & 63)) &
                 UINT64_C(1)) == 0)
                continue;
            xor_words(left + (size_t)row * (size_t)words,
                      left + (size_t)column * (size_t)words, words);
            xor_words(inverse + (size_t)row * (size_t)words,
                      inverse + (size_t)column * (size_t)words, words);
        }
    }
    for (int row = 0; row < k; row++)
        for (int column = 0; column < k; column++) {
            int bit = (int)((left[(size_t)row * (size_t)words +
                                  (size_t)(column / 64)] >>
                             (column & 63)) &
                            UINT64_C(1));
            if (bit != (row == column))
                die("kernel-coordinate inverse verification failed");
        }

    Snapshot result;
    result.d = d;
    result.rank = d - k;
    result.nullity = k;
    result.words = words;
    result.arena =
        xcalloc((size_t)result.rank * (size_t)words, sizeof(*result.arena));
    result.nonpivot_cols = xmalloc((size_t)k * sizeof(*result.nonpivot_cols));
    result.npidx_for_col = xmalloc((size_t)d * sizeof(*result.npidx_for_col));
    result.basis_pivots =
        xmalloc((size_t)result.rank * sizeof(*result.basis_pivots));
    result.pivot_to_row =
        xmalloc((size_t)d * sizeof(*result.pivot_to_row));
    for (int coordinate = 0; coordinate < d; coordinate++) {
        result.npidx_for_col[coordinate] = -1;
        result.pivot_to_row[coordinate] = -1;
    }
    for (int free_index = 0; free_index < k; free_index++) {
        int coordinate = free_columns[free_index];
        result.nonpivot_cols[free_index] = coordinate;
        result.npidx_for_col[coordinate] = free_index;
    }

    int row_index = 0;
    u64 *systematic = xmalloc((size_t)words * sizeof(*systematic));
    for (int coordinate = 0; coordinate < d; coordinate++) {
        memset(systematic, 0, (size_t)words * sizeof(*systematic));
        const u64 *value =
            bw_kernel_coordinate(kernel, coordinate, reflected);
        for (int word = 0; word < words; word++) {
            u64 remaining = value[word];
            while (remaining != 0) {
                int bit = __builtin_ctzll(remaining);
                int index = 64 * word + bit;
                if (index < k)
                    xor_words(systematic,
                              inverse + (size_t)index * (size_t)words,
                              words);
                remaining &= remaining - 1;
            }
        }
        int free_index = result.npidx_for_col[coordinate];
        if (free_index >= 0) {
            for (int index = 0; index < k; index++) {
                int bit = (int)((systematic[index / 64] >> (index & 63)) &
                                UINT64_C(1));
                if (bit != (index == free_index))
                    die("systematic kernel-coordinate check failed");
            }
            continue;
        }
        if (row_index >= result.rank)
            die("too many snapshot pivot rows");
        memcpy(result.arena + (size_t)row_index * (size_t)words,
               systematic, (size_t)words * sizeof(*systematic));
        result.basis_pivots[row_index] = coordinate;
        result.pivot_to_row[coordinate] = row_index;
        row_index++;
    }
    if (row_index != result.rank)
        die("snapshot pivot-row count mismatch");

    free(systematic);
    free(inverse);
    free(left);
    free(free_columns);
    free(work);
    free(selection_has);
    free(selection_basis);
    return result;
}

static i64 bw_common_core_row_count(int n_level, int multiplier,
                                    int residue_parity,
                                    const DivisorData *data,
                                    int divisor_count) {
    i64 rows = 0;
    for (int index = 0; index < divisor_count; index++) {
        int step = multiplier / data[index].q;
        int parity = selected_v_parity(residue_parity, step);
        i64 lower;
        i64 upper;
        core_interval(n_level, residue_parity, data[index].h,
                      &lower, &upper);
        rows += count_selected(lower, upper, parity);
    }
    return rows;
}

/* Reflect the parity-zero core and append the exact rows by which the
 * parity-one common interval is larger. */
static Snapshot bw_make_parity_one_snapshot(const BwKernel *kernel,
                                            int n_level, int multiplier,
                                            const DivisorData *data,
                                            int divisor_count,
                                            int *exception_rows_out,
                                            int *exception_rank_out,
                                            i64 *exception_nnz_out) {
    Snapshot reflected = bw_snapshot_from_kernel(kernel, 1);
    int exceptions = 0;
    i64 exception_nnz = 0;
    for (int index = 0; index < divisor_count; index++)
        if (data[index].h % n_level == 0) {
            exceptions++;
            exception_nnz += data[index].count;
        }

    Crref parity_one = crref_from_snapshot(&reflected, exceptions);
    int gains = 0;
    for (int index = 0; index < divisor_count; index++) {
        if (data[index].h % n_level != 0)
            continue;
        int step = multiplier / data[index].q;
        int parity = selected_v_parity(1, step);
        i64 a = data[index].h / n_level;
        i64 left = -a;
        i64 right = a - 1;
        i64 v = (positive_mod_i64(left, 2) == parity) ? left : right;
        if (positive_mod_i64(v, 2) != parity)
            die("internal parity-one exceptional endpoint error");
        build_row(&parity_one, multiplier, 1, &data[index], v);
        gains += crref_insert_current_work(&parity_one);
        printf("REFLECTION_EXCEPTION q=%d H=%d v=%lld weight=%d gain=%d\n",
               data[index].q, data[index].h, (long long)v,
               data[index].count, parity_one.rank - reflected.rank);
    }
    crref_compact(&parity_one);
    Snapshot result = snapshot_from_crref(&parity_one);
    crref_destroy(&parity_one);
    snapshot_destroy(&reflected);
    *exception_rows_out = exceptions;
    *exception_rank_out = gains;
    *exception_nnz_out = exception_nnz;
    return result;
}

#ifndef SPATIAL_CRT_KERNEL_F2_BW_FINISH_LIBRARY
int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr,
                "Usage: %s N Q CORE0.bin W1 [W2 ...]\n", argv[0]);
        return EXIT_FAILURE;
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

    i64 equation_margin = expected_full_rows + multiplier - (i64)q_total;
    printf("N=%d M=%d Q=%d global_parity_columns=%d divisors=%d "
           "full_coprime_rows=%lld equation_margin_after_W=%lld\n",
           n_level, multiplier, q_total, d, divisor_count,
           (long long)expected_full_rows, (long long)equation_margin);
    if (equation_margin < 0)
        die("dimension obstruction: coprime rows plus W cannot span");

    size_t solution_count = (size_t)argc - 4;
    BwKernel kernel = bw_load_clean_kernel(
        argv[3], argv + 4, solution_count, d);
    printf("BW_COMPLETENESS supplied cleaned kernel is assumed complete; "
           "row annihilation is checked exactly, while a new case still "
           "requires a rank certificate or independent randomized runs\n");
    i64 common_rows[2];
    common_rows[0] = bw_common_core_row_count(
        n_level, multiplier, 0, data, divisor_count);
    common_rows[1] = bw_common_core_row_count(
        n_level, multiplier, 1, data, divisor_count);
    if (kernel.matrix_rows != common_rows[0])
        die("CORE0 row count does not match the exact parity-zero core");

    Snapshot snapshots[2];
    memset(snapshots, 0, sizeof(snapshots));
    snapshots[0] = bw_snapshot_from_kernel(&kernel, 0);
    int reflection_exceptions = 0;
    int reflection_gain = 0;
    i64 reflection_exception_nnz = 0;
    snapshots[1] = bw_make_parity_one_snapshot(
        &kernel, n_level, multiplier, data, divisor_count,
        &reflection_exceptions, &reflection_gain,
        &reflection_exception_nnz);
    if (common_rows[1] - common_rows[0] != reflection_exceptions)
        die("reflection exception count does not match core row difference");
    printf("CORE_FROM_BW residue_parity=0 rows=%lld rank=%d/%d nullity=%d\n",
           (long long)common_rows[0], snapshots[0].rank, d,
           snapshots[0].nullity);
    printf("CORE_FROM_REFLECTION residue_parity=1 rows=%lld "
           "reflected_rows=%lld exception_rows=%d exception_nnz=%lld "
           "exception_rank_gain=%d rank=%d/%d nullity=%d\n",
           (long long)common_rows[1], (long long)common_rows[0],
           reflection_exceptions, (long long)reflection_exception_nnz,
           reflection_gain, snapshots[1].rank, d, snapshots[1].nullity);
    free(kernel.coordinate_masks);

    int inverse_n = inverse_mod(n_level % multiplier, multiplier);
    if ((inverse_n & 1) == 0)
        die("internal error: inverse of odd N modulo even M is not odd");

    i64 output_capacity_i64 =
        (i64)((n_level + 1) / 2) * snapshots[0].nullity +
        (i64)((n_level - 1) / 2) * snapshots[1].nullity;
    if (output_capacity_i64 > d)
        output_capacity_i64 = d;
    int output_capacity = (int)output_capacity_i64;
    int output_words = (d + 63) / 64;
    uint64_t output_bytes =
        (uint64_t)output_capacity * (uint64_t)output_words * sizeof(u64) +
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
    uint64_t output_work_bytes = (uint64_t)output_words * sizeof(u64);
    guard_additional_allocation(output_bytes + maximum_sector_bytes +
                                    output_work_bytes,
                                0, "output plus restored-sector storage");
    DenseOutput output = dense_output_create(d, output_capacity);
    u64 *output_work = xcalloc((size_t)output_words, sizeof(*output_work));
    printf("OUTPUT capacity=%d/%d allocation=%llu_bytes=%.3f_GiB "
           "max_restored_sector=%.3f_GiB\n",
           output_capacity, d, (unsigned long long)output_bytes,
           (double)output_bytes / (double)(UINT64_C(1) << 30),
           (double)maximum_sector_bytes /
               (double)(UINT64_C(1) << 30));

    i64 total_even_rows = 0;
    i64 total_even_kernel = 0;
    size_t peak_sector_bytes = 0;
    for (int residue_parity = 0; residue_parity <= 1;
         residue_parity++) {
        const Snapshot *snapshot = &snapshots[residue_parity];
        for (int residue = residue_parity; residue < n_level; residue += 2) {
            int exceptions = count_sector_exceptions(
                n_level, multiplier, residue, data, divisor_count);
            Crref sector = crref_from_snapshot(snapshot, exceptions);
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

            i64 sector_rows = 0;
            for (int index = 0; index < divisor_count; index++) {
                int step = multiplier / data[index].q;
                int parity = selected_v_parity(residue_parity, step);
                i64 lower;
                i64 upper;
                legal_interval(n_level, residue, data[index].h,
                               &lower, &upper);
                sector_rows += count_selected(lower, upper, parity);
            }
            total_even_rows += sector_rows;
            total_even_kernel += kernel_dimension;
            if (sector.peak_used_bytes > peak_sector_bytes)
                peak_sector_bytes = sector.peak_used_bytes;
            printf("sector r=%d even_rows=%lld endpoints=%d rank=%d/%d "
                   "kernel_dim=%d output_shift=%d W_gain=%d W_rank=%d/%d\n",
                   residue, (long long)sector_rows, exceptions,
                   sector.rank, d, kernel_dimension, shift, output_gain,
                   output.rank, d);
            fflush(stdout);
            crref_destroy(&sector);
        }
        snapshot_destroy(&snapshots[residue_parity]);
    }

    if (2 * total_even_rows != expected_full_rows)
        die("internal parity row-count mismatch");
    i64 full_kernel_dimension = 2 * total_even_kernel;
    i64 full_coprime_rank = (i64)q_total - full_kernel_dimension;
    i64 full_w_gain = 2 * (i64)output.rank;
    i64 full_defect = full_kernel_dimension - full_w_gain;
    i64 assisted_rank = (i64)q_total - full_defect;
    printf("TOTAL even_coprime_rows=%lld full_coprime_rank=%lld/%d "
           "full_coprime_kernel_dim=%lld W_gain=%lld/%lld "
           "final_defect=%lld assisted_rank=%lld/%d "
           "peak_sector=%zu output_allocation=%llu\n",
           (long long)total_even_rows, (long long)full_coprime_rank,
           q_total, (long long)full_kernel_dimension,
           (long long)full_w_gain, (long long)full_kernel_dimension,
           (long long)full_defect, (long long)assisted_rank, q_total,
           peak_sector_bytes, (unsigned long long)output_bytes);

    free(output_work);
    dense_output_destroy(&output);
    for (int index = 0; index < divisor_count; index++)
        free(data[index].values);
    free(data);
    free(divisors);
    return EXIT_SUCCESS;
}
#endif
