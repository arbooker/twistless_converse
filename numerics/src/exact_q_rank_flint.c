/* Exact characteristic-zero rank of the literal scrR_N(Q) row matrix.
 *
 * This is the dense FLINT fallback for Hall-admissible candidates on which
 * SymPy's sparse exact-domain elimination is slow.  It uses the same exact
 * half-open windows as paper0.tex, removes all q=1,2 singleton pivots, and
 * for even Q ranks only the even-supported parity sector.  Reflection gives
 * an isomorphic odd sector.  It combines every divisor-triangular deletion
 * arising from an s|Q with 2*H_s-2>=Q/s.
 *
 * Compile:
 *   cc -O3 -Wall -Wextra -Werror $(pkg-config --cflags flint) \
 *      -o exact_q_rank_flint exact_q_rank_flint.c \
 *      $(pkg-config --libs flint) -lm
 * Library build for the Hall minimality scanner:
 *   cc -O3 -DEXACT_Q_RANK_FLINT_NO_MAIN $(pkg-config --cflags flint) \
 *      -c exact_q_rank_flint.c -o exact_q_rank_flint_core.o
 * Usage:
 *   ./exact_q_rank_flint N Q [--estimate]
 */

#include <errno.h>
#include <inttypes.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_mat.h>

#include "exact_q_rank_flint.h"
#include "spatial_row_pruning.h"

typedef int64_t i64;
typedef __int128 i128;

static void die(const char *message) {
    fprintf(stderr, "%s\n", message);
    exit(EXIT_FAILURE);
}

#ifndef EXACT_Q_RANK_FLINT_NO_MAIN
static int parse_positive_int(const char *text, const char *name) {
    char *end = NULL;
    errno = 0;
    long value = strtol(text, &end, 10);
    if (errno != 0 || end == text || *end != '\0' || value <= 0 ||
        value > INT_MAX) {
        fprintf(stderr, "%s must be an integer in [1,INT_MAX]\n", name);
        exit(EXIT_FAILURE);
    }
    return (int)value;
}
#endif

static i64 gcd_i64(i64 a, i64 b) {
    while (b != 0) {
        i64 next = a % b;
        a = b;
        b = next;
    }
    return a < 0 ? -a : a;
}

static i64 lcm_i64(i64 a, i64 b) {
    i64 divisor = gcd_i64(a, b);
    i128 result = (i128)(a / divisor) * b;
    if (result <= 0 || result > INT64_MAX)
        die("lcm overflow");
    return (i64)result;
}

/* Smallest C with C^2*lcm(N,q^2)>=Q^2. */
static int window_radius(int n_level, int q_total, int q) {
    i128 q_squared = (i128)q * q;
    if (q_squared > INT64_MAX)
        die("q^2 overflow");
    i64 ell = lcm_i64(n_level, (i64)q_squared);
    i128 target = (i128)q_total * q_total;
    int low = 0;
    int high = q_total;
    while (low < high) {
        int middle = low + (high - low) / 2;
        if ((i128)middle * middle * ell >= target)
            high = middle;
        else
            low = middle + 1;
    }
    return low;
}

static int row_parity(int q_total, int q, int shift) {
    int step = q_total / q;
    int parity = shift % 2;
    if (parity < 0)
        parity += 2;
    if (step & 1)
        parity ^= 1; /* q is even and every primitive residue is odd. */
    return parity;
}

static int support_column(int q_total, int q, int shift, int a) {
    i64 value = ((i64)a * (q_total / q) + shift) % q_total;
    if (value < 0)
        value += q_total;
    return (int)value;
}

static int is_divisor(int q_total, int q) {
    return q_total % q == 0;
}

typedef struct {
    int n_level;
    int q_total;
} ExactPruningContext;

static int exact_pruning_window(void *context, int q) {
    const ExactPruningContext *parameters = context;
    return window_radius(parameters->n_level, parameters->q_total, q);
}

static int is_selected_divisor(
    const SpatialRowPruning *pruning, int q_total, int q) {
    return is_divisor(q_total, q) &&
           spatial_row_pruning_is_selected(pruning, q);
}

static void mark_singletons(int n_level, int q_total,
                            const SpatialRowPruning *pruning,
                            int parity_reduced,
                            unsigned char *removed, int coordinate_count) {
    for (int q = 1; q <= 2; q++) {
        if (!is_selected_divisor(pruning, q_total, q))
            continue;
        int radius = window_radius(n_level, q_total, q);
        for (int shift = -radius + 1; shift <= radius - 2; shift++) {
            if (!spatial_row_pruning_shift_selected(pruning, q, shift))
                continue;
            if (parity_reduced && row_parity(q_total, q, shift) != 0)
                continue;
            int column = support_column(q_total, q, shift, 1);
            if (parity_reduced) {
                if (column & 1)
                    die("internal singleton parity error");
                column /= 2;
            }
            if (column < 0 || column >= coordinate_count)
                die("internal singleton column error");
            removed[column] = 1;
        }
    }
}

static i64 count_residual_rows(int n_level, int q_total,
                               const SpatialRowPruning *pruning,
                               int parity_reduced) {
    i64 rows = 0;
    for (int q = 3; q <= q_total; q++) {
        if (!is_selected_divisor(pruning, q_total, q))
            continue;
        int radius = window_radius(n_level, q_total, q);
        for (int shift = -radius + 1; shift <= radius - 2; shift++) {
            if (!spatial_row_pruning_shift_selected(pruning, q, shift))
                continue;
            if (!parity_reduced || row_parity(q_total, q, shift) == 0)
                rows++;
        }
    }
    return rows;
}

int exact_q_rank_flint_compute(int n_level, int q_total, int estimate_only,
                               ExactQRankFlintResult *result, FILE *report) {
    if (n_level <= 0 || q_total <= 0 || !result)
        die("exact rank requires positive N,Q and a result object");
    int parity_reduced = (q_total % 2 == 0);
    ExactPruningContext pruning_context = {n_level, q_total};
    SpatialRowPruning pruning;
    spatial_row_pruning_init(
        &pruning, q_total, exact_pruning_window, &pruning_context);
    int coordinate_count = parity_reduced ? q_total / 2 : q_total;
    unsigned char *removed =
        calloc((size_t)coordinate_count, sizeof(*removed));
    int *column_map = malloc((size_t)coordinate_count * sizeof(*column_map));
    if (!removed || !column_map)
        die("out of memory allocating column map");
    mark_singletons(n_level, q_total, &pruning, parity_reduced, removed,
                    coordinate_count);

    int removed_count = 0;
    int residual_columns = 0;
    for (int column = 0; column < coordinate_count; column++) {
        if (removed[column]) {
            column_map[column] = -1;
            removed_count++;
        } else {
            column_map[column] = residual_columns++;
        }
    }
    i64 residual_rows =
        count_residual_rows(n_level, q_total, &pruning, parity_reduced);
    i128 entries = (i128)residual_rows * residual_columns;
    long double gib =
        (long double)entries * sizeof(fmpz) / (1024.0L * 1024.0L * 1024.0L);
    *result = (ExactQRankFlintResult){
        .parity_reduced = parity_reduced,
        .coordinate_count = coordinate_count,
        .singleton_pivots = removed_count,
        .residual_columns = residual_columns,
        .residual_rows = residual_rows,
        .residual_rank = -1,
        .sector_rank = -1,
        .full_defect = -1,
        .estimated_fmpz_storage_gib = gib,
    };
    if (report) {
        fprintf(report,
                "N=%d Q=%d parity_reduced=%d singleton_pivots=%d "
                "residual_matrix=%" PRId64
                "x%d estimated_fmpz_storage_gib=%.3Lf\n",
                n_level, q_total, parity_reduced, removed_count,
                residual_rows, residual_columns, gib);
        spatial_row_pruning_print(report, &pruning);
        fputc('\n', report);
        fflush(report);
    }
    if (estimate_only) {
        spatial_row_pruning_destroy(&pruning);
        free(column_map);
        free(removed);
        return 0;
    }
    if (residual_rows > WORD_MAX)
        die("too many rows for this FLINT build");

    fmpz_mat_t matrix;
    fmpz_mat_init(matrix, (slong)residual_rows, (slong)residual_columns);
    slong row = 0;
    for (int q = 3; q <= q_total; q++) {
        if (!is_selected_divisor(&pruning, q_total, q))
            continue;
        int radius = window_radius(n_level, q_total, q);
        for (int shift = -radius + 1; shift <= radius - 2; shift++) {
            if (!spatial_row_pruning_shift_selected(&pruning, q, shift))
                continue;
            if (parity_reduced && row_parity(q_total, q, shift) != 0)
                continue;
            for (int a = 1; a <= q; a++) {
                if (gcd_i64(a, q) != 1)
                    continue;
                int column = support_column(q_total, q, shift, a);
                if (parity_reduced) {
                    if (column & 1)
                        die("internal row parity error");
                    column /= 2;
                }
                int residual = column_map[column];
                if (residual >= 0)
                    fmpz_set_ui(fmpz_mat_entry(matrix, row, residual), 1);
            }
            row++;
        }
    }
    if (row != residual_rows)
        die("internal row-count mismatch");

    slong residual_rank = fmpz_mat_rank(matrix);
    slong sector_rank = removed_count + residual_rank;
    slong sector_defect = coordinate_count - sector_rank;
    slong full_defect = parity_reduced ? 2 * sector_defect : sector_defect;
    result->residual_rank = residual_rank;
    result->sector_rank = sector_rank;
    result->full_defect = full_defect;
    if (report)
        fprintf(report,
                "rank_QQ=%ld/%d residual_rank_QQ=%ld/%d full_defect=%ld\n",
                (long)sector_rank, coordinate_count, (long)residual_rank,
                residual_columns, (long)full_defect);

    fmpz_mat_clear(matrix);
    spatial_row_pruning_destroy(&pruning);
    free(column_map);
    free(removed);
    flint_cleanup();
    return 0;
}

#ifndef EXACT_Q_RANK_FLINT_NO_MAIN
int main(int argc, char **argv) {
    if (argc < 3 || argc > 4) {
        fprintf(stderr, "Usage: %s N Q [--estimate]\n", argv[0]);
        return EXIT_FAILURE;
    }
    int n_level = parse_positive_int(argv[1], "N");
    int q_total = parse_positive_int(argv[2], "Q");
    int estimate_only = 0;
    if (argc == 4) {
        if (strcmp(argv[3], "--estimate") != 0)
            die("third argument must be --estimate");
        estimate_only = 1;
    }
    ExactQRankFlintResult result;
    if (exact_q_rank_flint_compute(n_level, q_total, estimate_only,
                                   &result, stdout) != 0)
        return EXIT_FAILURE;
    return estimate_only || result.full_defect == 0 ? EXIT_SUCCESS : 1;
}
#endif
