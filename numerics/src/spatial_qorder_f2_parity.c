/* Direct parity-sector row reduction for the genuine buffered spatial system.
 *
 * For even Q, each row R_(q,u) is supported on one parity of j.  Reflection
 * sigma(j)=Q-1-j sends u to -u-1 and exchanges the two parity sectors.  The
 * exact half-open window
 *
 *     1-C_q <= u <= C_q-2,
 *     C_q = ceil(Q/sqrt(lcm(N,q^2))),
 *
 * is a disjoint union of reflected pairs {u0,-u0-1}, 0<=u0<=C_q-2.
 * This program chooses the even-supported member and maps j=2k to k.
 * The q=1,2 singleton pivots are removed exactly before bit-packed Gaussian
 * elimination.  Hence the reported full defect is twice the sector defect.
 *
 * Every divisibility-minimal s|Q with 2*C_s-2>=Q/s is retained, while all
 * blocks properly divisible by such an s are omitted.  These exact
 * complete-row reductions combine triangularly in the divisor order.
 * A full-rank result over F_2 certifies full rank over Q; a deficit can be
 * characteristic-specific and should be checked by an odd-prime version.
 *
 * This source is intentionally separate from spatial_qorder_f2_even*.c.
 * Those programs fold sigma-orbits and are computationally isomorphic for
 * even Q, but describe the calculation as an invariant-subspace trick.
 *
 * Compile: gcc -O3 -march=native -o spatial_qorder_f2_parity \
 *              spatial_qorder_f2_parity.c -lm
 * Usage:   ./spatial_qorder_f2_parity N Q
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <limits.h>

#include "spatial_row_pruning.h"

#if defined(__AVX512F__) || defined(__AVX2__)
#include <immintrin.h>
#endif

typedef uint64_t u64;
typedef int64_t i64;

static int QQ;
static int halfQ;
static int dim_residual;
static int removed_singletons;
static int row_words;
static int *col_map;
static u64 *basis_rows;
static int *pivot_to_row;
static int g_rank;

static i64 igcd(i64 a, i64 b) {
    while (b) { i64 t = a % b; a = b; b = t; }
    return a < 0 ? -a : a;
}

static i64 ilcm(i64 a, i64 b) {
    i64 g = igcd(a, b);
    __int128 value = (__int128)(a / g) * b;
    if (value > INT64_MAX) {
        fprintf(stderr, "lcm overflow for %lld and %lld\n",
                (long long)a, (long long)b);
        exit(1);
    }
    return (i64)value;
}

static int window_C(int n_level, int q) {
    i64 ell = ilcm((i64)n_level, (i64)q * q);
    i64 q2 = (i64)QQ * QQ;
    if (ell <= 0) return 0;
    i64 c = (i64)ceill((long double)QQ / sqrtl((long double)ell));
    if (c < 1) c = 1;
    while (c > 1 && (__int128)(c - 1) * (c - 1) * ell >= q2) c--;
    while ((__int128)c * c * ell < q2) c++;
    return (int)c;
}

static int pruning_window_C(void *context, int q) {
    return window_C(*(const int *)context, q);
}

static int row_parity(int q, int u) {
    int parity = u % 2;
    if (parity < 0) parity += 2;
    if ((QQ / q) & 1) parity ^= 1;
    return parity;
}

static int even_member_u(int q, int u0) {
    return row_parity(q, u0) == 0 ? u0 : -u0 - 1;
}

static void build_residual_column_map(
    int n_level, const SpatialRowPruning *pruning) {
    unsigned char *removed =
        (unsigned char *)calloc((size_t)halfQ, sizeof(unsigned char));
    if (!removed) { fprintf(stderr, "OOM singleton map\n"); exit(1); }

    for (int q = 1; q <= 2; q++) {
        if (QQ % q != 0) continue;
        if (!spatial_row_pruning_is_selected(pruning, q))
            continue;
        int c = window_C(n_level, q);
        for (int u0 = 0; u0 <= c - 2; u0++) {
            int u = even_member_u(q, u0);
            i64 j = ((i64)(QQ / q) + u) % QQ;
            if (j < 0) j += QQ;
            if (j & 1) {
                fprintf(stderr, "internal singleton parity error q=%d u=%d\n",
                        q, u);
                exit(1);
            }
            removed[j / 2] = 1;
        }
    }

    col_map = (int *)malloc((size_t)halfQ * sizeof(int));
    if (!col_map) { fprintf(stderr, "OOM column map\n"); exit(1); }
    dim_residual = 0;
    removed_singletons = 0;
    for (int k = 0; k < halfQ; k++) {
        if (removed[k]) {
            col_map[k] = -1;
            removed_singletons++;
        } else {
            col_map[k] = dim_residual++;
        }
    }
    free(removed);
}

static inline void set_bit(u64 *row, int bit) {
    row[bit >> 6] |= (u64)1 << (bit & 63);
}

static void make_even_row(int q, int u, u64 *row) {
    memset(row, 0, (size_t)row_words * sizeof(u64));
    if (row_parity(q, u) != 0) {
        fprintf(stderr, "internal row-sector error q=%d u=%d\n", q, u);
        exit(1);
    }
    int step = QQ / q;
    for (int a = 1; a <= q; a++) {
        if (igcd(a, q) != 1) continue;
        i64 j = ((i64)a * step + u) % QQ;
        if (j < 0) j += QQ;
        if (j & 1) {
            fprintf(stderr, "mixed row parity q=%d u=%d a=%d\n", q, u, a);
            exit(1);
        }
        int col = col_map[j / 2];
        if (col >= 0) set_bit(row, col);
    }
}

static inline int first_bit(const u64 *row) {
    for (int w = 0; w < row_words; w++)
        if (row[w]) return 64 * w + __builtin_ctzll(row[w]);
    return -1;
}

static inline void xor_row(u64 *dst, const u64 *src, int pivot) {
    int w = pivot >> 6;
#if defined(__AVX512F__)
    for (; w + 8 <= row_words; w += 8) {
        __m512i a = _mm512_loadu_si512((const void *)(dst + w));
        __m512i b = _mm512_loadu_si512((const void *)(src + w));
        _mm512_storeu_si512((void *)(dst + w), _mm512_xor_si512(a, b));
    }
#elif defined(__AVX2__)
    for (; w + 4 <= row_words; w += 4) {
        __m256i a = _mm256_loadu_si256((const __m256i *)(dst + w));
        __m256i b = _mm256_loadu_si256((const __m256i *)(src + w));
        _mm256_storeu_si256((__m256i *)(dst + w), _mm256_xor_si256(a, b));
    }
#endif
    for (; w < row_words; w++) dst[w] ^= src[w];
}

static int try_add_row(u64 *row) {
    for (;;) {
        int pivot = first_bit(row);
        if (pivot < 0 || pivot >= dim_residual) return 0;
        int prior = pivot_to_row[pivot];
        if (prior < 0) {
            pivot_to_row[pivot] = g_rank++;
            return 1;
        }
        xor_row(row, basis_rows + (size_t)prior * row_words, pivot);
    }
}

int main(int argc, char **argv) {
    if (argc < 3) {
        fprintf(stderr, "Usage: %s N Q\n", argv[0]);
        return 1;
    }
    int n_level = atoi(argv[1]);
    QQ = atoi(argv[2]);
    if (n_level <= 0 || QQ <= 0 || (QQ & 1)) {
        fprintf(stderr, "require N>0 and positive even Q\n");
        return 1;
    }
    halfQ = QQ / 2;
    SpatialRowPruning pruning;
    spatial_row_pruning_init(&pruning, QQ, pruning_window_C, &n_level);
    build_residual_column_map(n_level, &pruning);
    row_words = (dim_residual + 63) / 64;

    clock_t setup_start = clock();
    size_t basis_words = (size_t)dim_residual * (size_t)row_words;
    basis_rows = (u64 *)calloc(basis_words ? basis_words : 1, sizeof(u64));
    pivot_to_row = (int *)malloc((size_t)(dim_residual ? dim_residual : 1)
                                 * sizeof(int));
    if (!basis_rows || !pivot_to_row) {
        fprintf(stderr, "OOM residual_dim=%d basis_bytes=%zu\n",
                dim_residual, basis_words * sizeof(u64));
        return 1;
    }
    for (int c = 0; c < dim_residual; c++) pivot_to_row[c] = -1;
    g_rank = 0;
    double setup_seconds = (double)(clock() - setup_start) / CLOCKS_PER_SEC;

    /* The selected blocks span the literal family by divisor-triangular
     * complete-row elimination. */
    int rows_tried = 0;
    clock_t run_start = clock();
    for (int q = 3; q <= QQ && g_rank < dim_residual; q++) {
        if (QQ % q != 0) continue;
        if (!spatial_row_pruning_is_selected(&pruning, q))
            continue;
        int c = window_C(n_level, q);
        int pair_count = spatial_row_pruning_pair_count(&pruning, q, c);
        for (int u0 = 0; u0 < pair_count && g_rank < dim_residual; u0++) {
            int u = even_member_u(q, u0);
            u64 *row = basis_rows + (size_t)g_rank * row_words;
            make_even_row(q, u, row);
            try_add_row(row);
            rows_tried++;
        }
    }
    double run_seconds = (double)(clock() - run_start) / CLOCKS_PER_SEC;

    int sector_rank = removed_singletons + g_rank;
    int sector_defect = halfQ - sector_rank;
    printf("N=%d Q=%d p=2 parity=even residual_rank=%d/%d "
           "sector_rank=%d/%d full_defect=%d rows_tried=%d "
           "setup=%.2fs run=%.2fs basis_bytes=%zu\n",
           n_level, QQ, g_rank, dim_residual, sector_rank, halfQ,
           2 * sector_defect, rows_tried, setup_seconds, run_seconds,
           basis_words * sizeof(u64));
    spatial_row_pruning_print(stdout, &pruning);
    putchar('\n');

    spatial_row_pruning_destroy(&pruning);
    free(col_map);
    free(basis_rows);
    free(pivot_to_row);
    return 0;
}
