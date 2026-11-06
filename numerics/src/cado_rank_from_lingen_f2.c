#define _FILE_OFFSET_BITS 64

#include <errno.h>
#include <inttypes.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

/*
 * Extract deg(det F) and ord_x(det F) from the binary polynomial generator
 * written by CADO-NFS lingen.  In CADO's no-RHS nullspace pipeline, lingen
 * discards the zeroth moment and uses X^T A^(i+1) Y.  Consequently
 * deg(det F), the finite block-Hankel/realization rank found by lingen, is a
 * one-sided lower bound for rank(A).  The weaker quantity
 * deg(det F)-ord_x(det F) remains useful as the detected nonzero-spectral
 * part.  This program prints both and states the moment-offset assumption.
 *
 * CADO writes 64-by-64 coefficient blocks to files named
 *
 *     PREFIX.sols<COL0>-<COL1>.<ROW0>-<ROW1>.
 *
 * The determinant valuation is computed exactly.  If the local Smith
 * exponents of F at x=0 are a_i, multiplication by F on
 * (F_2[x]/x^k)^n has nullity sum_i min(a_i,k).  Thus the first zero
 * difference of consecutive nullities gives sum_i a_i = ord_x(det F).
 * Applying the same calculation after reversing each column gives the
 * correction between the sum of column degrees and deg(det F).
 */

enum { SPLIT_WIDTH = 64 };

typedef struct {
    size_t n;
    size_t words;
    size_t ncoeff;
    uint64_t *coeff;
    size_t *col_degree;
} poly_matrix;

static void die(const char *message)
{
    fprintf(stderr, "error: %s\n", message);
    exit(EXIT_FAILURE);
}

static void die_errno(const char *what, const char *path)
{
    fprintf(stderr, "error: %s '%s': %s\n", what, path, strerror(errno));
    exit(EXIT_FAILURE);
}

static int checked_mul_size(size_t a, size_t b, size_t *out)
{
    if (a != 0 && b > SIZE_MAX / a)
        return 0;
    *out = a * b;
    return 1;
}

static uint64_t load_le64(const unsigned char bytes[8])
{
    uint64_t value = 0;
    unsigned int i;
    for (i = 0; i < 8; ++i)
        value |= (uint64_t)bytes[i] << (8U * i);
    return value;
}

static uint64_t *poly_row(poly_matrix *p, size_t degree, size_t row)
{
    return p->coeff + (degree * p->n + row) * p->words;
}

static const uint64_t *poly_const_row(const poly_matrix *p, size_t degree,
                                      size_t row)
{
    return p->coeff + (degree * p->n + row) * p->words;
}

static void make_block_filename(char *path, size_t path_size,
                                const char *prefix, size_t col, size_t row)
{
    int count = snprintf(path, path_size, "%s.sols%zu-%zu.%zu-%zu",
                         prefix, col, col + SPLIT_WIDTH,
                         row, row + SPLIT_WIDTH);
    if (count < 0 || (size_t)count >= path_size)
        die("lingen block filename is too long");
}

static void load_polynomial(poly_matrix *p, size_t n, const char *prefix)
{
    char path[PATH_MAX];
    struct stat st;
    size_t row, col, degree;
    size_t block_bytes = SPLIT_WIDTH * sizeof(uint64_t);
    size_t total_words, total_bytes;

    memset(p, 0, sizeof(*p));
    if (n == 0 || n % SPLIT_WIDTH != 0)
        die("block size must be a positive multiple of 64");

    make_block_filename(path, sizeof(path), prefix, 0, 0);
    if (stat(path, &st) != 0)
        die_errno("cannot stat", path);
    if (st.st_size <= 0 || (uint64_t)st.st_size % block_bytes != 0)
        die("a lingen block has an invalid byte length");

    p->n = n;
    p->words = n / 64;
    p->ncoeff = (size_t)((uint64_t)st.st_size / block_bytes);

    if (!checked_mul_size(p->ncoeff, n, &total_words) ||
        !checked_mul_size(total_words, p->words, &total_words) ||
        !checked_mul_size(total_words, sizeof(uint64_t), &total_bytes))
        die("polynomial matrix allocation size overflow");
    p->coeff = calloc(1, total_bytes);
    p->col_degree = malloc(n * sizeof(*p->col_degree));
    if (p->coeff == NULL || p->col_degree == NULL)
        die("cannot allocate polynomial matrix");
    for (col = 0; col < n; ++col)
        p->col_degree[col] = SIZE_MAX;

    for (row = 0; row < n; row += SPLIT_WIDTH) {
        for (col = 0; col < n; col += SPLIT_WIDTH) {
            FILE *file;
            unsigned char bytes[SPLIT_WIDTH * sizeof(uint64_t)];

            make_block_filename(path, sizeof(path), prefix, col, row);
            if (stat(path, &st) != 0)
                die_errno("cannot stat", path);
            if ((uint64_t)st.st_size != p->ncoeff * block_bytes)
                die("lingen coefficient blocks have unequal lengths");
            file = fopen(path, "rb");
            if (file == NULL)
                die_errno("cannot open", path);

            for (degree = 0; degree < p->ncoeff; ++degree) {
                size_t i;
                if (fread(bytes, sizeof(bytes), 1, file) != 1) {
                    fclose(file);
                    die_errno("cannot read", path);
                }
                for (i = 0; i < SPLIT_WIDTH; ++i) {
                    uint64_t value = load_le64(bytes + i * sizeof(uint64_t));
                    uint64_t *dst = poly_row(p, degree, row + i);
                    dst[col / 64] = value;
                }
            }
            if (fclose(file) != 0)
                die_errno("cannot close", path);
        }
    }

    for (degree = 0; degree < p->ncoeff; ++degree) {
        for (row = 0; row < n; ++row) {
            const uint64_t *src = poly_const_row(p, degree, row);
            size_t word;
            for (word = 0; word < p->words; ++word) {
                uint64_t bits = src[word];
                while (bits != 0) {
                    unsigned int bit = (unsigned int)__builtin_ctzll(bits);
                    col = 64 * word + bit;
                    p->col_degree[col] = degree;
                    bits &= bits - 1;
                }
            }
        }
    }
    for (col = 0; col < n; ++col) {
        if (p->col_degree[col] == SIZE_MAX)
            die("lingen generator has an identically zero column");
    }
}

static void free_polynomial(poly_matrix *p)
{
    free(p->coeff);
    free(p->col_degree);
    memset(p, 0, sizeof(*p));
}

static size_t dense_rank(uint64_t *matrix, size_t nrows, size_t ncols)
{
    size_t words = (ncols + 63) / 64;
    size_t rank = 0, col;

    for (col = 0; col < ncols && rank < nrows; ++col) {
        size_t word = col / 64;
        uint64_t mask = UINT64_C(1) << (col % 64);
        size_t pivot = rank, row, w;

        while (pivot < nrows && !(matrix[pivot * words + word] & mask))
            ++pivot;
        if (pivot == nrows)
            continue;
        if (pivot != rank) {
            for (w = 0; w < words; ++w) {
                uint64_t tmp = matrix[rank * words + w];
                matrix[rank * words + w] = matrix[pivot * words + w];
                matrix[pivot * words + w] = tmp;
            }
        }
        for (row = rank + 1; row < nrows; ++row) {
            uint64_t *dst;
            const uint64_t *src;
            if (!(matrix[row * words + word] & mask))
                continue;
            dst = matrix + row * words;
            src = matrix + rank * words;
            for (w = word; w < words; ++w)
                dst[w] ^= src[w];
        }
        ++rank;
    }
    return rank;
}

static uint64_t *build_toeplitz(const poly_matrix *p, size_t order,
                                int reverse, size_t max_bytes,
                                size_t *dimension_out, size_t *bytes_out)
{
    size_t dimension, words, row_words, bytes;
    size_t block_row, block_col, i;
    uint64_t *matrix;

    if (!checked_mul_size(p->n, order, &dimension))
        die("Toeplitz dimension overflow");
    words = (dimension + 63) / 64;
    if (!checked_mul_size(dimension, words, &row_words) ||
        !checked_mul_size(row_words, sizeof(uint64_t), &bytes))
        die("Toeplitz allocation size overflow");
    if (bytes > max_bytes)
        die("Toeplitz valuation matrix exceeds the memory limit");
    matrix = calloc(1, bytes);
    if (matrix == NULL)
        die("cannot allocate Toeplitz valuation matrix");

    for (block_row = 0; block_row < order; ++block_row) {
        for (block_col = 0; block_col <= block_row; ++block_col) {
            size_t polynomial_degree = block_row - block_col;
            for (i = 0; i < p->n; ++i) {
                uint64_t *dst = matrix + (block_row * p->n + i) * words;
                if (!reverse) {
                    if (polynomial_degree < p->ncoeff) {
                        const uint64_t *src =
                            poly_const_row(p, polynomial_degree, i);
                        memcpy(dst + block_col * p->words, src,
                               p->words * sizeof(*src));
                    }
                } else {
                    size_t j;
                    for (j = 0; j < p->n; ++j) {
                        size_t original_degree;
                        const uint64_t *src;
                        if (polynomial_degree > p->col_degree[j])
                            continue;
                        original_degree = p->col_degree[j] - polynomial_degree;
                        if (original_degree >= p->ncoeff)
                            continue;
                        src = poly_const_row(p, original_degree, i);
                        if ((src[j / 64] >> (j % 64)) & UINT64_C(1))
                            dst[block_col * p->words + j / 64] |=
                                UINT64_C(1) << (j % 64);
                    }
                }
            }
        }
    }
    *dimension_out = dimension;
    *bytes_out = bytes;
    return matrix;
}

static size_t determinant_valuation(const poly_matrix *p, int reverse,
                                    size_t max_order, size_t max_bytes,
                                    size_t *constant_rank)
{
    size_t order;
    size_t previous_nullity = 0;
    size_t previous_increment = p->n;

    for (order = 1; order <= max_order; ++order) {
        size_t dimension, bytes, rank, nullity, increment;
        uint64_t *toeplitz = build_toeplitz(p, order, reverse, max_bytes,
                                            &dimension, &bytes);
        rank = dense_rank(toeplitz, dimension, dimension);
        free(toeplitz);
        nullity = dimension - rank;
        if (order == 1)
            *constant_rank = rank;
        if (nullity < previous_nullity)
            die("Toeplitz nullity decreased unexpectedly");
        increment = nullity - previous_nullity;
        if (increment > previous_increment)
            die("Toeplitz nullity increments are not nonincreasing");
        printf("%s_order=%zu dimension=%zu rank=%zu nullity=%zu increment=%zu bytes=%zu\n",
               reverse ? "reverse" : "forward", order, dimension, rank,
               nullity, increment, bytes);
        if (increment == 0)
            return previous_nullity;
        previous_nullity = nullity;
        previous_increment = increment;
    }
    die("determinant valuation did not stabilize within --max-order");
    return 0;
}

static size_t parse_size(const char *text, const char *name)
{
    char *end = NULL;
    uintmax_t value;
    errno = 0;
    value = strtoumax(text, &end, 10);
    if (errno != 0 || end == text || *end != '\0' || value > SIZE_MAX) {
        fprintf(stderr, "error: invalid %s '%s'\n", name, text);
        exit(EXIT_FAILURE);
    }
    return (size_t)value;
}

static void usage(const char *program)
{
    fprintf(stderr,
            "usage: %s BLOCK_SIZE F_PREFIX [--max-order K] [--max-mib M]\n",
            program);
}

int main(int argc, char **argv)
{
    poly_matrix p;
    size_t n, max_order = 64, max_mib = 1024, max_bytes;
    size_t i, column_degree_sum = 0;
    size_t constant_rank, reversed_constant_rank;
    size_t valuation, reverse_valuation, determinant_degree;
    size_t nonzero_spectral_lower_bound;

    if (argc < 3) {
        usage(argv[0]);
        return EXIT_FAILURE;
    }
    n = parse_size(argv[1], "block size");
    for (i = 3; i < (size_t)argc; ++i) {
        if (strcmp(argv[i], "--max-order") == 0 && i + 1 < (size_t)argc)
            max_order = parse_size(argv[++i], "maximum order");
        else if (strcmp(argv[i], "--max-mib") == 0 && i + 1 < (size_t)argc)
            max_mib = parse_size(argv[++i], "memory limit");
        else {
            usage(argv[0]);
            return EXIT_FAILURE;
        }
    }
    if (max_order == 0 || max_mib == 0)
        die("maximum order and memory limit must be positive");
    if (!checked_mul_size(max_mib, 1024U * 1024U, &max_bytes))
        die("memory limit overflow");

    load_polynomial(&p, n, argv[2]);
    for (i = 0; i < p.n; ++i) {
        if (column_degree_sum > SIZE_MAX - p.col_degree[i])
            die("sum of column degrees overflow");
        column_degree_sum += p.col_degree[i];
    }

    printf("block_size=%zu coefficient_count=%zu polynomial_matrix_bytes=%zu\n",
           p.n, p.ncoeff, p.ncoeff * p.n * p.words * sizeof(uint64_t));
    printf("column_degree_sum=%zu\n", column_degree_sum);
    valuation = determinant_valuation(&p, 0, max_order, max_bytes,
                                      &constant_rank);
    reverse_valuation = determinant_valuation(&p, 1, max_order, max_bytes,
                                              &reversed_constant_rank);
    if (reverse_valuation > column_degree_sum)
        die("reverse valuation exceeds the sum of column degrees");
    determinant_degree = column_degree_sum - reverse_valuation;
    if (valuation > determinant_degree)
        die("determinant valuation exceeds determinant degree");
    nonzero_spectral_lower_bound = determinant_degree - valuation;

    printf("constant_coefficient_rank=%zu/%zu\n", constant_rank, p.n);
    printf("reversed_constant_coefficient_rank=%zu/%zu\n",
           reversed_constant_rank, p.n);
    printf("determinant_degree=%zu\n", determinant_degree);
    printf("determinant_codegree=%zu\n", valuation);
    printf("moment_offset_assumption=1\n");
    printf("nonzero_spectral_lower_bound=%zu\n",
           nonzero_spectral_lower_bound);
    printf("rank_lower_bound=%zu\n", determinant_degree);

    free_polynomial(&p);
    return EXIT_SUCCESS;
}
