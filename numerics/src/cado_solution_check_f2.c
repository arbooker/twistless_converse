#define _FILE_OFFSET_BITS 64

/*
 * Exact rank/check utility for many CADO GF(2) cleanup files.
 *
 * A cleanup file contains one little-endian uint64_t per matrix column; its
 * 64 bits are 64 candidate vectors.  In verification mode this program
 * checks every candidate against every row of a square CADO matrix.  In
 * rank-only mode it computes the rank of the union of arbitrarily many
 * cleanup files, optionally stopping once a certified target is reached.
 *
 * The older cado_kernel_project_f2 utility was designed for at most four
 * cleanup files and explicitly materialized a cleaned kernel basis.  That is
 * unsuitable for the N=97 width-512 calculation.  This companion leaves the
 * earlier program unchanged.
 */

#include <errno.h>
#include <inttypes.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

typedef uint64_t u64;

static void die(const char *message)
{
    fprintf(stderr, "error: %s\n", message);
    exit(EXIT_FAILURE);
}

static void die_path(const char *what, const char *path)
{
    fprintf(stderr, "error: %s '%s': %s\n", what, path, strerror(errno));
    exit(EXIT_FAILURE);
}

static void *xmalloc(size_t bytes)
{
    void *p = malloc(bytes);
    if (p == NULL && bytes != 0)
        die("out of memory");
    return p;
}

static int checked_mul_size(size_t a, size_t b, size_t *out)
{
    if (a != 0 && b > SIZE_MAX / a)
        return 0;
    *out = a * b;
    return 1;
}

static u64 file_size(const char *path)
{
    struct stat st;
    if (stat(path, &st) != 0)
        die_path("cannot stat", path);
    if (st.st_size < 0)
        die("negative file size");
    return (u64)st.st_size;
}

static char *companion_name(const char *matrix, const char *kind)
{
    size_t n = strlen(matrix);
    size_t k = strlen(kind);
    char *result;
    if (n < 4 || strcmp(matrix + n - 4, ".bin") != 0)
        die("matrix name must end in .bin");
    result = xmalloc(n + k + 1);
    memcpy(result, matrix, n - 4);
    result[n - 4] = '\0';
    strcat(result, kind);
    strcat(result, ".bin");
    return result;
}

static uint32_t read_u32_le(FILE *file)
{
    unsigned char b[4];
    if (fread(b, sizeof(b), 1, file) != 1)
        die("unexpected end of matrix or read error");
    return (uint32_t)b[0] | ((uint32_t)b[1] << 8) |
           ((uint32_t)b[2] << 16) | ((uint32_t)b[3] << 24);
}

static u64 read_u64_le(FILE *file)
{
    unsigned char b[8];
    u64 value = 0;
    unsigned int i;
    if (fread(b, sizeof(b), 1, file) != 1)
        die("unexpected end of solution file or read error");
    for (i = 0; i < 8; ++i)
        value |= (u64)b[i] << (8U * i);
    return value;
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

static int vector_zero(const u64 *v, size_t words)
{
    size_t i;
    for (i = 0; i < words; ++i)
        if (v[i] != 0)
            return 0;
    return 1;
}

static size_t highest_bit(const u64 *v, size_t words)
{
    size_t i;
    for (i = words; i-- > 0;) {
        if (v[i] != 0)
            return 64U * i + 63U - (size_t)__builtin_clzll(v[i]);
    }
    die("internal pivot request for zero vector");
    return 0;
}

static int insert_vector(u64 *basis, unsigned char *has_pivot, u64 *v,
                         size_t words)
{
    while (!vector_zero(v, words)) {
        size_t pivot = highest_bit(v, words);
        u64 *row = basis + pivot * words;
        size_t i;
        if (!has_pivot[pivot]) {
            memcpy(row, v, words * sizeof(*v));
            has_pivot[pivot] = 1;
            return 1;
        }
        for (i = 0; i < words; ++i)
            v[i] ^= row[i];
    }
    return 0;
}

static u64 **load_file_major(char **paths, size_t count,
                             u64 *coordinate_count_out)
{
    u64 coordinate_count;
    u64 **files;
    size_t file;
    if (count == 0)
        die("no solution files supplied");
    if ((file_size(paths[0]) & 7U) != 0)
        die("solution-file size is not a multiple of eight");
    coordinate_count = file_size(paths[0]) / 8U;
    if (coordinate_count > SIZE_MAX / sizeof(u64))
        die("solution file is too large for this machine");
    files = xmalloc(count * sizeof(*files));
    for (file = 0; file < count; ++file) {
        FILE *input;
        u64 coordinate;
        if (file_size(paths[file]) != 8U * coordinate_count)
            die("solution files have unequal sizes");
        input = fopen(paths[file], "rb");
        if (input == NULL)
            die_path("cannot open", paths[file]);
        files[file] = xmalloc((size_t)coordinate_count * sizeof(u64));
        for (coordinate = 0; coordinate < coordinate_count; ++coordinate)
            files[file][coordinate] = read_u64_le(input);
        if (fgetc(input) != EOF || ferror(input) || fclose(input) != 0)
            die("error finishing solution file");
    }
    *coordinate_count_out = coordinate_count;
    return files;
}

static size_t candidate_rank(u64 **solutions, size_t file_count,
                             u64 coordinate_count, size_t stop_at,
                             u64 *coordinates_examined)
{
    size_t lanes = 64U * file_count;
    size_t basis_words;
    u64 *basis;
    u64 *value;
    unsigned char *has_pivot;
    size_t rank = 0;
    u64 coordinate;
    if (!checked_mul_size(lanes, file_count, &basis_words))
        die("rank-basis size overflow");
    basis = xmalloc(basis_words * sizeof(*basis));
    value = xmalloc(file_count * sizeof(*value));
    has_pivot = xmalloc(lanes);
    memset(basis, 0, basis_words * sizeof(*basis));
    memset(has_pivot, 0, lanes);
    for (coordinate = 0; coordinate < coordinate_count; ++coordinate) {
        size_t file;
        for (file = 0; file < file_count; ++file)
            value[file] = solutions[file][coordinate];
        rank += (size_t)insert_vector(basis, has_pivot, value, file_count);
        if ((stop_at != 0 && rank >= stop_at) ||
            rank == 64U * file_count) {
            ++coordinate;
            break;
        }
    }
    *coordinates_examined = coordinate;
    free(has_pivot);
    free(value);
    free(basis);
    return rank;
}

static u64 *transpose_solutions(u64 **solutions, size_t file_count,
                                u64 coordinate_count)
{
    size_t words, bytes;
    u64 *packed;
    u64 coordinate;
    if (coordinate_count > SIZE_MAX ||
        !checked_mul_size((size_t)coordinate_count, file_count, &words))
        die("packed solution size overflow");
    if (!checked_mul_size(words, sizeof(*packed), &bytes))
        die("packed solution byte-size overflow");
    packed = xmalloc(bytes);
    for (coordinate = 0; coordinate < coordinate_count; ++coordinate) {
        size_t file;
        u64 *dst = packed + (size_t)coordinate * file_count;
        for (file = 0; file < file_count; ++file)
            dst[file] = solutions[file][coordinate];
    }
    return packed;
}

static void usage(const char *program)
{
    fprintf(stderr,
            "usage: %s MATRIX.bin W1 [W2 ...]\n"
            "       %s --rank-only [--stop-at K] W1 [W2 ...]\n",
            program, program);
}

int main(int argc, char **argv)
{
    int rank_only = 0;
    size_t stop_at = 0;
    int first_path = 1;
    const char *matrix_path = NULL;
    char **solution_paths;
    size_t file_count, lanes, rank;
    u64 coordinate_count, coordinates_examined;
    u64 **solutions;
    size_t file;

    if (argc < 3) {
        usage(argv[0]);
        return EXIT_FAILURE;
    }
    if (strcmp(argv[1], "--rank-only") == 0) {
        rank_only = 1;
        first_path = 2;
        if (first_path + 1 < argc &&
            strcmp(argv[first_path], "--stop-at") == 0) {
            stop_at = parse_size(argv[first_path + 1], "stop rank");
            first_path += 2;
        }
    } else {
        matrix_path = argv[1];
        first_path = 2;
    }
    if (first_path >= argc) {
        usage(argv[0]);
        return EXIT_FAILURE;
    }
    solution_paths = argv + first_path;
    file_count = (size_t)(argc - first_path);
    if (file_count > SIZE_MAX / 64U)
        die("candidate-lane count overflow");
    lanes = 64U * file_count;
    if (stop_at > lanes)
        die("stop rank exceeds candidate-lane count");

    solutions = load_file_major(solution_paths, file_count,
                                &coordinate_count);
    rank = candidate_rank(solutions, file_count, coordinate_count, stop_at,
                          &coordinates_examined);

    if (rank_only) {
        printf("mode=rank-only solution_coordinates=%" PRIu64
               " solution_files=%zu candidate_lanes=%zu candidate_rank=%zu"
               " coordinates_examined=%" PRIu64 " stop_at=%zu\n",
               coordinate_count, file_count, lanes, rank,
               coordinates_examined, stop_at);
        for (file = 0; file < file_count; ++file)
            free(solutions[file]);
        free(solutions);
        return stop_at != 0 && rank < stop_at ? 2 : EXIT_SUCCESS;
    }

    {
        char *rw_path = companion_name(matrix_path, ".rw");
        char *cw_path = companion_name(matrix_path, ".cw");
        u64 rows, columns, nonzeros = 0, bad_rows = 0;
        u64 bad_row_lane_products = 0;
        u64 *packed;
        u64 *accumulator;
        FILE *matrix;
        u64 row;
        if ((file_size(rw_path) & 3U) != 0 ||
            (file_size(cw_path) & 3U) != 0)
            die("matrix weight-file size is not a multiple of four");
        rows = file_size(rw_path) / 4U;
        columns = file_size(cw_path) / 4U;
        if (coordinate_count != columns)
            die("solution length does not equal square-matrix dimension");

        packed = transpose_solutions(solutions, file_count, coordinate_count);
        accumulator = xmalloc(file_count * sizeof(*accumulator));
        for (file = 0; file < file_count; ++file)
            free(solutions[file]);
        free(solutions);

        matrix = fopen(matrix_path, "rb");
        if (matrix == NULL)
            die_path("cannot open", matrix_path);
        for (row = 0; row < rows; ++row) {
            uint32_t weight = read_u32_le(matrix);
            uint32_t entry;
            size_t word;
            int bad = 0;
            memset(accumulator, 0, file_count * sizeof(*accumulator));
            nonzeros += weight;
            for (entry = 0; entry < weight; ++entry) {
                uint32_t column = read_u32_le(matrix);
                const u64 *value;
                if ((u64)column >= columns)
                    die("matrix contains an out-of-range column index");
                value = packed + (size_t)column * file_count;
                for (word = 0; word < file_count; ++word)
                    accumulator[word] ^= value[word];
            }
            for (word = 0; word < file_count; ++word) {
                bad |= accumulator[word] != 0;
                bad_row_lane_products +=
                    (u64)__builtin_popcountll(accumulator[word]);
            }
            bad_rows += (u64)bad;
        }
        if (fgetc(matrix) != EOF || ferror(matrix) || fclose(matrix) != 0)
            die("error finishing matrix file");

        printf("mode=verify matrix_rows=%" PRIu64
               " matrix_columns=%" PRIu64 " matrix_nonzeros=%" PRIu64
               " solution_files=%zu candidate_lanes=%zu candidate_rank=%zu"
               " coordinates_examined=%" PRIu64 " bad_rows=%" PRIu64
               " bad_row_lane_products=%" PRIu64 "\n",
               rows, columns, nonzeros, file_count, lanes, rank,
               coordinates_examined, bad_rows, bad_row_lane_products);
        free(accumulator);
        free(packed);
        free(cw_path);
        free(rw_path);
        return bad_rows == 0 ? EXIT_SUCCESS : EXIT_FAILURE;
    }
}
