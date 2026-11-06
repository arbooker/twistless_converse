/* Complete a tall rectangular CADO-NFS GF(2) sparse matrix C to a square
 * matrix [C | G], where every column of G is a unit vector in a distinct,
 * pseudorandomly selected row.
 *
 * If C is R by D with R >= D, G has R-D columns.  This avoids the large
 * artificial zero-column kernel introduced by CADO's normal square padding.
 * Whenever the selected unit columns are independent modulo im(C),
 *
 *       ker([C | G]) = ker(C) x {0}.
 *
 * The condition is directly testable after Block Wiedemann: all recovered
 * kernel vectors must have zero appended coordinates, and their first D
 * coordinates can be checked against C.  Different seeds give independent
 * row selections.  Existing output files are never overwritten.
 *
 * Input and output format:
 *   uint32 row_weight; uint32 column_index[row_weight]
 * with little-endian integers and .rw.bin/.cw.bin companion files.
 *
 * Compile:
 *   gcc -std=gnu11 -O3 -Wall -Wextra -Werror \
 *       -o cado_square_complete_f2 cado_square_complete_f2.c
 *
 * Usage:
 *   ./cado_square_complete_f2 INPUT.bin SEED OUTPUT.bin
 */

#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

typedef uint64_t u64;
typedef __uint128_t u128;

static void die(const char *message) {
    fprintf(stderr, "%s\n", message);
    exit(EXIT_FAILURE);
}

static void *xmalloc(size_t size) {
    void *result = malloc(size);
    if (!result && size != 0)
        die("out of memory");
    return result;
}

static char *companion_name(const char *matrix_name, const char *kind) {
    size_t length = strlen(matrix_name);
    if (length < 4 || strcmp(matrix_name + length - 4, ".bin") != 0)
        die("matrix name must end in .bin");
    size_t kind_length = strlen(kind);
    char *result = xmalloc(length + kind_length + 1);
    memcpy(result, matrix_name, length - 4);
    result[length - 4] = '\0';
    strcat(result, kind);
    strcat(result, ".bin");
    return result;
}

static u64 file_u32_count(const char *name) {
    struct stat information;
    if (stat(name, &information) != 0) {
        fprintf(stderr, "cannot stat %s: %s\n", name, strerror(errno));
        exit(EXIT_FAILURE);
    }
    if (information.st_size < 0 || (information.st_size & 3) != 0)
        die("weight-file size is not a nonnegative multiple of four");
    return (u64)information.st_size / 4;
}

static u64 parse_u64(const char *text, const char *name) {
    char *end = NULL;
    errno = 0;
    unsigned long long value = strtoull(text, &end, 10);
    if (errno != 0 || end == text || *end != '\0') {
        fprintf(stderr, "%s must be an unsigned integer\n", name);
        exit(EXIT_FAILURE);
    }
    return (u64)value;
}

static uint32_t read_u32_le(FILE *file) {
    unsigned char bytes[4];
    if (fread(bytes, sizeof(bytes), 1, file) != 1)
        die("unexpected end of input or read error");
    return (uint32_t)bytes[0] | ((uint32_t)bytes[1] << 8) |
           ((uint32_t)bytes[2] << 16) | ((uint32_t)bytes[3] << 24);
}

static void write_u32_le(FILE *file, uint32_t value) {
    unsigned char bytes[4];
    bytes[0] = (unsigned char)value;
    bytes[1] = (unsigned char)(value >> 8);
    bytes[2] = (unsigned char)(value >> 16);
    bytes[3] = (unsigned char)(value >> 24);
    if (fwrite(bytes, sizeof(bytes), 1, file) != 1)
        die("error writing output file");
}

static uint32_t *read_weights(const char *name, u64 count, u64 *sum_out) {
    if (count > SIZE_MAX / sizeof(uint32_t))
        die("weight array is too large for this machine");
    FILE *file = fopen(name, "rb");
    if (!file) {
        fprintf(stderr, "cannot open %s: %s\n", name, strerror(errno));
        exit(EXIT_FAILURE);
    }
    uint32_t *weights = xmalloc((size_t)count * sizeof(*weights));
    u64 sum = 0;
    for (u64 index = 0; index < count; index++) {
        weights[index] = read_u32_le(file);
        if (UINT64_MAX - sum < weights[index])
            die("nonzero-count overflow");
        sum += weights[index];
    }
    if (fgetc(file) != EOF || ferror(file) || fclose(file) != 0)
        die("error finishing weight file");
    *sum_out = sum;
    return weights;
}

static FILE *open_new(const char *name) {
    FILE *file = fopen(name, "wbx");
    if (!file) {
        fprintf(stderr, "cannot create %s without overwriting: %s\n", name,
                strerror(errno));
        exit(EXIT_FAILURE);
    }
    return file;
}

static u64 splitmix64(u64 *state) {
    u64 value = (*state += UINT64_C(0x9e3779b97f4a7c15));
    value = (value ^ (value >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    value = (value ^ (value >> 27)) * UINT64_C(0x94d049bb133111eb);
    return value ^ (value >> 31);
}

static u64 uniform_below(u64 *state, u64 bound) {
    if (bound == 0)
        die("internal zero random bound");
    return (u64)(((u128)splitmix64(state) * bound) >> 64);
}

int main(int argc, char **argv) {
    if (argc != 4) {
        fprintf(stderr, "Usage: %s INPUT.bin SEED OUTPUT.bin\n", argv[0]);
        return EXIT_FAILURE;
    }
    const char *input_name = argv[1];
    u64 random_state = parse_u64(argv[2], "SEED");
    const char *output_name = argv[3];
    if (strcmp(input_name, output_name) == 0)
        die("input and output names must differ");

    char *input_rw_name = companion_name(input_name, ".rw");
    char *input_cw_name = companion_name(input_name, ".cw");
    char *output_rw_name = companion_name(output_name, ".rw");
    char *output_cw_name = companion_name(output_name, ".cw");

    u64 row_count = file_u32_count(input_rw_name);
    u64 column_count = file_u32_count(input_cw_name);
    if (row_count < column_count)
        die("input must have at least as many rows as columns");
    if (row_count > UINT32_MAX)
        die("square output exceeds CADO's uint32 index range");
    u64 added_count = row_count - column_count;

    u64 row_nonzeros = 0;
    u64 column_nonzeros = 0;
    uint32_t *row_weights =
        read_weights(input_rw_name, row_count, &row_nonzeros);
    uint32_t *column_weights =
        read_weights(input_cw_name, column_count, &column_nonzeros);
    if (row_nonzeros != column_nonzeros)
        die("row- and column-weight files disagree on the nonzero count");

    uint32_t *rows = xmalloc((size_t)row_count * sizeof(*rows));
    uint32_t *added_column = xmalloc((size_t)row_count * sizeof(*added_column));
    for (u64 row = 0; row < row_count; row++) {
        rows[row] = (uint32_t)row;
        added_column[row] = UINT32_MAX;
    }
    for (u64 index = 0; index < added_count; index++) {
        u64 chosen = index + uniform_below(&random_state, row_count - index);
        uint32_t temporary = rows[index];
        rows[index] = rows[chosen];
        rows[chosen] = temporary;
        added_column[rows[index]] = (uint32_t)(column_count + index);
    }

    FILE *input = fopen(input_name, "rb");
    if (!input) {
        fprintf(stderr, "cannot open %s: %s\n", input_name, strerror(errno));
        return EXIT_FAILURE;
    }
    FILE *output = open_new(output_name);
    FILE *output_rw = open_new(output_rw_name);
    FILE *output_cw = open_new(output_cw_name);

    for (u64 row = 0; row < row_count; row++) {
        uint32_t weight = read_u32_le(input);
        if (weight != row_weights[row])
            die("matrix row weight disagrees with companion file");
        uint32_t extra = added_column[row] != UINT32_MAX;
        if (weight == UINT32_MAX && extra)
            die("row-weight overflow");
        write_u32_le(output, weight + extra);
        write_u32_le(output_rw, weight + extra);
        for (uint32_t entry = 0; entry < weight; entry++) {
            uint32_t column = read_u32_le(input);
            if ((u64)column >= column_count)
                die("matrix contains an out-of-range column index");
            write_u32_le(output, column);
        }
        if (extra)
            write_u32_le(output, added_column[row]);
    }
    if (fgetc(input) != EOF || ferror(input) || fclose(input) != 0)
        die("error finishing input matrix");
    for (u64 column = 0; column < column_count; column++)
        write_u32_le(output_cw, column_weights[column]);
    for (u64 column = 0; column < added_count; column++)
        write_u32_le(output_cw, 1);
    if (fclose(output) != 0 || fclose(output_rw) != 0 ||
        fclose(output_cw) != 0)
        die("error closing an output file");

    printf("input_rows=%" PRIu64 " input_columns=%" PRIu64
           " input_nonzeros=%" PRIu64 " added_unit_columns=%" PRIu64
           " output_dimension=%" PRIu64 " output_nonzeros=%" PRIu64
           " output=%s\n",
           row_count, column_count, row_nonzeros, added_count, row_count,
           row_nonzeros + added_count, output_name);

    free(added_column);
    free(rows);
    free(column_weights);
    free(row_weights);
    free(output_cw_name);
    free(output_rw_name);
    free(input_cw_name);
    free(input_rw_name);
    return EXIT_SUCCESS;
}
