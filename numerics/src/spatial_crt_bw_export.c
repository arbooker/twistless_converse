/* Export one parity common-core CRT matrix for CADO-NFS Block Wiedemann.
 *
 * This is a non-overwriting companion to spatial_crt_kernel_f2_parity_core.c.
 * It exports exactly the common-core rows used there, before elimination, in
 * CADO-NFS's headerless binary sparse-matrix format:
 *
 *   uint32 row_weight; uint32 column_index[row_weight]
 *
 * All integers in the files are little-endian.  Companion row- and
 * column-weight files are written beside MATRIX.bin as MATRIX.rw.bin and
 * MATRIX.cw.bin.
 *
 * Assumptions checked at startup:
 *   - N is an odd prime;
 *   - Q=N*M, gcd(N,M)=1, and M is even;
 *   - M/2 and the common-core row count fit CADO's 32-bit dimensions.
 *
 * Compile:
 *   gcc -std=gnu11 -O3 -Wall -Wextra -Werror \
 *       -o spatial_crt_bw_export spatial_crt_bw_export.c
 *
 * Usage:
 *   ./spatial_crt_bw_export N Q PARITY MATRIX.bin
 *   ./spatial_crt_bw_export N Q PARITY --estimate
 *
 * PARITY is 0 or 1 and refers to the residue parity in the even-j block.
 */

#include <errno.h>
#include <inttypes.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t u64;
typedef int64_t i64;
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

static void *xcalloc(size_t count, size_t size) {
    if (size != 0 && count > SIZE_MAX / size)
        die("allocation-size overflow");
    void *result = calloc(count, size);
    if (!result && count != 0 && size != 0)
        die("out of memory");
    return result;
}

static u64 parse_positive_u64(const char *text, const char *name) {
    char *end = NULL;
    errno = 0;
    unsigned long long value = strtoull(text, &end, 10);
    if (errno != 0 || end == text || *end != '\0' || value == 0) {
        fprintf(stderr, "%s must be a positive integer\n", name);
        exit(EXIT_FAILURE);
    }
    return (u64)value;
}

static int parse_parity(const char *text) {
    if (strcmp(text, "0") == 0)
        return 0;
    if (strcmp(text, "1") == 0)
        return 1;
    die("PARITY must be 0 or 1");
    return -1;
}

static u64 gcd_u64(u64 a, u64 b) {
    while (b != 0) {
        u64 next = a % b;
        a = b;
        b = next;
    }
    return a;
}

static u64 totient_u64(u64 n) {
    u64 result = n;
    u64 remaining = n;
    for (u64 p = 2; p <= remaining / p; p += (p == 2) ? 1 : 2) {
        if (remaining % p != 0)
            continue;
        result -= result / p;
        do {
            remaining /= p;
        } while (remaining % p == 0);
    }
    if (remaining > 1)
        result -= result / remaining;
    return result;
}

static int is_odd_prime_u64(u64 n) {
    if (n < 3 || (n & 1) == 0)
        return 0;
    for (u64 p = 3; p <= n / p; p += 2)
        if (n % p == 0)
            return 0;
    return 1;
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

static u64 positive_mod_i64(i64 value, u64 modulus) {
    i64 signed_modulus = (i64)modulus;
    i64 result = value % signed_modulus;
    if (result < 0)
        result += signed_modulus;
    return (u64)result;
}

/* h=min{h>=0:h^2 q^2 >= M^2 N}, using exact 128-bit arithmetic. */
static u64 buffered_radius(u64 n_level, u64 multiplier, u64 q) {
    u128 target = (u128)multiplier * multiplier * n_level;
    u128 q_squared = (u128)q * q;
    u64 low = 0;
    u64 high = n_level * (multiplier / q);
    if (multiplier % q != 0)
        high += n_level;
    while (low < high) {
        u64 middle = low + (high - low) / 2;
        if ((u128)middle * middle * q_squared >= target)
            high = middle;
        else
            low = middle + 1;
    }
    return low;
}

static void legal_interval(u64 n_level, u64 residue, u64 h,
                           i64 *lower, i64 *upper) {
    if (n_level > (u64)INT64_MAX || residue > (u64)INT64_MAX ||
        h > (u64)INT64_MAX)
        die("interval parameter exceeds signed 64-bit range");
    i64 n = (i64)n_level;
    i64 r = (i64)residue;
    i64 radius = (i64)h;
    *lower = ceil_div(1 - radius - r, n);
    *upper = floor_div(radius - 2 - r, n);
}

static void core_interval(u64 n_level, int residue_parity, u64 h,
                          i64 *lower, i64 *upper) {
    u64 first_residue = (u64)residue_parity;
    u64 last_residue = n_level - 1;
    if ((int)(last_residue & 1) != residue_parity)
        last_residue--;
    i64 unused_upper;
    i64 unused_lower;
    legal_interval(n_level, first_residue, h, lower, &unused_upper);
    legal_interval(n_level, last_residue, h, &unused_lower, upper);
}

static i64 first_with_parity(i64 lower, int parity) {
    if ((int)(lower & 1) != parity)
        lower++;
    return lower;
}

static u64 count_selected(i64 lower, i64 upper, int parity) {
    i64 first = first_with_parity(lower, parity);
    if (first > upper)
        return 0;
    return (u64)((upper - first) / 2 + 1);
}

static int compare_u64(const void *left, const void *right) {
    u64 a = *(const u64 *)left;
    u64 b = *(const u64 *)right;
    return (a > b) - (a < b);
}

static u64 *make_divisors(u64 n, size_t *count_out) {
    size_t count = 0;
    for (u64 d = 1; d <= n / d; d++)
        if (n % d == 0)
            count += (d == n / d) ? 1U : 2U;
    u64 *divisors = xmalloc(count * sizeof(*divisors));
    size_t index = 0;
    for (u64 d = 1; d <= n / d; d++) {
        if (n % d != 0)
            continue;
        divisors[index++] = d;
        if (d != n / d)
            divisors[index++] = n / d;
    }
    qsort(divisors, count, sizeof(*divisors), compare_u64);
    *count_out = count;
    return divisors;
}

static uint32_t *make_units(u64 q, uint32_t *count_out) {
    if (q > UINT32_MAX)
        die("divisor exceeds CADO's 32-bit index range");
    uint32_t *units = xmalloc((size_t)q * sizeof(*units));
    uint32_t count = 0;
    for (u64 a = 0; a < q; a++)
        if (gcd_u64(a, q) == 1)
            units[count++] = (uint32_t)a;
    *count_out = count;
    return units;
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

static char *companion_name(const char *matrix_name, const char *kind) {
    size_t length = strlen(matrix_name);
    if (length < 4 || strcmp(matrix_name + length - 4, ".bin") != 0)
        die("matrix output name must end in .bin");
    size_t kind_length = strlen(kind);
    char *result = xmalloc(length + kind_length + 1);
    memcpy(result, matrix_name, length - 4);
    result[length - 4] = '\0';
    strcat(result, kind);
    strcat(result, ".bin");
    return result;
}

int main(int argc, char **argv) {
    if (argc != 5) {
        fprintf(stderr,
                "Usage: %s N Q PARITY MATRIX.bin|--estimate\n", argv[0]);
        return EXIT_FAILURE;
    }

    u64 n_level = parse_positive_u64(argv[1], "N");
    u64 q_total = parse_positive_u64(argv[2], "Q");
    int residue_parity = parse_parity(argv[3]);
    const char *matrix_name = argv[4];
    int estimate_only = strcmp(matrix_name, "--estimate") == 0;

    if (!is_odd_prime_u64(n_level))
        die("require N to be an odd prime");
    if (q_total % n_level != 0)
        die("require N|Q");
    u64 multiplier = q_total / n_level;
    if (gcd_u64(n_level, multiplier) != 1)
        die("require gcd(N,Q/N)=1");
    if ((multiplier & 1) != 0)
        die("require even M=Q/N");
    u64 dimension = multiplier / 2;
    if (dimension > UINT32_MAX)
        die("M/2 exceeds CADO's 32-bit matrix dimension");

    size_t divisor_count = 0;
    u64 *divisors = make_divisors(multiplier, &divisor_count);
    if (estimate_only) {
        u64 row_count = 0;
        u64 nonzero_count = 0;
        for (size_t divisor_index = 0; divisor_index < divisor_count;
             divisor_index++) {
            u64 q = divisors[divisor_index];
            u64 step = multiplier / q;
            int v_parity = residue_parity ^ (int)(step & 1);
            u64 h = buffered_radius(n_level, multiplier, q);
            i64 lower;
            i64 upper;
            core_interval(n_level, residue_parity, h, &lower, &upper);
            u64 rows_for_q = count_selected(lower, upper, v_parity);
            row_count += rows_for_q;
            nonzero_count += rows_for_q * totient_u64(q);
        }
        printf("N=%" PRIu64 " M=%" PRIu64 " Q=%" PRIu64
               " parity=%d rows=%" PRIu64 " columns=%" PRIu64
               " row_margin=%" PRId64 " nonzeros=%" PRIu64 "\n",
               n_level, multiplier, q_total, residue_parity, row_count,
               dimension, (i64)row_count - (i64)dimension, nonzero_count);
        free(divisors);
        return EXIT_SUCCESS;
    }

    char *row_weight_name = companion_name(matrix_name, ".rw");
    char *column_weight_name = companion_name(matrix_name, ".cw");
    FILE *matrix = fopen(matrix_name, "wb");
    FILE *row_weights = fopen(row_weight_name, "wb");
    FILE *column_weights = fopen(column_weight_name, "wb");
    if (!matrix || !row_weights || !column_weights)
        die("cannot open an output file");

    uint32_t *column_weight = xcalloc((size_t)dimension,
                                      sizeof(*column_weight));
    u64 row_count = 0;
    u64 nonzero_count = 0;

    for (size_t divisor_index = 0; divisor_index < divisor_count;
         divisor_index++) {
        u64 q = divisors[divisor_index];
        u64 step = multiplier / q;
        int v_parity = residue_parity ^ (int)(step & 1);
        u64 h = buffered_radius(n_level, multiplier, q);
        i64 lower;
        i64 upper;
        core_interval(n_level, residue_parity, h, &lower, &upper);
        u64 rows_for_q = count_selected(lower, upper, v_parity);
        if (rows_for_q == 0)
            continue;

        uint32_t unit_count = 0;
        uint32_t *units = make_units(q, &unit_count);
        i64 first = first_with_parity(lower, v_parity);
        for (i64 v = first; v <= upper; v += 2) {
            write_u32_le(matrix, unit_count);
            write_u32_le(row_weights, unit_count);
            u64 v_mod = positive_mod_i64(v, multiplier);
            for (uint32_t unit_index = 0; unit_index < unit_count;
                 unit_index++) {
                u64 t = v_mod + (u64)units[unit_index] * step;
                if (t >= multiplier)
                    t %= multiplier;
                if (((t + (u64)residue_parity) & 1) != 0)
                    die("internal parity error while exporting row");
                u64 column = (t - (u64)residue_parity) / 2;
                if (column >= dimension)
                    die("internal column-index error");
                write_u32_le(matrix, (uint32_t)column);
                if (column_weight[column] == UINT32_MAX)
                    die("column weight exceeds uint32 range");
                column_weight[column]++;
            }
            row_count++;
            nonzero_count += unit_count;
        }
        free(units);
    }

    if (row_count > UINT32_MAX)
        die("common-core row count exceeds CADO's 32-bit dimension");
    for (u64 column = 0; column < dimension; column++)
        write_u32_le(column_weights, column_weight[column]);

    if (fclose(matrix) != 0 || fclose(row_weights) != 0 ||
        fclose(column_weights) != 0)
        die("error closing an output file");

    printf("N=%" PRIu64 " M=%" PRIu64 " Q=%" PRIu64
           " parity=%d rows=%" PRIu64 " columns=%" PRIu64
           " nonzeros=%" PRIu64 " matrix=%s rw=%s cw=%s\n",
           n_level, multiplier, q_total, residue_parity, row_count,
           dimension, nonzero_count, matrix_name, row_weight_name,
           column_weight_name);

    free(divisors);
    free(column_weight);
    free(row_weight_name);
    free(column_weight_name);
    return EXIT_SUCCESS;
}
