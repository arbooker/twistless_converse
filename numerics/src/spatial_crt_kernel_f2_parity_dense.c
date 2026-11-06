/* Exact large-M CRT kernel/top-up engine over F_2: dense fast version.
 *
 * This uses the same exact parity and common-core reductions as
 * spatial_crt_kernel_f2_parity_core.c, but deliberately avoids compressed
 * RRE.  One parity core at a time is reduced by dense forward echelon;
 * its usually small nullspace is recovered by back substitution.  Sector
 * endpoint rows then act on that small core kernel, and only the resulting
 * translated sector kernels are inserted into the output echelon basis.
 *
 * For N=71, M=360360 the core dimension is D=M/2=180180.  One dense core
 * arena is about 3.78 GiB.  Both core kernels are computed first; the output
 * arena is then allocated only to their rigorous aggregate dimension bound.
 * Always run --estimate before a large case.
 *
 * Compile:
 *   gcc -std=gnu11 -O3 -march=native -Wall -Wextra -Werror \
 *       -o spatial_crt_kernel_f2_parity_dense \
 *       spatial_crt_kernel_f2_parity_dense.c
 * Usage:
 *   ./spatial_crt_kernel_f2_parity_dense N Q [--estimate|--force]
 */

#include <errno.h>
#include <immintrin.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t u64;
typedef int64_t i64;
typedef __int128 i128;

#define SAFETY_RESERVE_BYTES (UINT64_C(512) << 20)

typedef struct {
    int d;
    int words;
    int capacity;
    int rank;
    u64 *rows;
    int *pivots;
    int *pivot_to_row;
} Echelon;

typedef struct {
    int q;
    int count;
    int *units;
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
        die("internal modular inverse failure");
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

static int buffered_radius(int n_level, int multiplier, int q,
                           int q_total) {
    i128 target = (i128)multiplier * multiplier * n_level;
    i128 q_squared = (i128)q * q;
    int low = 0;
    int high = q_total / q + (q_total % q != 0);
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
    for (int d = 1; d <= n / d; d++)
        if (n % d == 0)
            count += d == n / d ? 1 : 2;
    int *result = xmalloc((size_t)count * sizeof(int));
    int at = 0;
    for (int d = 1; d <= n / d; d++) {
        if (n % d != 0)
            continue;
        result[at++] = d;
        if (d != n / d)
            result[at++] = n / d;
    }
    qsort(result, (size_t)count, sizeof(int), compare_ints);
    *count_out = count;
    return result;
}

static uint64_t available_memory_bytes(void) {
    FILE *file = fopen("/proc/meminfo", "r");
    if (!file)
        return 0;
    char label[64];
    char unit[32];
    unsigned long long kib = 0;
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

static inline void xor_words_from(u64 *restrict destination,
                                  const u64 *restrict source,
                                  int first_word, int words) {
    int word = first_word;
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

static inline void xor_words(u64 *restrict destination,
                             const u64 *restrict source, int words) {
    xor_words_from(destination, source, 0, words);
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

static inline int row_dot_from(const u64 *left, const u64 *right,
                               int first_word, int words) {
    unsigned int parity = 0;
    for (int word = first_word; word < words; word++)
        parity ^= (unsigned int)__builtin_parityll(left[word] & right[word]);
    return (int)(parity & 1U);
}

static Echelon echelon_create_capacity(int d, int capacity) {
    if (capacity < 0 || capacity > d)
        die("invalid echelon row capacity");
    Echelon result;
    result.d = d;
    result.words = (d + 63) / 64;
    result.capacity = capacity;
    result.rank = 0;
    result.rows = xcalloc((size_t)capacity * result.words, sizeof(u64));
    result.pivots = xmalloc((size_t)capacity * sizeof(int));
    result.pivot_to_row = xmalloc((size_t)d * sizeof(int));
    for (int column = 0; column < d; column++)
        result.pivot_to_row[column] = -1;
    return result;
}

static Echelon echelon_create(int d) {
    return echelon_create_capacity(d, d);
}

static void echelon_destroy(Echelon *basis) {
    free(basis->rows);
    free(basis->pivots);
    free(basis->pivot_to_row);
    memset(basis, 0, sizeof(*basis));
}

static int echelon_insert(Echelon *basis, u64 *work) {
    int start = 0;
    for (;;) {
        int pivot = first_bit_from(work, start, basis->words, basis->d);
        if (pivot < 0)
            return 0;
        int row_index = basis->pivot_to_row[pivot];
        if (row_index < 0) {
            if (basis->rank >= basis->capacity)
                die("echelon row capacity exhausted");
            u64 *destination =
                basis->rows + (size_t)basis->rank * basis->words;
            memcpy(destination, work, (size_t)basis->words * sizeof(u64));
            basis->pivots[basis->rank] = pivot;
            basis->pivot_to_row[pivot] = basis->rank;
            basis->rank++;
            return 1;
        }
        const u64 *source =
            basis->rows + (size_t)row_index * basis->words;
        xor_words_from(work, source, pivot >> 6, basis->words);
        start = pivot + 1;
    }
}

/* Return column-major nullspace basis: nullity consecutive d-bit vectors. */
static u64 *echelon_kernel(const Echelon *basis, int *nullity_out) {
    int nullity = basis->d - basis->rank;
    u64 *kernel = xcalloc((size_t)nullity * basis->words, sizeof(u64));
    int free_index = 0;
    for (int free_column = 0; free_column < basis->d; free_column++) {
        if (basis->pivot_to_row[free_column] >= 0)
            continue;
        u64 *vector = kernel + (size_t)free_index * basis->words;
        vector[free_column >> 6] |=
            UINT64_C(1) << (free_column & 63);
        for (int pivot = basis->d - 1; pivot >= 0; pivot--) {
            int row_index = basis->pivot_to_row[pivot];
            if (row_index < 0)
                continue;
            const u64 *row =
                basis->rows + (size_t)row_index * basis->words;
            if (row_dot_from(row, vector, pivot >> 6, basis->words))
                vector[pivot >> 6] |= UINT64_C(1) << (pivot & 63);
        }
        free_index++;
    }
    if (free_index != nullity)
        die("internal nullity enumeration mismatch");
    *nullity_out = nullity;
    return kernel;
}

static int selected_v_parity(int residue_parity, int step) {
    return residue_parity ^ (step & 1);
}

static i64 first_with_parity(i64 lower, int parity) {
    if ((lower & 1) != parity)
        lower++;
    return lower;
}

static void legal_interval(int n_level, int residue, int h,
                           i64 *lower, i64 *upper) {
    *lower = ceil_div(1 - (i64)h - residue, n_level);
    *upper = floor_div((i64)h - 2 - residue, n_level);
}

static void core_interval(int n_level, int residue_parity, int h,
                          i64 *lower, i64 *upper) {
    int last_residue = n_level - 1;
    if ((last_residue & 1) != residue_parity)
        last_residue--;
    i64 unused;
    legal_interval(n_level, residue_parity, h, lower, &unused);
    legal_interval(n_level, last_residue, h, &unused, upper);
}

static i64 count_selected(i64 lower, i64 upper, int parity) {
    i64 first = first_with_parity(lower, parity);
    return first > upper ? 0 : (upper - first) / 2 + 1;
}

static void build_row(u64 *row, int words, int d, int multiplier,
                      int residue_parity, const DivisorData *divisor,
                      i64 v) {
    memset(row, 0, (size_t)words * sizeof(u64));
    int step = multiplier / divisor->q;
    for (int index = 0; index < divisor->count; index++) {
        int t = positive_mod_i64(
            v + (i64)divisor->units[index] * step, multiplier);
        if (((t + residue_parity) & 1) != 0)
            die("internal compressed-row parity failure");
        int column = (t - residue_parity) / 2;
        if (column < 0 || column >= d)
            die("internal compressed column out of range");
        row[column >> 6] ^= UINT64_C(1) << (column & 63);
    }
}

static i64 build_core(Echelon *core, int n_level, int multiplier,
                      int residue_parity, const DivisorData *data,
                      int divisor_count, u64 *work) {
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
            build_row(work, core->words, core->d, multiplier,
                      residue_parity, &data[index], v);
            (void)echelon_insert(core, work);
            rows++;
            if (rows >= next_report) {
                fprintf(stderr,
                        "core parity=%d progress rows=%lld rank=%d/%d\n",
                        residue_parity, (long long)rows, core->rank, core->d);
                next_report += 50000;
            }
        }
    }
    return rows;
}

static int add_endpoint_signature(Echelon *constraints, const u64 *row,
                                  const u64 *core_kernel,
                                  int core_nullity, int physical_words,
                                  u64 *signature) {
    memset(signature, 0, (size_t)constraints->words * sizeof(u64));
    for (int index = 0; index < core_nullity; index++) {
        const u64 *vector =
            core_kernel + (size_t)index * physical_words;
        if (row_dot_from(row, vector, 0, physical_words))
            signature[index >> 6] |= UINT64_C(1) << (index & 63);
    }
    return echelon_insert(constraints, signature);
}

static int impose_sector_endpoints(Echelon *constraints, int n_level,
                                   int multiplier, int residue,
                                   const DivisorData *data,
                                   int divisor_count,
                                   const u64 *core_kernel,
                                   int core_nullity, u64 *physical_work,
                                   u64 *signature_work) {
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
            build_row(physical_work, (multiplier / 2 + 63) / 64,
                      multiplier / 2, multiplier, residue_parity,
                      &data[index], v);
            (void)add_endpoint_signature(
                constraints, physical_work, core_kernel, core_nullity,
                (multiplier / 2 + 63) / 64, signature_work);
            rows++;
        }
        i64 right_lower = core_upper + 1;
        if (right_lower < lower)
            right_lower = lower;
        for (i64 v = first_with_parity(right_lower, parity);
             v <= upper; v += 2) {
            build_row(physical_work, (multiplier / 2 + 63) / 64,
                      multiplier / 2, multiplier, residue_parity,
                      &data[index], v);
            (void)add_endpoint_signature(
                constraints, physical_work, core_kernel, core_nullity,
                (multiplier / 2 + 63) / 64, signature_work);
            rows++;
        }
    }
    return rows;
}

static void translate_vector(const u64 *source, u64 *destination, int d,
                             int words, int shift) {
    memset(destination, 0, (size_t)words * sizeof(u64));
    for (int word = 0; word < words; word++) {
        u64 remaining = source[word];
        while (remaining != 0) {
            int bit = __builtin_ctzll(remaining);
            int column = 64 * word + bit;
            if (column < d) {
                int translated = column + shift;
                if (translated >= d)
                    translated -= d;
                destination[translated >> 6] ^=
                    UINT64_C(1) << (translated & 63);
            }
            remaining &= remaining - 1;
        }
    }
}

static int process_sector(Echelon *output, int n_level, int multiplier,
                          int residue, const DivisorData *data,
                          int divisor_count, const u64 *core_kernel,
                          int core_nullity, int inverse_n,
                          u64 *physical_work, u64 *translated_work,
                          u64 *signature_work, int *endpoint_rows_out,
                          int *output_gain_out) {
    Echelon constraints =
        echelon_create_capacity(core_nullity, core_nullity);
    int endpoints = impose_sector_endpoints(
        &constraints, n_level, multiplier, residue, data, divisor_count,
        core_kernel, core_nullity, physical_work, signature_work);
    int sector_nullity = 0;
    u64 *coefficient_kernel =
        echelon_kernel(&constraints, &sector_nullity);
    int old_rank = output->rank;
    for (int vector_index = 0; vector_index < sector_nullity;
         vector_index++) {
        memset(physical_work, 0, (size_t)output->words * sizeof(u64));
        const u64 *coefficients = coefficient_kernel +
            (size_t)vector_index * constraints.words;
        for (int word = 0; word < constraints.words; word++) {
            u64 remaining = coefficients[word];
            while (remaining != 0) {
                int bit = __builtin_ctzll(remaining);
                int core_index = 64 * word + bit;
                if (core_index < core_nullity)
                    xor_words(physical_work,
                              core_kernel +
                                  (size_t)core_index * output->words,
                              output->words);
                remaining &= remaining - 1;
            }
        }
        i64 numerator = (i64)(residue & 1) + (i64)inverse_n * residue;
        if (numerator & 1)
            die("internal nonintegral output half-shift");
        int shift = positive_mod_i64(numerator / 2, output->d);
        translate_vector(physical_work, translated_work, output->d,
                         output->words, shift);
        (void)echelon_insert(output, translated_work);
    }
    free(coefficient_kernel);
    echelon_destroy(&constraints);
    *endpoint_rows_out = endpoints;
    *output_gain_out = output->rank - old_rank;
    return sector_nullity;
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
        else
            die("unknown option");
    }
    int n_level = parse_positive_int(argv[1], "N");
    int q_total = parse_positive_int(argv[2], "Q");
    if (!is_odd_prime(n_level))
        die("require odd prime N");
    if (q_total % n_level != 0)
        die("require N|Q");
    int multiplier = q_total / n_level;
    if (gcd_int(n_level, multiplier) != 1 || (multiplier & 1))
        die("require even M=Q/N coprime to N");
    int d = multiplier / 2;
    int words = (d + 63) / 64;

    int divisor_count = 0;
    int *divisors = make_divisors(multiplier, &divisor_count);
    DivisorData *data = xcalloc((size_t)divisor_count, sizeof(*data));
    i64 full_rows = 0;
    for (int index = 0; index < divisor_count; index++) {
        int q = divisors[index];
        data[index].q = q;
        data[index].units = xmalloc((size_t)q * sizeof(int));
        for (int a = 0; a < q; a++)
            if (gcd_int(a, q) == 1)
                data[index].units[data[index].count++] = a;
        data[index].h = buffered_radius(n_level, multiplier, q, q_total);
        full_rows += 2 * (i64)data[index].h - 2;
    }

    uint64_t dense_bytes =
        (uint64_t)d * (uint64_t)words * sizeof(u64);
    uint64_t staged_bytes = dense_bytes + SAFETY_RESERVE_BYTES +
        (uint64_t)64 * d * sizeof(int);
    uint64_t available = available_memory_bytes();
    i64 equation_margin = full_rows + multiplier - (i64)q_total;
    printf("N=%d M=%d Q=%d parity_columns=%d full_coprime_rows=%lld "
           "equation_margin_after_W=%lld\n",
           n_level, multiplier, q_total, d, (long long)full_rows,
           (long long)equation_margin);
    printf("MEMORY one_dense_basis=%llu_bytes=%.3f_GiB "
           "staged_core_plus_reserve=%.3f_GiB MemAvailable=%.3f_GiB\n",
           (unsigned long long)dense_bytes,
           (double)dense_bytes / (double)(UINT64_C(1) << 30),
           (double)staged_bytes / (double)(UINT64_C(1) << 30),
           (double)available / (double)(UINT64_C(1) << 30));
    if (equation_margin < 0) {
        printf("DIMENSION_OBSTRUCTION shortfall=%lld\n",
               (long long)-equation_margin);
        estimate_only = 1;
    }
    if (estimate_only)
        goto cleanup;
    guard_additional_allocation(dense_bytes, force, "dense core");

    int inverse_n = inverse_mod(n_level % multiplier, multiplier);
    u64 *physical_work = xcalloc((size_t)words, sizeof(u64));
    u64 *translated_work = xcalloc((size_t)words, sizeof(u64));
    u64 *signature_work = xcalloc((size_t)words, sizeof(u64));
    u64 *core_kernels[2] = {NULL, NULL};
    int core_nullities[2] = {0, 0};
    i64 total_even_rows = 0;
    i64 total_even_kernel = 0;

    for (int residue_parity = 0; residue_parity <= 1;
         residue_parity++) {
        guard_additional_allocation(dense_bytes, force, "dense core");
        Echelon core = echelon_create(d);
        i64 core_rows = build_core(&core, n_level, multiplier,
                                   residue_parity, data, divisor_count,
                                   physical_work);
        int core_nullity = d - core.rank;
        uint64_t kernel_bytes =
            (uint64_t)core_nullity * words * sizeof(u64);
        guard_additional_allocation(kernel_bytes, force,
                                    "common-core kernel");
        u64 *core_kernel =
            echelon_kernel(&core, &core_nullities[residue_parity]);
        if (core_nullities[residue_parity] != core_nullity)
            die("internal common-core nullity mismatch");
        core_kernels[residue_parity] = core_kernel;
        printf("core parity=%d rows=%lld rank=%d/%d nullity=%d "
               "kernel_storage=%zu_bytes\n",
               residue_parity, (long long)core_rows, core.rank, d,
               core_nullity,
               (size_t)core_nullity * words * sizeof(u64));
        echelon_destroy(&core);
    }

    i64 output_capacity_i64 =
        (i64)((n_level + 1) / 2) * core_nullities[0] +
        (i64)((n_level - 1) / 2) * core_nullities[1];
    if (output_capacity_i64 > d)
        output_capacity_i64 = d;
    int output_capacity = (int)output_capacity_i64;
    uint64_t output_bytes =
        (uint64_t)output_capacity * words * sizeof(u64);
    int maximum_core_nullity = core_nullities[0] > core_nullities[1]
                                   ? core_nullities[0]
                                   : core_nullities[1];
    int maximum_constraint_words = (maximum_core_nullity + 63) / 64;
    uint64_t small_elimination_bytes =
        2 * (uint64_t)maximum_core_nullity *
        (uint64_t)maximum_constraint_words * sizeof(u64);
    /* calloc may leave the output pages uncommitted until later insertions,
     * so the guard must reserve output and the simultaneous small
     * constraint/nullspace pair additively in one check. */
    guard_additional_allocation(output_bytes + small_elimination_bytes,
                                force,
                                "output plus sector elimination storage");
    Echelon output = echelon_create_capacity(d, output_capacity);
    printf("OUTPUT capacity=%d/%d allocation=%llu_bytes=%.3f_GiB\n",
           output_capacity, d, (unsigned long long)output_bytes,
           (double)output_bytes / (double)(UINT64_C(1) << 30));

    for (int residue_parity = 0; residue_parity <= 1;
         residue_parity++) {
        const u64 *core_kernel = core_kernels[residue_parity];
        int core_nullity = core_nullities[residue_parity];
        for (int residue = residue_parity; residue < n_level; residue += 2) {
            int endpoints = 0;
            int output_gain = 0;
            int kernel_dimension = process_sector(
                &output, n_level, multiplier, residue, data, divisor_count,
                core_kernel, core_nullity, inverse_n, physical_work,
                translated_work, signature_work, &endpoints, &output_gain);
            total_even_kernel += kernel_dimension;
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
            i64 numerator = (i64)(residue & 1) +
                            (i64)inverse_n * residue;
            int shift = positive_mod_i64(numerator / 2, d);
            printf("sector r=%d even_rows=%lld endpoints=%d kernel_dim=%d "
                   "output_shift=%d W_gain=%d W_rank=%d/%d\n",
                   residue, (long long)sector_rows, endpoints,
                   kernel_dimension, shift, output_gain, output.rank, d);
        }
        free(core_kernels[residue_parity]);
    }

    if (2 * total_even_rows != full_rows)
        die("internal parity row-count mismatch");
    i64 full_kernel = 2 * total_even_kernel;
    i64 full_gain = 2 * (i64)output.rank;
    i64 defect = full_kernel - full_gain;
    printf("TOTAL full_coprime_rank=%lld/%d full_coprime_kernel_dim=%lld "
           "W_gain=%lld/%lld final_defect=%lld assisted_rank=%lld/%d "
           "output_rows_storage=%zu_bytes\n",
           (long long)((i64)q_total - full_kernel), q_total,
           (long long)full_kernel, (long long)full_gain,
           (long long)full_kernel, (long long)defect,
           (long long)((i64)q_total - defect), q_total,
           (size_t)output.rank * output.words * sizeof(u64));
    echelon_destroy(&output);
    free(physical_work);
    free(translated_work);
    free(signature_work);

cleanup:
    for (int index = 0; index < divisor_count; index++)
        free(data[index].units);
    free(data);
    free(divisors);
    return EXIT_SUCCESS;
}
