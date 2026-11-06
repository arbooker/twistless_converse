/* Exact projected Block-Wiedemann finisher with a 64-bit total modulus Q.
 *
 * The audited finisher stores compressed coordinates modulo M/2 in 32-bit
 * integers, which is sufficient for N=97, M=61,261,200.  Its historical
 * command-line entry point nevertheless parsed Q=NM as an int.  This
 * non-overwriting wrapper retains every rank and verification routine from
 * spatial_crt_kernel_f2_bw_finish_minor.c, replacing only the command-line
 * and buffered-radius setup so Q may exceed INT_MAX.
 */

#define SPATIAL_CRT_KERNEL_F2_BW_FINISH_MINOR_LIBRARY
#include "spatial_crt_kernel_f2_bw_finish_minor.c"
#undef SPATIAL_CRT_KERNEL_F2_BW_FINISH_MINOR_LIBRARY

static i64 largeq_parse_positive_i64(const char *text, const char *name) {
    char *end = NULL;
    errno = 0;
    long long value = strtoll(text, &end, 10);
    if (errno != 0 || end == text || *end != '\0' || value <= 0) {
        fprintf(stderr, "%s must be a positive signed 64-bit integer\n", name);
        exit(EXIT_FAILURE);
    }
    return (i64)value;
}

/* h=min{h>=0:h^2 q^2 >= M^2 N}, using exact 128-bit arithmetic. */
static int largeq_buffered_radius(int n_level, int multiplier, int q) {
    i128 target = (i128)multiplier * multiplier * n_level;
    i128 q_squared = (i128)q * q;
    i64 low = 0;
    i64 high = (i64)n_level * (multiplier / q);
    if (multiplier % q != 0)
        high += n_level;
    while (low < high) {
        i64 middle = low + (high - low) / 2;
        if ((i128)middle * middle * q_squared >= target)
            high = middle;
        else
            low = middle + 1;
    }
    if (low > INT_MAX)
        die("buffered radius does not fit the finisher's compressed format");
    return (int)low;
}

int main(int argc, char **argv) {
    int setup_only =
        argc == 4 && strcmp(argv[3], "--setup-only") == 0;
    if (!setup_only && argc < 8) {
        fprintf(stderr,
                "Usage: %s N Q CORE0.bin SEED OVERSAMPLE HASHES "
                "W1 [W2 ...]\n"
                "       %s N Q --setup-only\n",
                argv[0],
                argv[0]);
        return EXIT_FAILURE;
    }
    int n_level = parse_positive_int(argv[1], "N");
    i64 q_total = largeq_parse_positive_i64(argv[2], "Q");
    if (!is_odd_prime(n_level))
        die("require N to be an odd prime");
    if (q_total % n_level != 0)
        die("require N|Q");
    i64 multiplier_i64 = q_total / n_level;
    if (multiplier_i64 > INT_MAX)
        die("Q/N does not fit the finisher's compressed format");
    int multiplier = (int)multiplier_i64;
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
        if (!setup_only) {
            data[index].values = xmalloc((size_t)q * sizeof(int));
            for (int a = 0; a < q; a++)
                if (gcd_int(a, q) == 1)
                    data[index].values[data[index].count++] = a;
        }
        data[index].h = largeq_buffered_radius(n_level, multiplier, q);
        expected_full_rows += 2 * (i64)data[index].h - 2;
    }

    i64 equation_margin = expected_full_rows + multiplier - q_total;
    printf("N=%d M=%d Q=%lld global_parity_columns=%d divisors=%d "
           "full_coprime_rows=%lld equation_margin_after_W=%lld\n",
           n_level, multiplier, (long long)q_total, d, divisor_count,
           (long long)expected_full_rows, (long long)equation_margin);
    if (equation_margin < 0)
        die("dimension obstruction: coprime rows plus W cannot span");
    if (setup_only) {
        free(data);
        free(divisors);
        printf("LARGE_Q_SETUP_PASS\n");
        return EXIT_SUCCESS;
    }

    u64 minor_seed = minor_parse_u64(argv[4], "SEED");
    int oversample = parse_positive_int(argv[5], "OVERSAMPLE");
    int hash_count = parse_positive_int(argv[6], "HASHES");

    size_t solution_count = (size_t)argc - 7;
    BwKernel kernel =
        bw_load_clean_kernel(argv[3], argv + 7, solution_count, d);
    printf("BW_COMPLETENESS supplied cleaned kernel is assumed complete; "
           "row annihilation is checked exactly, while a new case still "
           "requires a separate rank certificate\n");

    i64 common_rows[2];
    common_rows[0] =
        bw_common_core_row_count(n_level, multiplier, 0, data, divisor_count);
    common_rows[1] =
        bw_common_core_row_count(n_level, multiplier, 1, data, divisor_count);
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
        &reflection_exceptions, &reflection_gain, &reflection_exception_nnz);
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

    int *sector_dimensions = xcalloc((size_t)n_level,
                                     sizeof(*sector_dimensions));
    int *sector_shifts = xcalloc((size_t)n_level, sizeof(*sector_shifts));
    i64 total_even_rows = 0;
    i64 total_even_kernel = 0;
    size_t peak_sector_bytes = 0;

    /* First pass: obtain the exact row count r of the top-up image matrix. */
    for (int residue_parity = 0; residue_parity <= 1; residue_parity++) {
        const Snapshot *snapshot = &snapshots[residue_parity];
        for (int residue = residue_parity; residue < n_level; residue += 2) {
            int exceptions = count_sector_exceptions(
                n_level, multiplier, residue, data, divisor_count);
            Crref sector = crref_from_snapshot(snapshot, exceptions);
            int added_rows = add_sector_exceptions(
                &sector, n_level, multiplier, residue, data, divisor_count);
            if (added_rows != exceptions)
                die("internal endpoint-row count mismatch");
            sector_dimensions[residue] = sector.frozen;
            i64 numerator =
                (i64)(residue & 1) + (i64)inverse_n * residue;
            if (numerator & 1)
                die("internal half-shift is not integral");
            sector_shifts[residue] = positive_mod_i64(numerator / 2, d);
            total_even_kernel += sector.frozen;
            total_even_rows += minor_sector_row_count(
                n_level, multiplier, residue, residue_parity, data,
                divisor_count);
            if (sector.peak_used_bytes > peak_sector_bytes)
                peak_sector_bytes = sector.peak_used_bytes;
            crref_destroy(&sector);
        }
    }
    if (2 * total_even_rows != expected_full_rows)
        die("internal parity row-count mismatch");

    i64 full_kernel_dimension = 2 * total_even_kernel;
    i64 full_coprime_rank = q_total - full_kernel_dimension;
    printf("PROJECTION_PASS1 even_kernel_rows=%lld full_coprime_rank=%lld/%lld "
           "full_coprime_kernel_dim=%lld peak_sector=%zu\n",
           (long long)total_even_kernel, (long long)full_coprime_rank,
           (long long)q_total, (long long)full_kernel_dimension,
           peak_sector_bytes);

    if (total_even_kernel == 0) {
        printf("PROJECTION_CERTIFIED trivial_empty_kernel=1 final_defect=0 "
               "assisted_rank=%lld/%lld\n",
               (long long)q_total, (long long)q_total);
        for (int parity = 0; parity < 2; parity++)
            snapshot_destroy(&snapshots[parity]);
        free(sector_shifts);
        free(sector_dimensions);
        for (int index = 0; index < divisor_count; index++)
            free(data[index].values);
        free(data);
        free(divisors);
        return EXIT_SUCCESS;
    }
    if (total_even_kernel > d)
        die("top-up domain exceeds its ambient dimension; full rank impossible");

    if (total_even_kernel > (i64)INT_MAX / oversample)
        die("projection bucket-count overflow");
    i64 requested_buckets = total_even_kernel * (i64)oversample;
    int row_count = (int)total_even_kernel;
    int bucket_count = (int)requested_buckets;

    int projection_words = (bucket_count + 63) / 64;
    uint64_t projection_bytes =
        (uint64_t)row_count * (uint64_t)projection_words * sizeof(u64) +
        (uint64_t)row_count * sizeof(int) +
        (uint64_t)bucket_count * sizeof(int) +
        (uint64_t)projection_words * sizeof(u64) +
        (uint64_t)d * sizeof(int);
    guard_additional_allocation(
        projection_bytes + (uint64_t)peak_sector_bytes, 0,
        "compressed projection plus restored sector");
    DenseOutput output = dense_output_create(bucket_count, row_count);
    u64 *work = xcalloc((size_t)projection_words, sizeof(*work));
    printf("PROJECTION_SETUP seed=%" PRIu64 " oversample=%d hashes=%d "
           "buckets=%d source_columns=%d allocation=%llu_bytes=%.3f_GiB\n",
           minor_seed, oversample, hash_count, bucket_count, d,
           (unsigned long long)projection_bytes,
           (double)projection_bytes / (double)(UINT64_C(1) << 30));

    /* Second pass: build and eliminate the explicit sparse image R*P. */
    int inserted_rows = 0;
    for (int residue_parity = 0; residue_parity <= 1; residue_parity++) {
        const Snapshot *snapshot = &snapshots[residue_parity];
        for (int residue = residue_parity; residue < n_level; residue += 2) {
            int exceptions = count_sector_exceptions(
                n_level, multiplier, residue, data, divisor_count);
            Crref sector = crref_from_snapshot(snapshot, exceptions);
            int added_rows = add_sector_exceptions(
                &sector, n_level, multiplier, residue, data, divisor_count);
            if (added_rows != exceptions)
                die("internal endpoint-row count mismatch in projection pass");
            if (sector.frozen != sector_dimensions[residue])
                die("sector kernel dimension changed between passes");
            int old_rank = output.rank;
            for (int free_index = 0; free_index < sector.frozen; free_index++) {
                (void)minor_insert_kernel_row(
                    &output, work, &sector, free_index,
                    sector_shifts[residue], minor_seed, bucket_count,
                    hash_count, d);
                inserted_rows++;
            }
            printf("projection_sector r=%d kernel_dim=%d image_gain=%d "
                   "image_rank=%d/%d\n",
                   residue, sector.frozen, output.rank - old_rank,
                   output.rank, row_count);
            fflush(stdout);
            crref_destroy(&sector);
        }
        snapshot_destroy(&snapshots[residue_parity]);
    }
    if (inserted_rows != row_count)
        die("projection pass inserted the wrong number of rows");

    int certified = output.rank == row_count;
    i64 proved_full_w_gain = 2 * (i64)output.rank;
    i64 assisted_rank_lower = full_coprime_rank + proved_full_w_gain;
    if (certified) {
        printf("PROJECTION_CERTIFIED image_rank=%d/%d W_gain=%lld/%lld "
               "final_defect=0 assisted_rank=%lld/%lld\n",
               output.rank, row_count, (long long)proved_full_w_gain,
               (long long)full_kernel_dimension,
               (long long)q_total, (long long)q_total);
    } else {
        printf("PROJECTION_INCONCLUSIVE image_rank=%d/%d "
               "proved_W_gain_lower_bound=%lld "
               "assisted_rank_lower_bound=%lld/%lld "
               "retry_with_another_seed_more_buckets_or_more_hashes=1\n",
               output.rank, row_count, (long long)proved_full_w_gain,
               (long long)assisted_rank_lower, (long long)q_total);
    }

    free(work);
    dense_output_destroy(&output);
    free(sector_shifts);
    free(sector_dimensions);
    for (int index = 0; index < divisor_count; index++)
        free(data[index].values);
    free(data);
    free(divisors);
    return certified ? EXIT_SUCCESS : 2;
}
