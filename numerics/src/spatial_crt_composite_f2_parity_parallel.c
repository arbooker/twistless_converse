/* Exact composite-level large-prime CRT solver over F_2 with a parallel
 * P-divisible finisher.  Q need not be divisible by N.
 *
 * This is deliberately a new variant.  It includes the same audited prime
 * common-core engine used by spatial_crt_composite_f2_parity.c, while leaving
 * that serial reference implementation unchanged.
 *
 * For one batch of remaining rows, the global signature basis G is frozen.
 * Rows are generated and reduced modulo G independently in parallel.  Fixed
 * consecutive blocks are then echelonized independently in parallel, and
 * their bases are merged into G in fixed block/row order.  Therefore after
 * every batch G spans exactly its old space plus all rows in the batch.  The
 * result is an exact deterministic F_2 rank, not a probabilistic rank test.
 *
 * Compile:
 *   gcc -std=gnu11 -O3 -march=native -mbmi2 -fopenmp \
 *       -Wall -Wextra -Werror -o spatial_crt_composite_f2_parity_parallel \
 *       spatial_crt_composite_f2_parity_parallel.c
 * Usage:
 *   ./spatial_crt_composite_f2_parity_parallel N P Q [--estimate|--force]
 *
 * Required: P is an odd prime occurring to exact exponent one in both N
 * and Q, and Q is even.  No divisibility relation between N/P and Q/P is
 * required.  The full level N remains present in every buffered radius.
 * Every divisibility-minimal d|Q satisfying 2*H_d-2>=Q/d is retained;
 * blocks properly divisible by any such d are omitted using the exact
 * divisor-triangular complete-row redundancy.
 *
 * OMP_NUM_THREADS controls the worker count.  The batch has 16 rows per
 * worker, with a minimum of 512 and a maximum of 8192 rows.  Its only large
 * extra allocation is batch_rows*ceil(kernel_dimension/64)*8 bytes.
 */

#define main spatial_crt_prime_core_embedded_main
#include "spatial_crt_kernel_f2_parity_core.c"
#undef main

#include "spatial_row_pruning.h"

#define FINISH_LOCAL_BLOCK 16
#define FINISH_MIN_BATCH 512
#define FINISH_MAX_BATCH 8192

typedef struct {
    int count;
    int *values;
} CompositeUnits;

static i64 composite_gcd_i64(i64 a, i64 b) {
    while (b != 0) {
        i64 next = a % b;
        a = b;
        b = next;
    }
    return a < 0 ? -a : a;
}

static int composite_buffered_radius(int n_level, int q_total, int q) {
    i64 q_squared_i64 = (i64)q * q;
    i64 common = composite_gcd_i64(n_level, q_squared_i64);
    i128 conductor = (i128)(n_level / common) * q_squared_i64;
    i128 target = (i128)q_total * q_total;
    int low = 0;
    int high = q_total / q;
    while (low < high) {
        int middle = low + (high - low) / 2;
        if ((i128)middle * middle * conductor >= target)
            high = middle;
        else
            low = middle + 1;
    }
    return low;
}

typedef struct {
    int n_level;
    int q_total;
} CompositePruningContext;

static int composite_pruning_window(void *context, int q) {
    const CompositePruningContext *parameters = context;
    return composite_buffered_radius(
        parameters->n_level, parameters->q_total, q);
}

static void composite_destroy_units(CompositeUnits *units) {
    free(units->values);
    units->values = NULL;
    units->count = 0;
}

static i64 composite_sector_even_row_count(
    int prime, int sector_length, int residue, const DivisorData *data,
    int divisor_count) {
    int residue_parity = residue & 1;
    i64 rows = 0;
    for (int index = 0; index < divisor_count; index++) {
        int step = sector_length / data[index].q;
        int parity = selected_v_parity(residue_parity, step);
        i64 lower;
        i64 upper;
        legal_interval(prime, residue, data[index].h, &lower, &upper);
        rows += count_selected(lower, upper, parity);
    }
    return rows;
}

static int parallel_worker_limit(void) {
#if defined(_OPENMP)
    int workers = omp_get_max_threads();
    return workers > 0 ? workers : 1;
#else
    return 1;
#endif
}

static int parallel_batch_capacity(int workers) {
    i64 capacity = (i64)FINISH_LOCAL_BLOCK * workers;
    if (capacity < FINISH_MIN_BATCH)
        capacity = FINISH_MIN_BATCH;
    if (capacity > FINISH_MAX_BATCH)
        capacity = FINISH_MAX_BATCH;
    return (int)capacity;
}

/* This differs from composite_snapshot_toggle only in postponing the padding
 * mask until a complete row has been generated.  Source snapshots are shared
 * read-only by all workers. */
static void parallel_snapshot_toggle(const Snapshot *sector, int offset,
                                     int column, u64 *signature,
                                     int signature_words,
                                     int signature_dimension) {
    if (column < 0 || column >= sector->d)
        die("internal parallel sector column out of range");
    int free_index = sector->npidx_for_col[column];
    if (free_index >= 0) {
        int target = offset + free_index;
        if (target < 0 || target >= signature_dimension)
            die("internal parallel free coordinate out of range");
        signature[target >> 6] ^= UINT64_C(1) << (target & 63);
        return;
    }

    int row_index = sector->pivot_to_row[column];
    if (row_index < 0 || row_index >= sector->rank)
        die("internal parallel pivot row missing");
    const u64 *source =
        sector->arena + (size_t)row_index * sector->words;
    int output_word = offset >> 6;
    int output_shift = offset & 63;
    for (int word = 0; word < sector->words; word++) {
        u64 value = source[word];
        if (value == 0)
            continue;
        if (output_word + word < signature_words)
            signature[output_word + word] ^= value << output_shift;
        if (output_shift != 0 && output_word + word + 1 < signature_words)
            signature[output_word + word + 1] ^=
                value >> (64 - output_shift);
    }
}

/* Read-only reduction by the global echelon basis.  It is safe for all
 * workers to call this concurrently while a batch is being prepared. */
static int parallel_reduce_global(const DenseOutput *basis, u64 *work) {
    int start = 0;
    for (;;) {
        int pivot = first_bit_from(work, start, basis->words, basis->d);
        if (pivot < 0)
            return 0;
        int row_index = basis->pivot_to_row[pivot];
        if (row_index < 0)
            return 1;
        const u64 *source =
            basis->rows + (size_t)row_index * basis->words;
        xor_words(work + (pivot >> 6), source + (pivot >> 6),
                  basis->words - (pivot >> 6));
        start = pivot + 1;
    }
}

static int parallel_hash_get(const int *keys, const int *values, int mask,
                             int key) {
    unsigned int position =
        ((unsigned int)key * UINT32_C(2654435761)) & (unsigned int)mask;
    while (keys[position] >= 0) {
        if (keys[position] == key)
            return values[position];
        position = (position + 1U) & (unsigned int)mask;
    }
    return -1;
}

static void parallel_hash_put(int *keys, int *values, int mask, int key,
                              int value) {
    unsigned int position =
        ((unsigned int)key * UINT32_C(2654435761)) & (unsigned int)mask;
    while (keys[position] >= 0)
        position = (position + 1U) & (unsigned int)mask;
    keys[position] = key;
    values[position] = value;
}

/* In-place echelon insertion into one fixed block.  The sparse hash contains
 * at most FINISH_LOCAL_BLOCK pivots, avoiding an O(threads*d) pivot table. */
static int parallel_local_insert(u64 *batch_rows, int words, int d,
                                 int row_slot, int *keys, int *values,
                                 int hash_mask) {
    u64 *work = batch_rows + (size_t)row_slot * words;
    int start = 0;
    for (;;) {
        int pivot = first_bit_from(work, start, words, d);
        if (pivot < 0)
            return 0;
        int basis_slot =
            parallel_hash_get(keys, values, hash_mask, pivot);
        if (basis_slot < 0) {
            parallel_hash_put(keys, values, hash_mask, pivot, row_slot);
            return 1;
        }
        const u64 *source =
            batch_rows + (size_t)basis_slot * words;
        xor_words(work + (pivot >> 6), source + (pivot >> 6),
                  words - (pivot >> 6));
        start = pivot + 1;
    }
}

/* Deterministic ascending unit list.  Large q uses fixed logical chunks in
 * two parallel passes; it uses no q-byte flag array and hence has the same
 * principal allocation as the serial constructor. */
static CompositeUnits parallel_make_units(int q, int force, int workers) {
    int logical_workers = workers;
    if (logical_workers > q)
        logical_workers = q;
    uint64_t allocation_bytes = (uint64_t)q * sizeof(int);
    if (workers > 1 && q >= 100000) {
        uint64_t auxiliary_bytes =
            (uint64_t)logical_workers * 2 * sizeof(int);
        if (UINT64_MAX - allocation_bytes < auxiliary_bytes)
            die("parallel unit-list allocation-size overflow");
        allocation_bytes += auxiliary_bytes;
    }
    guard_additional_allocation(allocation_bytes, force,
                                "temporary parallel unit-residue list");
    CompositeUnits result;
    result.count = 0;
    result.values = xmalloc((size_t)q * sizeof(int));
    if (workers <= 1 || q < 100000) {
        for (int a = 0; a < q; a++)
            if (gcd_int(a, q) == 1)
                result.values[result.count++] = a;
        return result;
    }

    int *counts = xcalloc((size_t)logical_workers, sizeof(*counts));
    int *offsets = xcalloc((size_t)logical_workers, sizeof(*offsets));
#if defined(_OPENMP)
#pragma omp parallel for schedule(static)
#endif
    for (int worker = 0; worker < logical_workers; worker++) {
        int begin = (int)((i64)q * worker / logical_workers);
        int end = (int)((i64)q * (worker + 1) / logical_workers);
        int count = 0;
        for (int a = begin; a < end; a++)
            if (gcd_int(a, q) == 1)
                count++;
        counts[worker] = count;
    }
    for (int worker = 0; worker < logical_workers; worker++) {
        offsets[worker] = result.count;
        result.count += counts[worker];
    }
#if defined(_OPENMP)
#pragma omp parallel for schedule(static)
#endif
    for (int worker = 0; worker < logical_workers; worker++) {
        int begin = (int)((i64)q * worker / logical_workers);
        int end = (int)((i64)q * (worker + 1) / logical_workers);
        int output = offsets[worker];
        for (int a = begin; a < end; a++)
            if (gcd_int(a, q) == 1)
                result.values[output++] = a;
        if (output != offsets[worker] + counts[worker])
            die("internal parallel unit count mismatch");
    }
    free(offsets);
    free(counts);
    return result;
}

int main(int argc, char **argv) {
    if (argc < 4 || argc > 5) {
        fprintf(stderr,
                "Usage: %s N P Q [--estimate|--force]\n", argv[0]);
        return EXIT_FAILURE;
    }
    int estimate_only = 0;
    int force = 0;
    if (argc == 5) {
        if (strcmp(argv[4], "--estimate") == 0)
            estimate_only = 1;
        else if (strcmp(argv[4], "--force") == 0)
            force = 1;
        else {
            fprintf(stderr, "unknown option: %s\n", argv[4]);
            return EXIT_FAILURE;
        }
    }

    int n_level = parse_positive_int(argv[1], "N");
    int prime = parse_positive_int(argv[2], "P");
    int q_total = parse_positive_int(argv[3], "Q");
    if (!is_odd_prime(prime))
        die("require P to be an odd prime");
    if (n_level % prime != 0)
        die("require P|N");
    int s = n_level / prime;
    if (gcd_int(prime, s) != 1)
        die("require P not to divide N/P");
    if (q_total % prime != 0)
        die("require P|Q");
    if ((q_total & 1) != 0)
        die("require even Q for the parity/reflection reduction");
    int sector_length = q_total / prime;
    if (gcd_int(prime, sector_length) != 1)
        die("require gcd(P,Q/P)=1");
    if ((sector_length & 1) != 0)
        die("internal error: odd P and even Q did not make Q/P even");
    int parity_columns = sector_length / 2;
    int workers = parallel_worker_limit();
    int batch_capacity = parallel_batch_capacity(workers);
    CompositePruningContext pruning_context = {n_level, q_total};
    SpatialRowPruning pruning;
    spatial_row_pruning_init(
        &pruning, q_total, composite_pruning_window, &pruning_context);

    int all_divisor_count = 0;
    int *all_divisors = make_divisors(q_total, &all_divisor_count);
    i64 expected_all_rows = 0;
    i64 expected_remaining_even_rows = 0;
    uint64_t maximum_remaining_unit_bytes = 0;
    for (int index = 0; index < all_divisor_count; index++) {
        int q = all_divisors[index];
        if (!spatial_row_pruning_is_selected(&pruning, q))
            continue;
        int h = composite_buffered_radius(n_level, q_total, q);
        expected_all_rows += 2 * (i64)h - 2;
        if (q % prime == 0) {
            expected_remaining_even_rows += h - 1;
            if (h >= 2) {
                int logical_workers = workers < q ? workers : q;
                uint64_t bytes = (uint64_t)q * sizeof(int);
                if (workers > 1 && q >= 100000)
                    bytes += (uint64_t)logical_workers * 2 *
                             sizeof(int);
                if (bytes > maximum_remaining_unit_bytes)
                    maximum_remaining_unit_bytes = bytes;
            }
        }
    }

    int raw_pfree_count = 0;
    int *pfree_divisors = make_divisors(sector_length, &raw_pfree_count);
    DivisorData *data =
        xcalloc((size_t)raw_pfree_count, sizeof(*data));
    int divisor_count = 0;
    i64 expected_pfree_rows = 0;
    uint64_t pfree_unit_bytes = 0;
    for (int index = 0; index < raw_pfree_count; index++) {
        int q = pfree_divisors[index];
        if (!spatial_row_pruning_is_selected(&pruning, q))
            continue;
        int h = composite_buffered_radius(n_level, q_total, q);
        expected_pfree_rows += 2 * (i64)h - 2;
        if (h < 2)
            continue;
        if (UINT64_MAX - pfree_unit_bytes < (uint64_t)q * sizeof(int))
            die("P-free unit-list size overflow");
        pfree_unit_bytes += (uint64_t)q * sizeof(int);
        data[divisor_count].q = q;
        data[divisor_count].h = h;
        divisor_count++;
    }

    size_t arena_u64 = compressed_arena_u64(parity_columns);
    uint64_t one_arena_bytes = (uint64_t)arena_u64 * sizeof(u64);
    uint64_t core_stage_bytes =
        one_arena_bytes + crref_auxiliary_bytes(parity_columns);
    uint64_t worst_kernel = (uint64_t)q_total / 2;
    uint64_t worst_signature_bytes =
        worst_kernel * ((worst_kernel + 63) / 64) * sizeof(u64);
    uint64_t worst_batch_bytes =
        (uint64_t)batch_capacity * ((worst_kernel + 63) / 64) *
        sizeof(u64);
    i64 equation_margin = expected_all_rows - q_total;
    printf("N=%d P=%d N_over_P=%d Q_over_P=%d Q=%d "
           "parity_columns_per_sector=%d "
           "P_free_divisors=%d/%d all_divisors=%d workers=%d "
           "finish_batch=%d\n",
           n_level, prime, s, sector_length, q_total,
           parity_columns, divisor_count, raw_pfree_count,
           all_divisor_count, workers, batch_capacity);
    printf("ROWS all=%lld P_free=%lld P_divisible_even=%lld "
           "equation_margin=%lld\n",
           (long long)expected_all_rows, (long long)expected_pfree_rows,
           (long long)expected_remaining_even_rows,
           (long long)equation_margin);
    spatial_row_pruning_print(stdout, &pruning);
    putchar('\n');
    printf("MEMORY P_free_units=%.3f_GiB one_compressed_core=%.3f_GiB "
           "worst_case_signature_basis=%.3f_GiB "
           "worst_case_parallel_batch=%.3f_GiB MemAvailable=%.3f_GiB\n",
           (double)pfree_unit_bytes / (double)(UINT64_C(1) << 30),
           (double)one_arena_bytes / (double)(UINT64_C(1) << 30),
           (double)worst_signature_bytes / (double)(UINT64_C(1) << 30),
           (double)worst_batch_bytes / (double)(UINT64_C(1) << 30),
           (double)available_memory_bytes() /
               (double)(UINT64_C(1) << 30));
    if (equation_margin < 0) {
        printf("DIMENSION_OBSTRUCTION shortfall=%lld; no elimination run\n",
               (long long)-equation_margin);
        estimate_only = 1;
    }
    if (estimate_only)
        goto cleanup_unbuilt;

    guard_additional_allocation(pfree_unit_bytes, force,
                                "P-free unit-residue lists");
    for (int index = 0; index < divisor_count; index++) {
        int q = data[index].q;
        data[index].values = xmalloc((size_t)q * sizeof(int));
        for (int a = 0; a < q; a++)
            if (gcd_int(a, q) == 1)
                data[index].values[data[index].count++] = a;
    }

    Snapshot common[2];
    memset(common, 0, sizeof(common));
    for (int residue_parity = 0; residue_parity <= 1;
         residue_parity++) {
        guard_additional_allocation(core_stage_bytes, force,
                                    "compressed P-free common core");
        Crref core = crref_create(parity_columns, arena_u64);
        i64 rows = build_common_core(&core, prime, sector_length,
                                     residue_parity, data,
                                     divisor_count);
        uint64_t bytes = snapshot_storage_bytes(
            parity_columns, core.rank, core.frozen);
        guard_additional_allocation(bytes, force,
                                    "P-free common-core snapshot");
        common[residue_parity] = snapshot_from_crref(&core);
        printf("CORE parity=%d rows=%lld rank=%d/%d nullity=%d "
               "snapshot=%.3f_GiB\n",
               residue_parity, (long long)rows, core.rank,
               parity_columns, core.frozen,
               (double)bytes / (double)(UINT64_C(1) << 30));
        fflush(stdout);
        crref_destroy(&core);
    }

    uint64_t sector_metadata_bytes =
        (uint64_t)prime * (sizeof(Snapshot) + sizeof(int));
    guard_additional_allocation(sector_metadata_bytes, force,
                                "sector metadata");
    Snapshot *sectors = xcalloc((size_t)prime, sizeof(*sectors));
    int *kernel_offsets =
        xcalloc((size_t)prime, sizeof(*kernel_offsets));
    i64 total_pfree_rows_check = 0;
    i64 kernel_dimension_i64 = 0;
    uint64_t sector_snapshot_bytes = 0;
    for (int residue_parity = 0; residue_parity <= 1;
         residue_parity++) {
        for (int residue = residue_parity; residue < prime;
             residue += 2) {
            int exceptions = count_sector_exceptions(
                prime, sector_length, residue, data, divisor_count);
            size_t sector_arena_u64 = restored_sector_arena_u64(
                &common[residue_parity], exceptions);
            if (sector_arena_u64 > UINT64_MAX / sizeof(u64))
                die("restored sector allocation-size overflow");
            uint64_t sector_work_bytes =
                (uint64_t)sector_arena_u64 * sizeof(u64) +
                crref_auxiliary_bytes(parity_columns);
            guard_additional_allocation(
                sector_work_bytes, force,
                "restored P-free sector workspace");
            Crref sector = crref_from_snapshot(
                &common[residue_parity], exceptions);
            int added = add_sector_exceptions(
                &sector, prime, sector_length, residue, data,
                divisor_count);
            if (added != exceptions)
                die("internal composite endpoint-row count mismatch");
            i64 sector_rows = composite_sector_even_row_count(
                prime, sector_length, residue, data, divisor_count);
            total_pfree_rows_check += sector_rows;
            if (kernel_dimension_i64 > INT_MAX)
                die("composite kernel dimension exceeds int range");
            kernel_offsets[residue] = (int)kernel_dimension_i64;
            kernel_dimension_i64 += sector.frozen;
            if (kernel_dimension_i64 > INT_MAX)
                die("composite kernel dimension exceeds int range");
            uint64_t bytes = snapshot_storage_bytes(
                parity_columns, sector.rank, sector.frozen);
            guard_additional_allocation(bytes, force,
                                        "final sector-kernel snapshot");
            sectors[residue] = snapshot_from_crref(&sector);
            sector_snapshot_bytes += bytes;
            printf("SECTOR r=%d rows=%lld endpoints=%d rank=%d/%d "
                   "kernel=%d offset=%d snapshot=%.3f_MiB\n",
                   residue, (long long)sector_rows, exceptions,
                   sector.rank, parity_columns, sector.frozen,
                   kernel_offsets[residue],
                   (double)bytes / (double)(UINT64_C(1) << 20));
            fflush(stdout);
            crref_destroy(&sector);
        }
        snapshot_destroy(&common[residue_parity]);
    }
    if (2 * total_pfree_rows_check != expected_pfree_rows)
        die("internal composite CRT sectors do not partition P-free rows");
    for (int index = 0; index < divisor_count; index++)
        free(data[index].values);
    free(data);
    data = NULL;
    free(pfree_divisors);
    pfree_divisors = NULL;

    int kernel_dimension = (int)kernel_dimension_i64;
    int signature_capacity = kernel_dimension;
    if ((i64)signature_capacity > expected_remaining_even_rows)
        signature_capacity = (int)expected_remaining_even_rows;
    int signature_words = (kernel_dimension + 63) / 64;
    uint64_t signature_bytes =
        (uint64_t)signature_capacity * signature_words * sizeof(u64) +
        (uint64_t)(signature_capacity + kernel_dimension) * sizeof(int) +
        (uint64_t)signature_words * sizeof(u64);
    int maximum_blocks =
        (batch_capacity + FINISH_LOCAL_BLOCK - 1) /
        FINISH_LOCAL_BLOCK;
    int hash_capacity = 1;
    while (hash_capacity < 2 * FINISH_LOCAL_BLOCK)
        hash_capacity *= 2;
    uint64_t batch_matrix_bytes =
        (uint64_t)batch_capacity * signature_words * sizeof(u64);
    uint64_t batch_aux_bytes =
        (uint64_t)maximum_blocks * hash_capacity * 2 * sizeof(int) +
        (uint64_t)maximum_blocks * sizeof(int) +
        (uint64_t)batch_capacity * sizeof(int);
    uint64_t parallel_bytes = batch_matrix_bytes + batch_aux_bytes;
    if (UINT64_MAX - signature_bytes < parallel_bytes)
        die("parallel finisher concurrent allocation-size overflow");
    uint64_t finisher_concurrent_bytes = signature_bytes + parallel_bytes;
    if (UINT64_MAX - finisher_concurrent_bytes <
        maximum_remaining_unit_bytes)
        die("parallel finisher/unit allocation-size overflow");
    finisher_concurrent_bytes += maximum_remaining_unit_bytes;
    guard_additional_allocation(
        finisher_concurrent_bytes, force,
        "signature basis, parallel batch, and largest unit list");
    DenseOutput signatures =
        dense_output_create(kernel_dimension, signature_capacity);
    u64 *batch_rows = signature_words > 0
                          ? xcalloc((size_t)batch_capacity *
                                        signature_words,
                                    sizeof(*batch_rows))
                          : NULL;
    int *local_keys =
        xmalloc((size_t)maximum_blocks * hash_capacity * sizeof(int));
    int *local_values =
        xmalloc((size_t)maximum_blocks * hash_capacity * sizeof(int));
    int *local_counts =
        xcalloc((size_t)maximum_blocks, sizeof(*local_counts));
    int *local_indices =
        xmalloc((size_t)batch_capacity * sizeof(*local_indices));
    printf("FINISH_PARALLEL kernel_dimension=%d signature_capacity=%d "
           "sector_snapshots=%.3f_GiB signature_allocation=%.3f_GiB "
           "batch_allocation=%.3f_GiB workers=%d batch=%d block=%d\n",
           kernel_dimension, signature_capacity,
           (double)sector_snapshot_bytes /
               (double)(UINT64_C(1) << 30),
           (double)signature_bytes / (double)(UINT64_C(1) << 30),
           (double)parallel_bytes / (double)(UINT64_C(1) << 30),
           workers, batch_capacity, FINISH_LOCAL_BLOCK);
    fflush(stdout);

    i64 remaining_rows_processed = 0;
    i64 next_report = 50000;
    for (int index = 0;
         index < all_divisor_count && signatures.rank < kernel_dimension;
         index++) {
        int q = all_divisors[index];
        if (q % prime != 0)
            continue;
        if (!spatial_row_pruning_is_selected(&pruning, q))
            continue;
        int h = composite_buffered_radius(n_level, q_total, q);
        if (h < 2)
            continue;
        int step = q_total / q;
        int required_u_parity = step & 1;
        CompositeUnits units =
            parallel_make_units(q, force, workers);
        i64 lower = 1 - (i64)h;
        i64 upper = (i64)h - 2;
        i64 first = first_with_parity(lower, required_u_parity);
        i64 row_count = upper >= first ? (upper - first) / 2 + 1 : 0;
        for (i64 row_base = 0;
             row_base < row_count && signatures.rank < kernel_dimension;
             row_base += batch_capacity) {
            int batch_count = (int)(row_count - row_base);
            if (batch_count > batch_capacity)
                batch_count = batch_capacity;
            int block_count =
                (batch_count + FINISH_LOCAL_BLOCK - 1) /
                FINISH_LOCAL_BLOCK;

#if defined(_OPENMP)
#pragma omp parallel for schedule(static)
#endif
            for (int slot = 0; slot < batch_count; slot++) {
                u64 *work = batch_rows +
                            (size_t)slot * signature_words;
                if (signature_words > 0)
                    memset(work, 0,
                           (size_t)signature_words * sizeof(*work));
                i64 pair_index = row_base + slot;
                i64 u = first + 2 * pair_index;
                for (int unit_index = 0; unit_index < units.count;
                     unit_index++) {
                    int a = units.values[unit_index];
                    int j = positive_mod_i64(
                        u + (i64)a * step, q_total);
                    if ((j & 1) != 0)
                        die("internal parallel row has odd coordinate");
                    int residue = j % prime;
                    int t = (j - residue) / prime;
                    if (((t + residue) & 1) != 0)
                        die("internal parallel CRT parity mismatch");
                    int column = (t - (residue & 1)) / 2;
                    parallel_snapshot_toggle(
                        &sectors[residue], kernel_offsets[residue],
                        column, work, signature_words,
                        kernel_dimension);
                }
                if ((kernel_dimension & 63) != 0 &&
                    signature_words > 0)
                    work[signature_words - 1] &=
                        (UINT64_C(1) << (kernel_dimension & 63)) - 1;
                (void)parallel_reduce_global(&signatures, work);
            }

#if defined(_OPENMP)
#pragma omp parallel for schedule(static)
#endif
            for (int block = 0; block < block_count; block++) {
                int begin = block * FINISH_LOCAL_BLOCK;
                int end = begin + FINISH_LOCAL_BLOCK;
                if (end > batch_count)
                    end = batch_count;
                int *keys = local_keys +
                            (size_t)block * hash_capacity;
                int *values = local_values +
                              (size_t)block * hash_capacity;
                for (int position = 0; position < hash_capacity;
                     position++)
                    keys[position] = -1;
                int count = 0;
                for (int slot = begin; slot < end; slot++) {
                    if (parallel_local_insert(
                            batch_rows, signature_words,
                            kernel_dimension, slot, keys, values,
                            hash_capacity - 1))
                        local_indices[begin + count++] = slot;
                }
                local_counts[block] = count;
            }

            for (int block = 0;
                 block < block_count &&
                 signatures.rank < kernel_dimension;
                 block++) {
                int begin = block * FINISH_LOCAL_BLOCK;
                for (int local = 0;
                     local < local_counts[block] &&
                     signatures.rank < kernel_dimension;
                     local++) {
                    int slot = local_indices[begin + local];
                    u64 *work = batch_rows +
                                (size_t)slot * signature_words;
                    (void)dense_output_insert(&signatures, work);
                }
            }
            remaining_rows_processed += batch_count;
            if (remaining_rows_processed >= next_report) {
                printf("FINISH_PARALLEL progress rows=%lld rank=%d/%d\n",
                       (long long)remaining_rows_processed,
                       signatures.rank, kernel_dimension);
                fflush(stdout);
                while (next_report <= remaining_rows_processed)
                    next_report += 50000;
            }
        }
        composite_destroy_units(&units);
    }
    if (signatures.rank < kernel_dimension &&
        remaining_rows_processed != expected_remaining_even_rows)
        die("internal parallel P-divisible row count mismatch");

    i64 even_base_rank = (i64)q_total / 2 - kernel_dimension;
    i64 even_rank = even_base_rank + signatures.rank;
    i64 even_defect = kernel_dimension - signatures.rank;
    i64 full_rank = 2 * even_rank;
    i64 full_defect = 2 * even_defect;
    printf("TOTAL P_free_even_rank=%lld/%d P_free_even_kernel=%d "
           "P_divisible_signature_rank=%d/%d even_rank=%lld/%d "
           "full_rank=%lld/%d full_defect=%lld\n",
           (long long)even_base_rank, q_total / 2, kernel_dimension,
           signatures.rank, kernel_dimension, (long long)even_rank,
           q_total / 2, (long long)full_rank, q_total,
           (long long)full_defect);

    free(local_indices);
    free(local_counts);
    free(local_values);
    free(local_keys);
    free(batch_rows);
    dense_output_destroy(&signatures);
    for (int residue = 0; residue < prime; residue++)
        snapshot_destroy(&sectors[residue]);
    free(sectors);
    free(kernel_offsets);

cleanup_unbuilt:
    spatial_row_pruning_destroy(&pruning);
    free(data);
    free(pfree_divisors);
    free(all_divisors);
    return EXIT_SUCCESS;
}
