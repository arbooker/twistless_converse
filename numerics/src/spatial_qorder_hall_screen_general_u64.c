/* Exact cyclotomic Hall obstruction for the genuine buffered row system.
 *
 * For every q|Q let
 *
 *   L_q = 2*ceil(Q/sqrt(lcm(N,q^2))) - 2,
 *   b_q = min(L_q,Q/q).
 *
 * Replacing primitive q-rows by complete q-coset rows is an invertible
 * divisor-triangular change of generators on the genuine nested windows.
 * In the cyclotomic decomposition of Q-periodic vectors, the complete
 * q-block can meet the Phi_D component only when D|Q/q.  Before forming the
 * flow, every proper multiple of every saturated divisor
 *
 *   s|Q,  2*ceil(Q/sqrt(lcm(N,s^2)))-2 >= Q/s
 *
 * is deleted by the exact simultaneous divisor-triangular redundancy.
 *
 * Fix a nonempty set S of primes dividing N and let A_S contain the full
 * Q-adic prime powers above S.  The components with A_S|D have dimension
 *
 *   H_S = phi(A_S)*Q/A_S,
 *
 * and only q coprime to A_S can meet them.  Their total source capacity is
 * at most
 *
 *   B_S = sum_{q|Q,(q,A_S)=1} b_q.
 *
 * Hence max_S (H_S-B_S)_+ is a rigorous lower bound for the rational
 * defect, and therefore also for every modular defect.  The program also
 * computes the stronger maximum-flow bound on the full divisor-poset graph:
 * left capacity b_q, right capacity phi(D), edge q->D iff D|Q/q.  A positive
 * value rejects Q without constructing a matrix.  A zero value is only a
 * screen, never a spanning certificate.
 *
 * The one-Q mode is a standalone Hall diagnostic.  The minimality modes
 * additionally call the exact FLINT rank routine in-process for the rare
 * Hall survivors.  Build the latter by object linking:
 *
 *   cc -O3 -DEXACT_Q_RANK_FLINT_NO_MAIN $(pkg-config --cflags flint) \
 *      -c exact_q_rank_flint.c -o exact_q_rank_flint_core.o
 *   cc -O3 -Wall -Wextra -Werror $(pkg-config --cflags flint) \
 *      spatial_qorder_hall_screen_general_u64.c exact_q_rank_flint_core.o \
 *      $(pkg-config --libs flint) -lm -o spatial_qorder_hall_screen_general_u64
 *
 * Usage:
 *   ./spatial_qorder_hall_screen_general_u64 N Q [Q ...]
 *   ./spatial_qorder_hall_screen_general_u64 --hall-survivors N UPPER_Q
 *   ./spatial_qorder_hall_screen_general_u64 --minimal N EXPECTED_Q
 *   ./spatial_qorder_hall_screen_general_u64 --minimal-file FILE
 * with 1 <= N,Q <= 2^64-1.  Unlike the original audited N|Q-only utility,
 * this census variant permits arbitrary Q; level-prime diagnostic cuts are
 * evaluated only when their selected primes divide Q.  The full divisor-
 * poset Hall flow, which determines PASS_SCREEN/REJECT, is unchanged.
 * All generated divisor products and
 * capacities must still fit in 64 bits.
 */

#include <errno.h>
#include <ctype.h>
#include <inttypes.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "exact_q_rank_flint.h"

typedef uint64_t u64;
typedef __uint128_t u128;

typedef struct {
    u64 prime;
    unsigned exponent;
} PrimePower;

typedef struct {
    int to;
    int next;
    u64 capacity;
} FlowEdge;

typedef struct {
    int node_count;
    int edge_count;
    int edge_capacity;
    int *head;
    int *level;
    int *next_edge;
    int *queue;
    FlowEdge *edges;
} FlowGraph;

typedef struct {
    u64 *divisors;
    u64 *capacities;
    u64 *raw_capacities;
    u64 *target_dimensions;
    size_t capacity;
} HallWorkspace;

typedef struct {
    size_t divisor_count;
    __int128 row_margin;
    u64 row_rank_upper_bound;
    __int128 hall_cut_defect_lower_bound;
    u64 full_hall_defect_lower_bound;
    u64 worst_level_prime_radical;
    int hall_computed;
    double hall_seconds;
} HallResult;

typedef struct {
    u64 n_level;
    u64 expected_q;
} MinimalityTarget;

typedef struct {
    u64 candidates;
    u64 row_capable;
    u64 hall_rejects;
    u64 hall_survivors;
    u64 flint_tests;
    double row_seconds;
    double hall_seconds;
    double flint_seconds;
} ScanStats;

static void die(const char *message) {
    fprintf(stderr, "%s\n", message);
    exit(EXIT_FAILURE);
}

static void *xmalloc(size_t bytes) {
    void *result = malloc(bytes);
    if (!result && bytes != 0)
        die("out of memory");
    return result;
}

static void *xrealloc(void *pointer, size_t bytes) {
    void *result = realloc(pointer, bytes);
    if (!result && bytes != 0)
        die("out of memory");
    return result;
}

static u64 parse_positive_u64(const char *text, const char *name) {
    char *end = NULL;
    errno = 0;
    unsigned long long value = strtoull(text, &end, 10);
    if (text[0] == '-' || errno != 0 || end == text || *end != '\0' ||
        value == 0) {
        fprintf(stderr, "%s must be an integer in [1,2^64-1]\n", name);
        exit(EXIT_FAILURE);
    }
    return (u64)value;
}

static u64 gcd_u64(u64 a, u64 b) {
    while (b != 0) {
        u64 next = a % b;
        a = b;
        b = next;
    }
    return a;
}

static int factor_u64(u64 n, PrimePower factors[64]) {
    int count = 0;
    for (u64 p = 2; p <= n / p; p = (p == 2) ? 3 : p + 2) {
        if (n % p != 0)
            continue;
        unsigned exponent = 0;
        do {
            n /= p;
            exponent++;
        } while (n % p == 0);
        factors[count++] = (PrimePower){p, exponent};
    }
    if (n > 1)
        factors[count++] = (PrimePower){n, 1};
    return count;
}

static size_t divisor_count(const PrimePower *factors, int factor_count) {
    size_t count = 1;
    for (int index = 0; index < factor_count; index++) {
        size_t multiplier = (size_t)factors[index].exponent + 1;
        if (count > SIZE_MAX / multiplier)
            die("too many divisors");
        count *= multiplier;
    }
    return count;
}

static void fill_divisors_recursive(const PrimePower *factors,
                                    int factor_count, int index,
                                    u64 value, u64 *divisors,
                                    size_t *position) {
    if (index == factor_count) {
        divisors[(*position)++] = value;
        return;
    }
    u64 power = 1;
    for (unsigned exponent = 0;
         exponent <= factors[index].exponent; exponent++) {
        fill_divisors_recursive(factors, factor_count, index + 1,
                                value * power, divisors, position);
        if (exponent != factors[index].exponent) {
            if (power > UINT64_MAX / factors[index].prime)
                die("divisor overflow");
            power *= factors[index].prime;
        }
    }
}

static u64 pow_u64(u64 base, unsigned exponent) {
    u64 result = 1;
    for (unsigned index = 0; index < exponent; index++) {
        if (result > UINT64_MAX / base)
            die("prime-power overflow");
        result *= base;
    }
    return result;
}

static u64 totient_from_q_factors(u64 value,
                                  const PrimePower *q_factors,
                                  int q_factor_count) {
    u64 result = value;
    for (int index = 0; index < q_factor_count; index++) {
        u64 prime = q_factors[index].prime;
        if (value % prime == 0)
            result = (result / prime) * (prime - 1);
    }
    return result;
}

static unsigned valuation_in_factorization(u64 prime,
                                           const PrimePower *factors,
                                           int factor_count) {
    for (int index = 0; index < factor_count; index++)
        if (factors[index].prime == prime)
            return factors[index].exponent;
    return 0;
}

static u64 window_radius(u64 n_level, u64 q_total, u64 q) {
    /* Since q|Q, cancel q^2 from
     *
     *   c^2 lcm(N,q^2) >= Q^2.
     *
     * This avoids forming q^2 or the lcm in 64 bits.  If
     * g=gcd(N,q^2), the exact reduced comparison is
     *
     *   c^2 (N/g) >= (Q/q)^2.
     *
     * gcd(N,q^2) is computed without forming q^2: first remove from N the
     * prime powers supplied by one q, and repeat for the second q factor. */
    u64 remaining = n_level;
    u64 shared = gcd_u64(remaining, q);
    remaining /= shared;
    shared = gcd_u64(remaining, q);
    remaining /= shared;
    u64 reduced_target = q_total / q;
    u128 target = (u128)reduced_target * reduced_target;
    u64 low = 0;
    u64 high = reduced_target;
    while (low < high) {
        u64 middle = low + (high - low) / 2;
        if ((u128)middle * middle * remaining >= target)
            high = middle;
        else
            low = middle + 1;
    }
    return low;
}

static void print_i128(__int128 value) {
    if (value == 0) {
        putchar('0');
        return;
    }
    if (value < 0) {
        putchar('-');
        value = -value;
    }
    char digits[64];
    int count = 0;
    while (value != 0) {
        digits[count++] = (char)('0' + value % 10);
        value /= 10;
    }
    while (count != 0)
        putchar(digits[--count]);
}

static FlowGraph flow_graph_create(int node_count, int edge_capacity) {
    FlowGraph graph;
    graph.node_count = node_count;
    graph.edge_count = 0;
    graph.edge_capacity = edge_capacity;
    graph.head = xmalloc((size_t)node_count * sizeof(*graph.head));
    graph.level = xmalloc((size_t)node_count * sizeof(*graph.level));
    graph.next_edge =
        xmalloc((size_t)node_count * sizeof(*graph.next_edge));
    graph.queue = xmalloc((size_t)node_count * sizeof(*graph.queue));
    graph.edges = xmalloc((size_t)edge_capacity * sizeof(*graph.edges));
    for (int node = 0; node < node_count; node++)
        graph.head[node] = -1;
    return graph;
}

static void flow_graph_destroy(FlowGraph *graph) {
    free(graph->edges);
    free(graph->queue);
    free(graph->next_edge);
    free(graph->level);
    free(graph->head);
}

static void flow_add_edge(FlowGraph *graph, int from, int to, u64 capacity) {
    if (graph->edge_count > graph->edge_capacity - 2)
        die("internal flow-edge capacity exceeded");
    int forward = graph->edge_count++;
    int reverse = graph->edge_count++;
    graph->edges[forward] =
        (FlowEdge){to, graph->head[from], capacity};
    graph->head[from] = forward;
    graph->edges[reverse] = (FlowEdge){from, graph->head[to], 0};
    graph->head[to] = reverse;
}

static int flow_bfs(FlowGraph *graph, int source, int sink) {
    for (int node = 0; node < graph->node_count; node++)
        graph->level[node] = -1;
    int begin = 0;
    int end = 0;
    graph->level[source] = 0;
    graph->queue[end++] = source;
    while (begin < end) {
        int node = graph->queue[begin++];
        for (int edge = graph->head[node]; edge >= 0;
             edge = graph->edges[edge].next) {
            int to = graph->edges[edge].to;
            if (graph->edges[edge].capacity == 0 ||
                graph->level[to] >= 0)
                continue;
            graph->level[to] = graph->level[node] + 1;
            graph->queue[end++] = to;
        }
    }
    return graph->level[sink] >= 0;
}

static u64 flow_dfs(FlowGraph *graph, int node, int sink, u64 pushed) {
    if (node == sink)
        return pushed;
    for (int *edge_pointer = &graph->next_edge[node];
         *edge_pointer >= 0;
         *edge_pointer = graph->edges[*edge_pointer].next) {
        int edge = *edge_pointer;
        int to = graph->edges[edge].to;
        if (graph->edges[edge].capacity == 0 ||
            graph->level[to] != graph->level[node] + 1)
            continue;
        u64 available = graph->edges[edge].capacity;
        u64 sent = flow_dfs(graph, to, sink,
                            pushed < available ? pushed : available);
        if (sent != 0) {
            graph->edges[edge].capacity -= sent;
            graph->edges[edge ^ 1].capacity += sent;
            return sent;
        }
    }
    return 0;
}

static u64 flow_maximum(FlowGraph *graph, int source, int sink,
                        u64 infinity) {
    u64 result = 0;
    while (flow_bfs(graph, source, sink)) {
        for (int node = 0; node < graph->node_count; node++)
            graph->next_edge[node] = graph->head[node];
        for (;;) {
            u64 sent = flow_dfs(graph, source, sink, infinity);
            if (sent == 0)
                break;
            result += sent;
        }
    }
    return result;
}

static double monotonic_seconds(void) {
    struct timespec value;
    if (clock_gettime(CLOCK_MONOTONIC, &value) != 0)
        die("clock_gettime failed");
    return (double)value.tv_sec + 1.0e-9 * value.tv_nsec;
}

static void hall_workspace_reserve(HallWorkspace *workspace, size_t count) {
    if (count <= workspace->capacity)
        return;
    workspace->divisors =
        xrealloc(workspace->divisors, count * sizeof(*workspace->divisors));
    workspace->capacities =
        xrealloc(workspace->capacities,
                 count * sizeof(*workspace->capacities));
    workspace->raw_capacities =
        xrealloc(workspace->raw_capacities,
                 count * sizeof(*workspace->raw_capacities));
    workspace->target_dimensions =
        xrealloc(workspace->target_dimensions,
                 count * sizeof(*workspace->target_dimensions));
    workspace->capacity = count;
}

static void hall_workspace_destroy(HallWorkspace *workspace) {
    free(workspace->target_dimensions);
    free(workspace->raw_capacities);
    free(workspace->capacities);
    free(workspace->divisors);
    *workspace = (HallWorkspace){0};
}

static u64 forced_divisor(const PrimePower *level_factors,
                          int level_factor_count) {
    u64 result = 1;
    int force_two = 0;
    for (int index = 0; index < level_factor_count; index++) {
        u64 prime = level_factors[index].prime;
        if (prime > 7) {
            if (result > UINT64_MAX / prime)
                die("forced divisor overflow");
            result *= prime;
        }
        if (prime == 2 && level_factors[index].exponent >= 2)
            force_two = 1;
    }
    if (force_two && result % 2 != 0) {
        if (result > UINT64_MAX / 2)
            die("forced divisor overflow");
        result *= 2;
    }
    return result;
}

static void hall_analyze_factored(
    u64 n_level, const PrimePower *level_factors, int level_factor_count,
    u64 q_total, const PrimePower *q_factors, int q_factor_count,
    int force_full_hall, HallWorkspace *workspace, HallResult *result) {
    size_t count = divisor_count(q_factors, q_factor_count);
    hall_workspace_reserve(workspace, count);
    u64 *divisors = workspace->divisors;
    u64 *capacities = workspace->capacities;
    u64 *raw_capacities = workspace->raw_capacities;
    u64 *target_dimensions = workspace->target_dimensions;
    size_t position = 0;
    fill_divisors_recursive(q_factors, q_factor_count, 0, 1,
                            divisors, &position);
    if (position != count)
        die("internal divisor-count mismatch");

    /* First compute every unpruned block capacity.  A divisor s is a
     * saturated anchor exactly when its capacity is Q/s. */
    for (size_t index = 0; index < count; index++) {
        u64 q = divisors[index];
        u64 radius = window_radius(n_level, q_total, q);
        u64 row_count = 2 * radius - 2;
        u64 translate_dimension = q_total / q;
        u64 capacity = row_count < translate_dimension
                           ? row_count : translate_dimension;
        raw_capacities[index] = capacity;
        target_dimensions[index] = totient_from_q_factors(
            q, q_factors, q_factor_count);
    }

    __int128 total_rows = 0;
    u128 selected_capacity_sum = 0;
    for (size_t q_index = 0; q_index < count; q_index++) {
        u64 q = divisors[q_index];
        int redundant = 0;
        for (size_t s_index = 0; s_index < count; s_index++) {
            u64 s = divisors[s_index];
            if (s != q && q % s == 0 &&
                raw_capacities[s_index] == q_total / s) {
                redundant = 1;
                break;
            }
        }
        capacities[q_index] = redundant ? 0 : raw_capacities[q_index];
        if (!redundant)
            total_rows += 2 * (__int128)window_radius(
                n_level, q_total, q) - 2;
        selected_capacity_sum += capacities[q_index];
    }

    u64 rank_upper_bound =
        selected_capacity_sum < q_total ? (u64)selected_capacity_sum : q_total;
    for (size_t s_index = 0;
         s_index < count && rank_upper_bound != 0; s_index++) {
        u64 s = divisors[s_index];
        u128 bound = q_total / s;
        for (size_t q_index = 0; q_index < count; q_index++) {
            if (divisors[q_index] % s == 0)
                continue;
            bound += raw_capacities[q_index];
            if (bound >= rank_upper_bound)
                break;
        }
        if (bound < rank_upper_bound)
            rank_upper_bound = (u64)bound;
    }

    *result = (HallResult){
        .divisor_count = count,
        .row_margin = total_rows - q_total,
        .row_rank_upper_bound = rank_upper_bound,
        .hall_cut_defect_lower_bound = 0,
        .full_hall_defect_lower_bound = 0,
        .worst_level_prime_radical = 0,
        .hall_computed = 0,
        .hall_seconds = 0.0,
    };
    if (!force_full_hall && rank_upper_bound < q_total)
        return;

    double hall_started = monotonic_seconds();
    __int128 best_defect = 0;
    u64 best_radical = 0;
    u64 subset_count = UINT64_C(1) << level_factor_count;
    for (u64 subset = 1; subset < subset_count; subset++) {
        u64 radical = 1;
        u64 full_part = 1;
        u64 phi_full_part = 1;
        int supported_cut = 1;
        for (int index = 0; index < level_factor_count; index++) {
            if (((subset >> index) & 1U) == 0)
                continue;
            u64 prime = level_factors[index].prime;
            unsigned exponent = valuation_in_factorization(
                prime, q_factors, q_factor_count);
            if (exponent == 0) {
                supported_cut = 0;
                break;
            }
            u64 power = pow_u64(prime, exponent);
            radical *= prime;
            full_part *= power;
            phi_full_part *= (power / prime) * (prime - 1);
        }
        if (!supported_cut)
            continue;
        __int128 target =
            (__int128)phi_full_part * (q_total / full_part);
        __int128 supply = 0;
        for (size_t index = 0; index < count; index++)
            if (gcd_u64(divisors[index], radical) == 1)
                supply += capacities[index];
        __int128 defect = target - supply;
        if (defect > best_defect) {
            best_defect = defect;
            best_radical = radical;
        }
    }

    if (count > (size_t)(INT_MAX - 2) / 2)
        die("too many divisors for flow node indices");
    size_t directed_pairs = 0;
    for (size_t q_index = 0; q_index < count; q_index++)
        for (size_t d_index = 0; d_index < count; d_index++)
            if ((q_total / divisors[q_index]) % divisors[d_index] == 0)
                directed_pairs++;
    size_t logical_edges = 2 * count + directed_pairs;
    if (logical_edges > (size_t)INT_MAX / 2)
        die("too many flow edges");
    int source = 0;
    int q_offset = 1;
    int d_offset = q_offset + (int)count;
    int sink = d_offset + (int)count;
    FlowGraph graph = flow_graph_create(
        sink + 1, (int)(2 * logical_edges));
    for (size_t index = 0; index < count; index++) {
        flow_add_edge(&graph, source, q_offset + (int)index,
                      capacities[index]);
        flow_add_edge(&graph, d_offset + (int)index, sink,
                      target_dimensions[index]);
    }
    for (size_t q_index = 0; q_index < count; q_index++)
        for (size_t d_index = 0; d_index < count; d_index++)
            if ((q_total / divisors[q_index]) % divisors[d_index] == 0)
                flow_add_edge(&graph, q_offset + (int)q_index,
                              d_offset + (int)d_index, q_total);
    u64 maximum_flow = flow_maximum(&graph, source, sink, q_total);
    if (maximum_flow > q_total)
        die("internal Hall flow exceeds the ambient dimension");
    flow_graph_destroy(&graph);

    result->hall_cut_defect_lower_bound = best_defect;
    result->full_hall_defect_lower_bound = q_total - maximum_flow;
    result->worst_level_prime_radical = best_radical;
    result->hall_computed = 1;
    result->hall_seconds = monotonic_seconds() - hall_started;
}

static void print_hall_result(u64 n_level, u64 q_total,
                              const HallResult *result) {
    printf("N=%" PRIu64 " Q=%" PRIu64
           " divisors=%zu row_margin=",
           n_level, q_total, result->divisor_count);
    print_i128(result->row_margin);
    printf(" rank_upper_bound=%" PRIu64
           " hall_cut_defect_lower_bound=",
           result->row_rank_upper_bound);
    print_i128(result->hall_cut_defect_lower_bound);
    printf(" full_hall_defect_lower_bound=%" PRIu64
           " worst_level_prime_radical=%" PRIu64 " status=%s\n",
           result->full_hall_defect_lower_bound,
           result->worst_level_prime_radical,
           result->full_hall_defect_lower_bound > 0
               ? "REJECT" : "PASS_SCREEN");
}

static uint32_t *smallest_prime_factors(u64 limit) {
    if (limit > UINT32_MAX)
        die("minimality multiplier exceeds the 32-bit SPF limit");
    if (limit > (SIZE_MAX / sizeof(uint32_t)) - 1)
        die("SPF allocation size overflow");
    uint32_t *spf =
        calloc((size_t)limit + 1, sizeof(*spf));
    if (!spf && limit != 0)
        die("out of memory allocating SPF table");
    for (u64 prime = 2; prime <= limit / prime; prime++) {
        if (spf[prime] != 0)
            continue;
        for (u64 multiple = prime * prime; multiple <= limit;
             multiple += prime)
            if (spf[multiple] == 0)
                spf[multiple] = (uint32_t)prime;
    }
    return spf;
}

static int factor_with_spf(u64 value, const uint32_t *spf,
                           PrimePower factors[64]) {
    int count = 0;
    while (value > 1) {
        u64 prime = spf[value] ? spf[value] : value;
        unsigned exponent = 0;
        do {
            value /= prime;
            exponent++;
        } while (value % prime == 0);
        factors[count++] = (PrimePower){prime, exponent};
    }
    return count;
}

static int merge_factorizations(const PrimePower *left, int left_count,
                                const PrimePower *right, int right_count,
                                PrimePower output[64]) {
    int i = 0;
    int j = 0;
    int count = 0;
    while (i < left_count || j < right_count) {
        if (j == right_count ||
            (i < left_count && left[i].prime < right[j].prime)) {
            output[count++] = left[i++];
        } else if (i == left_count || right[j].prime < left[i].prime) {
            output[count++] = right[j++];
        } else {
            output[count++] = (PrimePower){
                left[i].prime, left[i].exponent + right[j].exponent};
            i++;
            j++;
        }
    }
    return count;
}

/* The literal row-count bound has a closed form when N is prime and the
 * forced divisor is N.  This is only a rejection test: candidates that pass
 * still undergo the stronger all-orbit quotient bound below. */
static int prime_row_upper_allows(u64 n_level, u64 multiplier,
                                  const PrimePower *multiplier_factors,
                                  int multiplier_factor_count) {
    unsigned n_exponent = 0;
    u128 sigma = 1;
    for (int index = 0; index < multiplier_factor_count; index++) {
        u64 prime = multiplier_factors[index].prime;
        unsigned exponent = multiplier_factors[index].exponent;
        u128 power = 1;
        u128 term = 1;
        for (unsigned j = 0; j < exponent; j++) {
            power *= prime;
            term += power;
        }
        sigma *= term;
        if (prime == n_level)
            n_exponent = exponent;
    }
    u128 n_power = 1;
    u128 n_sigma = 1;
    for (unsigned j = 0; j < n_exponent; j++) {
        n_power *= n_level;
        n_sigma += n_power;
    }
    u128 sigma_coprime = sigma / n_sigma;
    u128 rational_part = 2 * sigma_coprime * n_sigma;
    u128 radical_coefficient = 2 * sigma_coprime * n_power;
    u128 columns = (u128)n_level * multiplier;
    if (rational_part > columns)
        return 1;
    u128 remainder = columns - rational_part;
    return radical_coefficient * radical_coefficient * n_level >
           remainder * remainder;
}

static int scan_minimality_target(const MinimalityTarget *target,
                                  const uint32_t *spf, u64 spf_limit) {
    u64 n_level = target->n_level;
    u64 expected_q = target->expected_q;
    PrimePower level_factors[64];
    int level_factor_count = factor_u64(n_level, level_factors);
    if (level_factor_count >= 63)
        die("too many distinct level primes for subset enumeration");
    u64 divisor = forced_divisor(level_factors, level_factor_count);
    if (expected_q % divisor != 0) {
        fprintf(stderr,
                "N=%" PRIu64 ": expected Q=%" PRIu64
                " violates forced divisor %" PRIu64 "\n",
                n_level, expected_q, divisor);
        return 2;
    }
    u64 upper_multiplier = (expected_q - 1) / divisor;
    if (upper_multiplier > spf_limit)
        die("internal SPF range is too small");
    PrimePower fixed_factors[64];
    int fixed_factor_count = factor_u64(divisor, fixed_factors);
    HallWorkspace workspace = {0};
    ScanStats stats = {0};
    u64 earlier_full = 0;
    int prime_level = n_level <= INT_MAX &&
                      level_factor_count == 1 &&
                      level_factors[0].prime == n_level &&
                      level_factors[0].exponent == 1 &&
                      divisor == n_level;
    double started = monotonic_seconds();

    for (u64 multiplier = 1; multiplier <= upper_multiplier; multiplier++) {
        double row_started = monotonic_seconds();
        PrimePower multiplier_factors[64];
        PrimePower q_factors[64];
        int multiplier_factor_count =
            factor_with_spf(multiplier, spf, multiplier_factors);
        stats.candidates++;
        if (prime_level &&
            !prime_row_upper_allows(n_level, multiplier,
                                    multiplier_factors,
                                    multiplier_factor_count)) {
            stats.row_seconds += monotonic_seconds() - row_started;
            goto report_progress;
        }
        int q_factor_count = merge_factorizations(
            fixed_factors, fixed_factor_count,
            multiplier_factors, multiplier_factor_count, q_factors);
        u64 q_total = divisor * multiplier;
        HallResult hall;
        hall_analyze_factored(
            n_level, level_factors, level_factor_count,
            q_total, q_factors, q_factor_count, 0, &workspace, &hall);
        double analyzed = monotonic_seconds();
        double row_seconds = analyzed - row_started - hall.hall_seconds;
        if (row_seconds < 0)
            row_seconds = 0;
        stats.row_seconds += row_seconds;
        stats.hall_seconds += hall.hall_seconds;
        if (hall.row_rank_upper_bound >= q_total) {
            stats.row_capable++;
            if (!hall.hall_computed)
                die("internal Hall computation was skipped");
            if (hall.full_hall_defect_lower_bound != 0) {
                stats.hall_rejects++;
            } else {
                stats.hall_survivors++;
                printf("HALL_SURVIVOR N=%" PRIu64 " Q=%" PRIu64 "\n",
                       n_level, q_total);
                fflush(stdout);
                if (n_level > INT_MAX || q_total > INT_MAX) {
                    fprintf(stderr,
                            "FLINT_UNAVAILABLE N=%" PRIu64 " Q=%" PRIu64
                            " reason=int_index_limit\n",
                            n_level, q_total);
                    hall_workspace_destroy(&workspace);
                    return 2;
                }
                ExactQRankFlintResult exact;
                double flint_started = monotonic_seconds();
                if (exact_q_rank_flint_compute(
                        (int)n_level, (int)q_total, 0, &exact, stdout) != 0)
                    die("in-process FLINT rank calculation failed");
                double flint_seconds =
                    monotonic_seconds() - flint_started;
                stats.flint_seconds += flint_seconds;
                stats.flint_tests++;
                printf("FLINT_RESULT N=%" PRIu64 " Q=%" PRIu64
                       " rank_QQ=%" PRId64 "/%d full_defect=%" PRId64
                       " seconds=%.6f\n",
                       n_level, q_total, exact.sector_rank,
                       exact.coordinate_count, exact.full_defect,
                       flint_seconds);
                fflush(stdout);
                if (exact.full_defect == 0) {
                    earlier_full = q_total;
                    break;
                }
            }
        }
report_progress:
        if (multiplier % UINT64_C(1000000) == 0 ||
            multiplier == upper_multiplier) {
            printf("MINIMALITY_PROGRESS N=%" PRIu64
                   " scanned=%" PRIu64 " row_capable=%" PRIu64
                   " hall_survivors=%" PRIu64 "\n",
                   n_level, stats.candidates, stats.row_capable,
                   stats.hall_survivors);
            fflush(stdout);
        }
    }

    double total_seconds = monotonic_seconds() - started;
    printf("MINIMALITY_SUMMARY N=%" PRIu64 " expected_Q=%" PRIu64
           " forced_divisor=%" PRIu64 " candidates=%" PRIu64
           " row_rejects=%" PRIu64 " hall_tests=%" PRIu64
           " hall_rejects=%" PRIu64 " flint_tests=%" PRIu64
           " earlier_full=%" PRIu64 " row_seconds=%.6f"
           " hall_seconds=%.6f flint_seconds=%.6f total_seconds=%.6f %s\n",
           n_level, expected_q, divisor, stats.candidates,
           stats.candidates - stats.row_capable, stats.row_capable,
           stats.hall_rejects, stats.flint_tests, earlier_full,
           stats.row_seconds, stats.hall_seconds, stats.flint_seconds,
           total_seconds,
           earlier_full ? "EARLIER_FULL_RANK" : "NO_EARLIER_FULL_RANK");
    hall_workspace_destroy(&workspace);
    return earlier_full ? 1 : 0;
}

/* Enumerate every modulus at most UPPER_Q allowed by the proved forced
 * divisor and surviving both the all-orbit row bound and the exact Hall
 * obstruction.  This diagnostic deliberately performs no rank computation;
 * in particular, PASS_SCREEN is not promoted to a spanning claim. */
static int scan_hall_survivors(u64 n_level, u64 upper_q) {
    PrimePower level_factors[64];
    int level_factor_count = factor_u64(n_level, level_factors);
    if (level_factor_count >= 63)
        die("too many distinct level primes for subset enumeration");
    u64 divisor = forced_divisor(level_factors, level_factor_count);
    u64 upper_multiplier = upper_q / divisor;
    if (upper_multiplier == 0) {
        printf("HALL_CENSUS_SUMMARY N=%" PRIu64 " upper_Q=%" PRIu64
               " forced_divisor=%" PRIu64
               " candidates=0 row_rejects=0 hall_tests=0"
               " hall_rejects=0 hall_survivors=0 total_seconds=0.000000\n",
               n_level, upper_q, divisor);
        return 0;
    }

    uint32_t *spf = smallest_prime_factors(upper_multiplier);
    PrimePower fixed_factors[64];
    int fixed_factor_count = factor_u64(divisor, fixed_factors);
    HallWorkspace workspace = {0};
    ScanStats stats = {0};
    int prime_level = n_level <= INT_MAX &&
                      level_factor_count == 1 &&
                      level_factors[0].prime == n_level &&
                      level_factors[0].exponent == 1 &&
                      divisor == n_level;
    double started = monotonic_seconds();

    for (u64 multiplier = 1; multiplier <= upper_multiplier; multiplier++) {
        PrimePower multiplier_factors[64];
        PrimePower q_factors[64];
        int multiplier_factor_count =
            factor_with_spf(multiplier, spf, multiplier_factors);
        stats.candidates++;
        if (prime_level &&
            !prime_row_upper_allows(n_level, multiplier,
                                    multiplier_factors,
                                    multiplier_factor_count))
            continue;
        int q_factor_count = merge_factorizations(
            fixed_factors, fixed_factor_count,
            multiplier_factors, multiplier_factor_count, q_factors);
        u64 q_total = divisor * multiplier;
        HallResult hall;
        hall_analyze_factored(
            n_level, level_factors, level_factor_count,
            q_total, q_factors, q_factor_count, 0, &workspace, &hall);
        if (hall.row_rank_upper_bound < q_total)
            continue;
        stats.row_capable++;
        stats.hall_seconds += hall.hall_seconds;
        if (!hall.hall_computed)
            die("internal Hall computation was skipped");
        if (hall.full_hall_defect_lower_bound != 0) {
            stats.hall_rejects++;
            continue;
        }
        stats.hall_survivors++;
        printf("HALL_SURVIVOR N=%" PRIu64 " Q=%" PRIu64 "\n",
               n_level, q_total);
        fflush(stdout);
    }

    printf("HALL_CENSUS_SUMMARY N=%" PRIu64 " upper_Q=%" PRIu64
           " forced_divisor=%" PRIu64 " candidates=%" PRIu64
           " row_rejects=%" PRIu64 " hall_tests=%" PRIu64
           " hall_rejects=%" PRIu64 " hall_survivors=%" PRIu64
           " hall_seconds=%.6f total_seconds=%.6f\n",
           n_level, upper_q, divisor, stats.candidates,
           stats.candidates - stats.row_capable, stats.row_capable,
           stats.hall_rejects, stats.hall_survivors,
           stats.hall_seconds, monotonic_seconds() - started);
    hall_workspace_destroy(&workspace);
    free(spf);
    return 0;
}

static int parse_target_line(char *line, MinimalityTarget *target) {
    char *comment = strchr(line, '#');
    if (comment)
        *comment = '\0';
    char *cursor = line;
    while (isspace((unsigned char)*cursor))
        cursor++;
    if (*cursor == '\0')
        return 0;
    if (*cursor == '-')
        return -1;
    errno = 0;
    char *end = NULL;
    unsigned long long n_value = strtoull(cursor, &end, 10);
    if (errno != 0 || end == cursor || n_value == 0)
        return -1;
    cursor = end;
    while (isspace((unsigned char)*cursor))
        cursor++;
    if (*cursor == '-')
        return -1;
    errno = 0;
    unsigned long long q_value = strtoull(cursor, &end, 10);
    if (errno != 0 || end == cursor || q_value == 0)
        return -1;
    cursor = end;
    while (isspace((unsigned char)*cursor))
        cursor++;
    if (*cursor != '\0')
        return -1;
    target->n_level = (u64)n_value;
    target->expected_q = (u64)q_value;
    return 1;
}

static MinimalityTarget *load_targets(const char *path, size_t *count_out) {
    FILE *file = fopen(path, "r");
    if (!file) {
        perror(path);
        exit(EXIT_FAILURE);
    }
    MinimalityTarget *targets = NULL;
    size_t count = 0;
    size_t capacity = 0;
    char line[4096];
    unsigned long line_number = 0;
    while (fgets(line, sizeof(line), file)) {
        line_number++;
        if (!strchr(line, '\n') && !feof(file)) {
            fprintf(stderr, "%s:%lu: line is too long\n",
                    path, line_number);
            exit(EXIT_FAILURE);
        }
        MinimalityTarget target;
        int status = parse_target_line(line, &target);
        if (status < 0) {
            fprintf(stderr, "%s:%lu: expected N EXPECTED_Q\n",
                    path, line_number);
            exit(EXIT_FAILURE);
        }
        if (status == 0)
            continue;
        if (count == capacity) {
            capacity = capacity ? 2 * capacity : 16;
            targets = xrealloc(targets, capacity * sizeof(*targets));
        }
        targets[count++] = target;
    }
    if (ferror(file)) {
        perror(path);
        exit(EXIT_FAILURE);
    }
    fclose(file);
    if (count == 0)
        die("minimality target file is empty");
    *count_out = count;
    return targets;
}

static int run_minimality_targets(const MinimalityTarget *targets,
                                  size_t target_count) {
    u64 maximum_multiplier = 0;
    for (size_t index = 0; index < target_count; index++) {
        for (size_t earlier = 0; earlier < index; earlier++)
            if (targets[earlier].n_level == targets[index].n_level) {
                fprintf(stderr, "duplicate level N=%" PRIu64 "\n",
                        targets[index].n_level);
                return 2;
            }
        PrimePower factors[64];
        int factor_count = factor_u64(targets[index].n_level, factors);
        u64 divisor = forced_divisor(factors, factor_count);
        if (targets[index].expected_q % divisor != 0) {
            fprintf(stderr,
                    "N=%" PRIu64 ": expected Q=%" PRIu64
                    " violates forced divisor %" PRIu64 "\n",
                    targets[index].n_level, targets[index].expected_q,
                    divisor);
            return 2;
        }
        u64 upper = (targets[index].expected_q - 1) / divisor;
        if (upper > maximum_multiplier)
            maximum_multiplier = upper;
    }
    uint32_t *spf = smallest_prime_factors(maximum_multiplier);
    int overall = 0;
    double started = monotonic_seconds();
    for (size_t index = 0; index < target_count; index++) {
        int status = scan_minimality_target(
            &targets[index], spf, maximum_multiplier);
        if (status == 2) {
            overall = 2;
            break;
        }
        if (status == 1)
            overall = 1;
    }
    printf("PIPELINE_SUMMARY targets=%zu seconds=%.6f status=%s\n",
           target_count, monotonic_seconds() - started,
           overall == 0 ? "PASS" :
           overall == 1 ? "FAIL" : "INCONCLUSIVE");
    free(spf);
    return overall;
}

static void usage(const char *program) {
    fprintf(stderr,
            "Usage:\n"
            "  %s N Q [Q ...]\n"
            "  %s --hall-survivors N UPPER_Q\n"
            "  %s --minimal N EXPECTED_Q\n"
            "  %s --minimal-file FILE\n",
            program, program, program, program);
}

int main(int argc, char **argv) {
    if (argc == 4 && strcmp(argv[1], "--hall-survivors") == 0)
        return scan_hall_survivors(
            parse_positive_u64(argv[2], "N"),
            parse_positive_u64(argv[3], "UPPER_Q"));
    if (argc == 4 && strcmp(argv[1], "--minimal") == 0) {
        MinimalityTarget target = {
            parse_positive_u64(argv[2], "N"),
            parse_positive_u64(argv[3], "EXPECTED_Q")};
        return run_minimality_targets(&target, 1);
    }
    if (argc == 3 && strcmp(argv[1], "--minimal-file") == 0) {
        size_t count = 0;
        MinimalityTarget *targets = load_targets(argv[2], &count);
        int status = run_minimality_targets(targets, count);
        free(targets);
        return status;
    }
    if (argc < 3 || argv[1][0] == '-') {
        usage(argv[0]);
        return EXIT_FAILURE;
    }

    u64 n_level = parse_positive_u64(argv[1], "N");
    PrimePower level_factors[64];
    int level_factor_count = factor_u64(n_level, level_factors);
    if (level_factor_count >= 63)
        die("too many distinct level primes for subset enumeration");
    HallWorkspace workspace = {0};
    for (int argument = 2; argument < argc; argument++) {
        u64 q_total = parse_positive_u64(argv[argument], "Q");
        PrimePower q_factors[64];
        int q_factor_count = factor_u64(q_total, q_factors);
        HallResult result;
        hall_analyze_factored(
            n_level, level_factors, level_factor_count,
            q_total, q_factors, q_factor_count, 1, &workspace, &result);
        print_hall_result(n_level, q_total, &result);
    }
    hall_workspace_destroy(&workspace);
    return EXIT_SUCCESS;
}
