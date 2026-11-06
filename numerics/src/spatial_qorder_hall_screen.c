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
 * q-block can meet the Phi_D component only when D|Q/q.
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
 * Compile:
 *   gcc -std=gnu11 -O3 -Wall -Wextra -Werror \
 *       -o spatial_qorder_hall_screen spatial_qorder_hall_screen.c
 * Usage:
 *   ./spatial_qorder_hall_screen N Q [Q ...]
 * with 1 <= N,Q <= 2^64-1 and N|Q.
 */

#include <errno.h>
#include <inttypes.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

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

static u128 lcm_level_q_squared(u64 n_level, u64 q) {
    u128 q_squared = (u128)q * q;
    u64 q_mod_n = q % n_level;
    u64 q_squared_mod_n =
        (u64)(((u128)q_mod_n * q_mod_n) % n_level);
    u64 divisor = gcd_u64(n_level, q_squared_mod_n);
    return (u128)(n_level / divisor) * q_squared;
}

static u64 window_radius(u64 n_level, u64 q_total, u64 q) {
    u128 ell = lcm_level_q_squared(n_level, q);
    u128 target = (u128)q_total * q_total;
    u128 threshold = target / ell + (target % ell != 0);
    u64 low = 0;
    u64 high = q_total;
    while (low < high) {
        u64 middle = low + (high - low) / 2;
        if ((u128)middle * middle >= threshold)
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

int main(int argc, char **argv) {
    if (argc < 3) {
        fprintf(stderr, "Usage: %s N Q [Q ...]\n", argv[0]);
        return EXIT_FAILURE;
    }
    u64 n_level = parse_positive_u64(argv[1], "N");
    PrimePower level_factors[64];
    int level_factor_count = factor_u64(n_level, level_factors);
    if (level_factor_count >= 63)
        die("too many distinct level primes for subset enumeration");

    for (int argument = 2; argument < argc; argument++) {
        u64 q_total = parse_positive_u64(argv[argument], "Q");
        if (q_total % n_level != 0)
            die("require N|Q");

        PrimePower q_factors[64];
        int q_factor_count = factor_u64(q_total, q_factors);
        size_t count = divisor_count(q_factors, q_factor_count);
        u64 *divisors = xmalloc(count * sizeof(*divisors));
        u64 *capacities = xmalloc(count * sizeof(*capacities));
        u64 *target_dimensions =
            xmalloc(count * sizeof(*target_dimensions));
        size_t position = 0;
        fill_divisors_recursive(q_factors, q_factor_count, 0, 1,
                                divisors, &position);
        if (position != count)
            die("internal divisor-count mismatch");

        __int128 total_rows = 0;
        for (size_t index = 0; index < count; index++) {
            u64 q = divisors[index];
            u64 radius = window_radius(n_level, q_total, q);
            if (radius == 0 || radius - 1 > UINT64_MAX / 2)
                die("row count exceeds 64 bits");
            u64 row_count = 2 * (radius - 1);
            u64 translate_dimension = q_total / q;
            capacities[index] = row_count < translate_dimension
                                    ? row_count : translate_dimension;
            target_dimensions[index] = totient_from_q_factors(
                q, q_factors, q_factor_count);
            total_rows += row_count;
        }

        __int128 best_defect = 0;
        u64 best_radical = 0;
        u64 subset_count = UINT64_C(1) << level_factor_count;
        for (u64 subset = 1; subset < subset_count; subset++) {
            u64 radical = 1;
            u64 full_part = 1;
            u64 phi_full_part = 1;
            for (int index = 0; index < level_factor_count; index++) {
                if (((subset >> index) & 1U) == 0)
                    continue;
                u64 prime = level_factors[index].prime;
                unsigned exponent = valuation_in_factorization(
                    prime, q_factors, q_factor_count);
                if (exponent == 0)
                    die("internal missing level prime in Q");
                u64 power = pow_u64(prime, exponent);
                radical *= prime;
                full_part *= power;
                phi_full_part *= (power / prime) * (prime - 1);
            }
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
        u64 full_hall_defect = q_total - maximum_flow;
        flow_graph_destroy(&graph);

        printf("N=%" PRIu64 " Q=%" PRIu64 " divisors=%zu row_margin=",
               n_level, q_total, count);
        print_i128(total_rows - q_total);
        printf(" hall_cut_defect_lower_bound=");
        print_i128(best_defect);
        printf(" full_hall_defect_lower_bound=%" PRIu64,
               full_hall_defect);
        printf(" worst_level_prime_radical=%" PRIu64 " status=%s\n",
               best_radical,
               full_hall_defect > 0 ? "REJECT" : "PASS_SCREEN");

        free(target_dimensions);
        free(capacities);
        free(divisors);
    }
    return EXIT_SUCCESS;
}
