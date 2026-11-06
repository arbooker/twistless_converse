CC ?= cc
ARCH_FLAGS ?= -march=native
CFLAGS ?= -O3 -std=gnu11 -Wall -Wextra
OMP_FLAGS ?= -fopenmp
FLINT_CFLAGS := $(shell pkg-config --cflags flint)
FLINT_LIBS := $(shell pkg-config --libs flint)

PLAIN = spatial_qorder_f2_parity spatial_crt_bw_export \
        spatial_qorder_hall_screen cado_square_complete_f2 \
        cado_rank_from_lingen_f2 cado_solution_check_f2
PARALLEL = spatial_crt_kernel_f2_parity_core spatial_crt_kernel_f2_parity_dense \
           spatial_crt_composite_f2_parity_parallel spatial_crt_kernel_f2_twoprime \
           spatial_crt_kernel_f2_bw_finish_minor_largeq
PROGRAMS = $(PLAIN) $(PARALLEL) exact_q_rank_flint spatial_qorder_hall_screen_general_u64
ALL_SOURCE = $(wildcard src/*.c src/*.h)

.PHONY: all test
all: $(addprefix bin/,$(PROGRAMS))

bin build:
	mkdir -p $@

$(addprefix bin/,$(PLAIN)): bin/%: src/%.c $(ALL_SOURCE) | bin
	$(CC) $(CPPFLAGS) $(CFLAGS) $(ARCH_FLAGS) $< $(LDFLAGS) -lm -o $@

$(addprefix bin/,$(PARALLEL)): bin/%: src/%.c $(ALL_SOURCE) | bin
	$(CC) $(CPPFLAGS) $(CFLAGS) $(ARCH_FLAGS) $(OMP_FLAGS) $< $(LDFLAGS) -lm -o $@

bin/exact_q_rank_flint: src/exact_q_rank_flint.c $(ALL_SOURCE) | bin
	$(CC) $(CPPFLAGS) $(CFLAGS) $(ARCH_FLAGS) $(FLINT_CFLAGS) $< $(LDFLAGS) $(FLINT_LIBS) -lm -o $@

build/exact_q_rank_flint_core.o: src/exact_q_rank_flint.c $(ALL_SOURCE) | build
	$(CC) $(CPPFLAGS) $(CFLAGS) $(ARCH_FLAGS) $(FLINT_CFLAGS) -DEXACT_Q_RANK_FLINT_NO_MAIN -c $< -o $@

bin/spatial_qorder_hall_screen_general_u64: src/spatial_qorder_hall_screen_general_u64.c build/exact_q_rank_flint_core.o $(ALL_SOURCE) | bin
	$(CC) $(CPPFLAGS) $(CFLAGS) $(ARCH_FLAGS) $(FLINT_CFLAGS) $< build/exact_q_rank_flint_core.o $(LDFLAGS) $(FLINT_LIBS) -lm -o $@

test: all
	python3 tests/smoke.py
