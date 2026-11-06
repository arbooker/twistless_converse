# Exact numerical verification

## System and certificate meanings

The rows are the reduced Ramanujan rows `R_(q,u)`, for `q | Q`, with the
strict buffered window

```text
-Q/sqrt(lcm(N,q²)) < u < Q/sqrt(lcm(N,q²)) - 1.
```

All endpoints and row pruning are calculated exactly. For even Q, the
reflection identifies the two parity systems; certifying either one suffices.
Full rank over F₂ proves full rank over Q. A deficient modular rank does
not prove rational deficiency. The N=38 endpoint is instead checked over Q
with FLINT. See the [toolkit](../pdf/rank_verification_toolkit.pdf) for proofs.

## Build

Requirements: a 64-bit Linux system, GCC with OpenMP and unsigned 128-bit
integers, make, FLINT 3 development files, pkg-config, Python 3, and util-linux
(`prlimit`). On Debian/Ubuntu the development packages include
`build-essential pkg-config libflint-dev` (check that FLINT is version 3).

```sh
make -j1
make test
```

The default is `-O3 -march=native`, dynamically linked to FLINT. Build on the
execution machine, or explicitly select a compatible architecture with
`ARCH_FLAGS=...`. Do not transfer a native binary to a different CPU without
checking its instruction set. Portable x86-64 builds can use `ARCH_FLAGS=`.
Static linking is optional (`LDFLAGS=-static`) and requires all static
dependency libraries. No binaries or machine-specific library paths are
stored in this repository.

## Spanning at the table endpoints

[data/levels.tsv](data/levels.tsv) gives `(N,Q,method,parameter)` for all
76 admissible levels at most 95, plus 97. The parameter is the distinguished
prime for composite CRT or the auxiliary prime for two-prime CRT.

| Method | Implementation |
| --- | --- |
| `direct` | `spatial_qorder_f2_parity.c` |
| `flint` | `exact_q_rank_flint.c` (N=38) |
| `prime_dense`, `prime_core` | One-prime CRT, dense or compressed common core |
| `composite_crt` | `spatial_crt_composite_f2_parity_parallel.c` |
| `two_prime`, `two_prime_projected` | `spatial_crt_kernel_f2_twoprime.c` (N=79,83,89) |
| `block_wiedemann` | The [N=97 pipeline](n97/README.md) |

`run_level.py N` prints the exact command; add `--run` to execute. It checks
both the exit status and the final zero-defect record. Resource limits are
explicit and default to one thread, one hour and 8 GiB address space:

```sh
python3 run_level.py 38 --run
python3 run_level.py 83 --threads 24 --sector-workers 5 --memory-gib 160 --timeout 14400
```

The second example only prints a command. `--memory-gib` is a hard address-
space limit, not a promise that the task fits; OpenMP stacks and mapped
libraries also count. Large levels are server computations and require a
separate resource plan. The two-prime executable also accepts `--estimate`;
the prime/composite CRT executables have their own `--estimate` modes.
Do not run all levels concurrently without measuring their combined peak.

For N=89 the recorded successful projection parameters are seed `890013`,
65536 extra columns and 3 hashes. A successful projected rank certificate
is rigorous; an unsuccessful projection is only inconclusive. The driver
retains these parameters. N=79 uses P=11; N=83 and N=89 use P=13.

## Minimality is a separate calculation

The C driver `spatial_qorder_hall_screen_general_u64` scans Q below a supplied
endpoint, obeying forced divisibility (`p>7, p|N ⇒ p|Q`; `4|N ⇒ 2|Q`). It
first applies a row-rank capacity bound, then the exact capacitated Hall
flow, then calls the FLINT rational rank routine **in-process** on survivors.
The standalone `exact_q_rank_flint` uses the same implementation.

```sh
bin/spatial_qorder_hall_screen_general_u64 --minimal 38 1596
bin/spatial_qorder_hall_screen_general_u64 --minimal-file data/minimality.tsv
```

The second command is an exhaustive production scan, not a quick test.
It does not establish spanning at the supplied endpoint: combine it with
the endpoint verification above. N=38 is included in both lists; testing
its smaller Hall survivors belongs here, not in the spanning run. N=97
is omitted from the minimality list. Passing Hall alone never certifies
spanning.

## Tests and large-run boundaries

`make test` exercises direct, both one-prime, composite and two-prime CRT,
FLINT at N=38, small minimality searches, and N=97's 64-bit dimensions
without allocating its matrix. Each child has a 2 GiB/120-second limit.
The distributed sparse pipeline has a separate N=71 regression run at its
historical non-minimal Q; it is intentionally not the table endpoint test.
Its complete-kernel and final-rank checks are mandatory, not a dense fallback.

After building CADO, a much smaller optional end-to-end test is available:

```sh
CADO_BWC_DIR="$PWD/../build/cado/linalg/bwc" python3 tests/sparse_smoke.py
```

It runs the full sparse certificate chain at N=31, Q=10416: square completion,
all seven CADO stages, determinant-degree lower bound, complete kernel
verification, and the projected finisher. Each child has a 2 GiB/120-second
limit. It does not use a separate dense rank calculation as an oracle.
