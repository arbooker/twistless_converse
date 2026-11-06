# Distributed N=97 calculation

This is the one-prime CRT/block-Wiedemann pipeline at
`N=97, M=61261200, Q=5942336400`. It is **not** the two-prime CRT solver.
Only parity zero is processed; reflection supplies the other parity.

## Build and configure

Build the project helpers with `make -C numerics`. Then, from the repository
root, initialize the pinned public CADO source and build its GF(2) tools:

```sh
git submodule update --init third_party/cado-nfs
bash numerics/build_cado.sh
export CADO_BWC_DIR="$PWD/build/cado/linalg/bwc"
```

CADO is pinned to `e3f70ce77f6ce332a6a95092eedf04474165db08`. The build requires
C/C++ compilers, CMake, GMP development files, Perl and Python. Build jobs
default to one; override `BUILD_JOBS` only within available memory.
`ARCH_FLAGS` selects the CPU architecture. The original cluster build used
`-march=skylake-avx512 -mtune=skylake-avx512`; do not use that setting on a CPU
without AVX-512. The export defaults to a native, non-MPI build and permits
dynamic system-library linking. The original computation used static linking.

Run `bash numerics/n97/00_check.sh` after building. It checks dimensions and
the 64-bit modulus path; it does not prove spanning. All paths and binaries
must be accessible on the compute nodes, and the CADO build tree must remain
intact because its generated driver uses files from that tree.

## Slurm templates

Review `slurm/*.sbatch` for your cluster before submission. No private
account or partition is embedded. Set `SBATCH_ACCOUNT` if your cluster
requires an account, and set `N97_PARTITION`. The optional
`N97_TEST_PARTITION` and `N97_FINISH_PARTITION` select different queues.

```sh
export N97_PARTITION=your_compute_partition
export N97_TEST_PARTITION=your_test_partition
bash numerics/n97/submit_n97.sh smoke /absolute/shared/work-directory
# Wait for that job to finish successfully, then:
bash numerics/n97/submit_n97.sh production /absolute/shared/work-directory I_UNDERSTAND
```

The second command submits preparation, an array of 16 independent seeds,
and a dependent exact check/finisher. It requires `SMOKE_PASS` from the first
job. Array concurrency can be reduced with `N97_ARRAY_CONCURRENCY`; seeds
need not start simultaneously. The smoke test uses N=71, Q=25585560 and can
take tens of minutes; it is not a quick shell syntax check.

Production templates reproduce the selected resource layout: one node per
seed, 24 physical cores/48 logical CPUs, eight concurrent 64-lane Krylov
processes, `--mem=170G`, 14 days. Core/sibling discovery and task affinity
are explicit. Reconstruction processes at most 256 candidates at once and
uses `BWC_MKSOL_INTERVAL=1024` for coefficient buffering, independently of
the retained checkpoint spacing `BWC_CHECKPOINT_INTERVAL=32768`.
Superseded intermediate files are discarded. Keep work directories separate from
the source repository. Provision approximately 600 GiB (645 GB) shared scratch for
all 16 seeds; allow site-specific headroom and monitor actual usage.

The final job requests 64 logical CPUs and `--mem=350G`, also 14 days. The
finisher caps input at 8192 candidate lanes (16 seeds × 512); its main dense
candidate storage is about 239 GiB before smaller working allocations.
Memory requests are Slurm values and must be checked against allocatable
node memory, not the advertised hardware total. These are production-scale
jobs, not appropriate for a laptop.

## What is rigorously checked

1. Export the sparse core (30,686,496 rows; 30,630,600 columns;
   1,474,426,612 nonzeros), then add 55,896 unit columns to make it square.
2. Run independent width-512 block-Wiedemann calculations. The exact
   determinant degree of each block recurrence supplies a rank lower bound.
3. Verify candidate annihilation and independence over F₂, and combine seeds
   until the independent kernel vectors match the nullity upper bound.
4. Only with that complete-kernel certificate, run the exact CRT endpoint
   and orbit-map finisher. Require its zero-defect result.

Randomness chooses witnesses; it does not replace any rank check. Failure
to obtain enough independent witnesses is inconclusive, never a proof of a
rank defect. `SEED_COMPLETE` and `AUGMENTED_CERTIFICATE_COMPLETE` are intermediate
markers. The final marker is `certificate/FINISHER_COMPLETE` and the associated
zero-defect output. The finisher performs the union check itself if necessary,
so there is no duplicate dependent check job.

The stage scripts can also be run manually using `N97_WORK_ROOT`. Read
`settings.sh`, `01_prepare_matrix.sh`, `02_run_seed_lanes.sh`,
`04_check_candidates.sh` and `05_finish.sh` for exact parameters and checks.

## Reconstruction from retained data

When the generator and Krylov checkpoints are already available, run
`bash numerics/n97/09_recover_and_finish.sh` in a compute allocation with
`N97_WORK_ROOT` and `CADO_BWC_DIR` set. This reconstructs and verifies
candidates sequentially, stops once the union has certified the complete
kernel, and runs the finisher. Use `--check-only` to omit the finisher,
or `bash numerics/n97/08_recover_seed.sh SEED` for one seed.
Each reconstruction stage uses 24 threads and a 128-GiB address-space cap;
the finisher needs the larger allocation described above. These entry points
require retained generator and checkpoint files, not just the final
candidate files left by compaction. A checksummed candidate manifest allows
the checker to accept fewer than 512 candidates when sufficient.
