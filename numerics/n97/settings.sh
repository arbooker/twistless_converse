#!/usr/bin/env bash

# Fixed Hall-screened N=97 production parameters.
N_LEVEL=97
MULTIPLIER=61261200
Q_TOTAL=5942336400
PARITY=0
COMPLETION_SEED=970001

# One independent Block-Wiedemann calculation per Slurm array task.
BWC_M=512
BWC_N=512
BWC_THREADS=${BWC_THREADS:-4x6}
BWC_LINGEN_THREADS=${BWC_LINGEN_THREADS:-$BWC_THREADS}
# Krylov still writes frequent rolling snapshots for its online checks, but
# production retains only the initial vector, the latest snapshot, and the
# sparse set needed by mksol. Keep checkpoint spacing independent of the
# smaller coefficient-buffer interval used during reconstruction.
BWC_INTERVAL=${BWC_INTERVAL:-4096}
BWC_CHECKPOINT_INTERVAL=${BWC_CHECKPOINT_INTERVAL:-32768}
BWC_MKSOL_INTERVAL=${BWC_MKSOL_INTERVAL:-1024}

MATRIX_BASENAME=n97m61261200-core0
EXPECTED_ROWS=30686496
EXPECTED_COLUMNS=30630600
EXPECTED_NONZEROS=1474426612
EXPECTED_ADDED_COLUMNS=55896
EXPECTED_FULL_COPRIME_ROWS=5953252752

SEED_BASE=97003
SEED_STRIDE=100
DEFAULT_SEED_COUNT=16
