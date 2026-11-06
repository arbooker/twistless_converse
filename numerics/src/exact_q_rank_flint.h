#ifndef EXACT_Q_RANK_FLINT_H
#define EXACT_Q_RANK_FLINT_H

#include <stdint.h>
#include <stdio.h>

typedef struct {
    int parity_reduced;
    int coordinate_count;
    int singleton_pivots;
    int residual_columns;
    int64_t residual_rows;
    int64_t residual_rank;
    int64_t sector_rank;
    int64_t full_defect;
    long double estimated_fmpz_storage_gib;
} ExactQRankFlintResult;

/* Compute the exact rational rank for one literal (N,Q) row system.
 * If estimate_only is nonzero, stop after determining the matrix dimensions.
 * If report is non-null, emit the same stable records as the standalone
 * executable.  Fatal construction errors terminate the calling program. */
int exact_q_rank_flint_compute(int n_level, int q_total, int estimate_only,
                               ExactQRankFlintResult *result, FILE *report);

#endif
