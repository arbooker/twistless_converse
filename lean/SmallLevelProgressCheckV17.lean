module

public import SmallLevelProgressCheckV16
public import SmallLevelAdditiveMellinV1
public import SmallLevelContinuationTheoryV4

@[expose] public section

-- The original additive transforms now have their literal Mellin formula.
-- Closed-system continuation is proved from explicit Taylor rows and bounds;
-- those rows, bounds, and determinant certificates still require instantiation.
#check SmallLevelOriginal.SmallLevelsTheorem
#check SmallLevelAdditive.original_common_halfplane
#print axioms SmallLevelAdditive.original_common_halfplane
#print axioms SmallLevelAdditive.mellin_eq_transform
#print axioms SmallLevelContinuation.normalForm_identity
#print axioms SmallLevelContinuation.halfplane_unique
#print axioms SmallLevelContinuation.determinant_analytic
#print axioms SmallLevelContinuation.adjugate_analytic
#print axioms SmallLevelContinuation.matrixSolve_meromorphic
#print axioms SmallLevelContinuation.matrixSolve_eq_germ
#print axioms SmallLevelContinuation.determinant_nonzero_germ
#print axioms SmallLevelContinuation.matrix_halfplane_extension
#print axioms SmallLevelContinuation.halfplane_glue
#check SmallLevelContinuation.closed_system_continuation
#print axioms SmallLevelContinuation.closed_system_continuation
#print axioms SmallLevelContinuation.mellin_remainder_analytic
#check SmallLevelContinuation.closed_system_of_mellin_remainders
#print axioms SmallLevelContinuation.closed_system_of_mellin_remainders
