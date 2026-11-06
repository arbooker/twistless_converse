module

public import SmallLevelProgressCheckV19
public import QuantitativeArithmeticLevelTwentyOneConverseV4

@[expose] public section

-- Actual level-21 continuation, all signs and unrestricted Hecke eigenvalue.
-- The sparse kernel certificates, matrix identification and every analytic
-- continuation premise are checked. Rightmost poles satisfy the explicit
-- determinant-factor equation and have a unique normalized leading vector.
-- Pole exclusion and full level-21 modularity are NOT asserted here.
#check SmallLevelOriginal.SmallLevelsTheorem
#print axioms SmallLevelTwentyOne.laurent_kernel
#print axioms SmallLevelTwentyOne.determinantFactor_exists_nonzero
#print axioms SmallLevelTwentyOne.laurentMatrix_exists_nonsingular
#check SmallLevelTwentyOne.original_leadingMatrix_nonsingular
#print axioms SmallLevelTwentyOne.original_leadingMatrix_nonsingular
#check SmallLevelTwentyOne.original_matrix_system
#print axioms SmallLevelTwentyOne.original_matrix_system
#check SmallLevelTwentyOne.original_grid_continuation
#print axioms SmallLevelTwentyOne.original_grid_continuation
#print axioms SmallLevelContinuation.continued_rows
#print axioms SmallLevelContinuation.continued_leading_kernel
#check SmallLevelTwentyOne.original_continued_system
#print axioms SmallLevelTwentyOne.original_continued_system
#print axioms SmallLevelTwentyOne.original_pole_constraint
#print axioms SmallLevelTwentyOne.rowCoefficient_complex
#print axioms SmallLevelTwentyOne.leadingMatrix_complex
#print axioms SmallLevelTwentyOne.original_singular_factor
#check SmallLevelTwentyOne.original_poles_on_locus
#print axioms SmallLevelTwentyOne.original_poles_on_locus
#print axioms SmallLevelTwentyOne.original_rank_coordinate
#print axioms SmallLevelTwentyOne.original_normalized_kernel_unique
#check SmallLevelTwentyOne.original_pole_normalization
#print axioms SmallLevelTwentyOne.original_pole_normalization
