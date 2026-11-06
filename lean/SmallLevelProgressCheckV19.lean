module

public import SmallLevelProgressCheckV18
public import SmallLevelTwentyOneAuxiliaryRowsV1

@[expose] public section

-- All-order Taylor--Fricke Mellin identities now follow from original input.
-- The 28 Taylor, 4 entire Ramanujan and 10 exact Hecke rows at level 21
-- are proved. Determinant and pole-exclusion certificates remain unproved.
-- No additional full small-level converse theorem is claimed here.
#check SmallLevelOriginal.SmallLevelsTheorem
#print axioms SmallLevelTaylor.integrated_series
#print axioms SmallLevelTaylor.deformed_mellin_envelope
#print axioms SmallLevelTaylor.deformed_mellin_series
#print axioms SmallLevelTaylor.coefficients_of_real_binomial
#check SmallLevelTaylor.taylorCoeff_additive_mellin
#print axioms SmallLevelTaylor.taylorCoeff_additive_mellin
#print axioms SmallLevelTaylor.taylorTerm_convergent
#print axioms SmallLevelTaylor.taylorTerm_additive_mellin
#check SmallLevelTaylor.all_taylor_mellin_rows
#print axioms SmallLevelTaylor.all_taylor_mellin_rows
#print axioms SmallLevelTaylor.normalized_taylor_mellin_rows
#check SmallLevelTaylor.original_finite_sum_taylor_rows
#print axioms SmallLevelTaylor.original_finite_sum_taylor_rows
#print axioms SmallLevelTaylor.taylorRowScalar_analytic
#print axioms SmallLevelAdditive.grid_mod
#print axioms SmallLevelAdditive.fricke_grid_partner
#check SmallLevelTaylor.original_closed_grid_taylor_rows
#print axioms SmallLevelTaylor.original_closed_grid_taylor_rows
#print axioms SmallLevelTaylor.original_ramanujan_entire
#print axioms SmallLevelTaylor.normalized_additive_hecke
#print axioms SmallLevelTwentyOne.taylorSpecs_valid
#check SmallLevelTwentyOne.original_taylor_system
#print axioms SmallLevelTwentyOne.original_taylor_system
#print axioms SmallLevelTwentyOne.original_entire_rows
#print axioms SmallLevelTwentyOne.original_hecke_grid
#print axioms SmallLevelTwentyOne.original_selected_hecke_rows
