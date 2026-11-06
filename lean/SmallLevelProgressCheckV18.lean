module

public import SmallLevelProgressCheckV17
public import SmallLevelTaylorTheoryV4

@[expose] public section

-- Genuine movable Mellin remainders now follow from the original input.
-- All-order shifted-Mellin coefficient identification and finite grid
-- certificates remain necessary before completing another level.
#check SmallLevelOriginal.SmallLevelsTheorem
#print axioms SmallLevelTaylor.fourier_boundary_bound
#print axioms SmallLevelTaylor.deformPoint_height
#print axioms SmallLevelTaylor.deformed_analytic
#print axioms SmallLevelTaylor.original_deformed_family_bound
#print axioms SmallLevelTaylor.cauchy_coefficient_bound
#print axioms SmallLevelTaylor.cauchy_remainder_bound
#print axioms SmallLevelTaylor.original_taylorRemainder_small
#print axioms SmallLevelTaylor.fricke_deformation_point
#print axioms SmallLevelTaylor.original_fricke_taylor_small
#print axioms SmallLevelTaylor.fricke_error_locallyIntegrable
#print axioms SmallLevelTaylor.cauchy_term_rapid
#print axioms SmallLevelTaylor.frickeError_rapid
#check SmallLevelTaylor.original_frickeError_mellin_analytic
#print axioms SmallLevelTaylor.original_frickeError_mellin_analytic
#check SmallLevelTaylor.original_ramanujan_mellin_remainders
#print axioms SmallLevelTaylor.original_ramanujan_mellin_remainders
#print axioms SmallLevelTaylor.additive_convergence_halfplane
#print axioms SmallLevelTaylor.frickeTaylorPolynomial_one_mellin
#check SmallLevelTaylor.leading_taylor_mellin_row
#print axioms SmallLevelTaylor.leading_taylor_mellin_row
