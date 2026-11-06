module

public import SmallLevelOriginalV1
public import SmallLevelAnalyticRigidityTheoryV4
public import SmallLevelThirtySixOriginalV1

/- Progress check for paper2-Astra.tex thm:small-levels.

The exact full target is SmallLevelOriginal.SmallLevelsTheorem. It is NOT
proved by this module. Level one is proved as actual ModularForm membership.

The new analytic chain proves fixed-point germ rigidity, rational-trace
nontorsion, fractional-period vanishing, exact five-cycle filter elimination,
and the level-36 five-branch filter conclusion without a cusp-growth premise.
The original level-36 Euler data supply the scaled Fourier quadratic law,
both possible S signs, holomorphy and the negative obstruction's full modular
invariance. The exact Hecke identity, finite congruence descent and cusp
conditions at level 36, and the other small levels, remain to be proved.
-/

#check SmallLevelOriginal.SmallLevelsTheorem
#check SmallLevelOriginal.level_one
#check SmallLevelThirtySix.original_orbit_data
#check SmallLevelAnalyticRigidity.hecke_filter_eq_zero

#print axioms SmallLevelOriginal.level_one
#print axioms SmallLevelAnalyticRigidity.multiplier_eq_derivative_pow
#print axioms SmallLevelAnalyticRigidity.rational_trace_eqOn_zero
#print axioms SmallLevelAnalyticRigidity.hecke_filter_eq_zero
#print axioms SmallLevelThirtySix.original_orbit_data
