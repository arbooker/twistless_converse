module

public import QuantitativeArithmeticMaassHeckeTheoryV4
public import QuantitativeMaassShiftedWaveCommuteV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmeticMaassHecke

open QuantitativeMaass

variable (N p : ℕ) [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (A B : ℤ) (hAB : (p : ℤ)*A+(N : ℤ)*B=1)

/-- The actual unramified automorphic Hecke operator commutes with the
Friedrichs resolvent. The differential compatibility is established on
compact Poincare seeds, then extended through the closed energy form. -/
theorem hecke_resolvent_commute :
    Commute (HeckeL2.operator N p hN hpN A B hAB) (friedrichsResolvent N) :=
  resolvent_commute_of_seed_graph N _
    (HeckeL2.operator_selfAdjoint N p hN hpN A B hAB)
    (hecke_preserves_seed_graph N p hN hpN A B hAB)

/-- Commutation with every shifted quotient wave time, without an
eigenbasis assumption or an assumed differential-domain invariance. -/
theorem hecke_shiftedWave_commute (t : ℝ) :
    Commute (HeckeL2.operator N p hN hpN A B hAB) (Wave.shiftedQuotientWave N t) :=
  Wave.shiftedQuotientWave_commute_of_resolvent N _
    (hecke_resolvent_commute N p hN hpN A B hAB) t

#print axioms hecke_resolvent_commute
#print axioms hecke_shiftedWave_commute

end QuantitativeArithmeticMaassHecke
