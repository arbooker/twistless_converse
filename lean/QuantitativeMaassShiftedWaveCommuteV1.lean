module

public import QuantitativeMaassShiftedWaveRangeV1
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A bounded operator commuting with the resolvent commutes with the
constructed shifted wave. This transfers a genuine resolvent commutation
proof to every wave time without assuming an eigenbasis. -/
theorem shiftedRangeCosine_commute_of_resolvent (A B : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) (hd : DenseRange A) (hBA : Commute B A) (t : ℝ) :
    Commute B (shiftedRangeCosine A t) := by
  apply DFunLike.coe_injective
  apply hd.equalizer (B * shiftedRangeCosine A t).continuous
    (shiftedRangeCosine A t * B).continuous
  funext v
  change B (shiftedRangeCosine A t (A v)) = shiftedRangeCosine A t (B (A v))
  have hAv : B (A v) = A (B v) := congrArg (fun T : H →L[ℂ] H => T v) hBA.eq
  rw [hAv, shiftedRangeCosine_range A hA hd, shiftedRangeCosine_range A hA hd]
  exact congrArg (fun T : H →L[ℂ] H => T v)
    ((hBA.symm.cfc_real (shiftedDampedCosine t)).symm.eq)

theorem shiftedQuotientWave_commute_of_resolvent (N : ℕ)
    (B : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (hB : Commute B (friedrichsResolvent N)) (t : ℝ) :
    Commute B (shiftedQuotientWave N t) :=
  shiftedRangeCosine_commute_of_resolvent _ B (friedrichsResolvent_isSelfAdjoint N)
    (friedrichsResolvent_denseRange N) hB t

#print axioms shiftedRangeCosine_commute_of_resolvent
#print axioms shiftedQuotientWave_commute_of_resolvent

end QuantitativeMaass.Wave
