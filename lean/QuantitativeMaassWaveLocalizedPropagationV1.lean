module

public import QuantitativeMaassWavePacketPropagationV1

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology

namespace QuantitativeMaass.Weighted

/-- Density upgrades propagation from the differential core to arbitrary
quotient L2 input localized by a smooth invariant cutoff. -/
theorem localized_wave_zero (N : ℕ) (b v w : Cutoff N) (c d : ℝ)
    (hv : ∀ Z : ℍ, c<(upperFunction b.value Z).re → upperFunction v.value Z=0)
    (hw : ∀ᵐ Z ∂quotientMeasure N,
      (upperFunction b.value Z).re<d → upperFunction w.value Z=0)
    (t : ℝ) (hsep : c+|b.gradientBound| * |t|<d) (f : AutomorphicSpace N) :
    multiplier N w (Wave.shiftedQuotientWave N t
      (quotientLocalization N v.value v.smooth f)).val=0 := by
  let K := ((multiplier N w).comp (AutomorphicSpace N).subtypeL).comp
    ((Wave.shiftedQuotientWave N t).comp (quotientLocalization N v.value v.smooth))
  have he : (K : AutomorphicSpace N → Lp ℂ 2 (quotientMeasure N))=fun _ => 0 := by
    apply (poincareSeedVector_dense N).equalizer K.continuous continuous_const
    funext u
    change multiplier N w (Wave.shiftedQuotientWave N t
      (quotientLocalization N v.value v.smooth (poincareSeedVector N u))).val=0
    rw [quotientLocalization_on_seed N v.value v.smooth v.invariant v.bound_nonneg
      v.value_bound v.gradient_bound]
    apply poincare_wave_observation_zero N b w (u.localized v.value v.smooth) c d _ hw t hsep
    intro Z hZ
    change upperFunction v.value Z*upperFunction u.toFun Z=0
    rw [hv Z hZ,zero_mul]
  exact congrFun he f

/-- Compact-time packets have the same off-diagonal support property on the
whole quotient L2 space, after literal smooth localization of the input. -/
theorem localized_packet_zero (N : ℕ) (b v w : Cutoff N) (c d : ℝ)
    (hv : ∀ Z : ℍ, c<(upperFunction b.value Z).re → upperFunction v.value Z=0)
    (hw : ∀ᵐ Z ∂quotientMeasure N,
      (upperFunction b.value Z).re<d → upperFunction w.value Z=0)
    {φ : ℝ → ℂ} (hφ : Wave.ShiftedWaveWeight φ)
    {R : ℝ} (hs : Function.support φ⊆Icc (-R) R)
    (hsep : c+|b.gradientBound| * R<d) (f : AutomorphicSpace N) :
    multiplier N w (Wave.shiftedQuotientWavePacket N φ hφ
      (quotientLocalization N v.value v.smooth f)).val=0 := by
  let K := ((multiplier N w).comp (AutomorphicSpace N).subtypeL).comp
    ((Wave.shiftedQuotientWavePacket N φ hφ).comp (quotientLocalization N v.value v.smooth))
  have he : (K : AutomorphicSpace N → Lp ℂ 2 (quotientMeasure N))=fun _ => 0 := by
    apply (poincareSeedVector_dense N).equalizer K.continuous continuous_const
    funext u
    change multiplier N w (Wave.shiftedQuotientWavePacket N φ hφ
      (quotientLocalization N v.value v.smooth (poincareSeedVector N u))).val=0
    rw [quotientLocalization_on_seed N v.value v.smooth v.invariant v.bound_nonneg
      v.value_bound v.gradient_bound]
    apply poincare_packet_observation_zero N b w (u.localized v.value v.smooth) c d _ hw hφ hs hsep
    intro Z hZ
    change upperFunction v.value Z*upperFunction u.toFun Z=0
    rw [hv Z hZ,zero_mul]
  exact congrFun he f

#print axioms localized_wave_zero
#print axioms localized_packet_zero

end QuantitativeMaass.Weighted
