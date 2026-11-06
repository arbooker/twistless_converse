module

public import QuantitativeNewGapNormalizerV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open scoped lp

theorem permutationSignRow_selfAdjoint {ι : Type*} (e : ι ≃ ι)
    (he : Function.Involutive e) (s : ℝ) :
    IsSelfAdjoint (permutationOperator e-(s:ℂ) • 1) := by
  have hs0 : IsSelfAdjoint ((s:ℂ) • (1 : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))) := by
    apply IsSelfAdjoint.smul
    · simp [IsSelfAdjoint]
    · exact IsSelfAdjoint.one _
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  rw [map_sub,(permutationOperator_selfAdjoint e he).adjoint_eq,hs0.adjoint_eq]

/-- Commuting actual normalizer permutations give commuting exact sign
projections, by the proved selfadjoint kernel-intertwining theorem. -/
theorem permutationSignProjections_commute {ι : Type*} (e d : ι ≃ ι)
    (he : Function.Involutive e) (hd : Function.Involutive d)
    (hed : Function.Commute e d) (s t : ℝ) :
    Commute (permutationSignSpace e s).starProjection (permutationSignSpace d t).starProjection := by
  apply kernelProjections_commute
  · exact permutationSignRow_selfAdjoint e he s
  · exact permutationSignRow_selfAdjoint d hd t
  · exact ((permutationOperators_commute e d hed).sub_right
      ((Commute.one_right _).smul_right (t:ℂ))).sub_left
        ((Commute.one_left _).smul_left (s:ℂ))

#print axioms permutationSignRow_selfAdjoint
#print axioms permutationSignProjections_commute

end QuantitativeNewGap
