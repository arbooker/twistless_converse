module

public import QuantitativeHolomorphicFilterStabilityV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open ContinuousLinearMap

variable {G H K E ι : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Extending the source by an isometry changes the filter on the orthogonal
complement, but that complement disappears in the reconstructed sandwich. -/
theorem finiteRowFilter_source_transport (S : G →L[ℂ] H) (hS : S.adjoint.comp S = 1)
    (V : G →L[ℂ] K) (qs : Finset ι) (L : ι → K →L[ℂ] E) (b : ι → ℝ) (d : ℕ) :
    (V.comp S.adjoint).comp ((finiteRowFilter qs L b (V.comp S.adjoint) d).comp
      (V.comp S.adjoint).adjoint) =
    V.comp ((finiteRowFilter qs L b V d).comp V.adjoint) := by
  have hs (x : G) : S.adjoint (S x) = x := congrArg (fun T : G →L[ℂ] G => T x) hS
  have hg (x : G) : finiteRowGram qs L (V.comp S.adjoint) (S x) = S (finiteRowGram qs L V x) := by
    simp only [finiteRowGram, sum_apply, adjoint_comp, adjoint_adjoint, comp_apply, hs, map_sum]
  let A := 1 - (finiteRowBound qs b)⁻¹ • finiteRowGram qs L V
  let B := 1 - (finiteRowBound qs b)⁻¹ • finiteRowGram qs L (V.comp S.adjoint)
  have hi (x : G) : B (S x) = S (A x) := by
    simp only [A, B, sub_apply, smul_apply, one_apply_eq_self, hg, map_sub, map_smul_of_tower]
  have hp (j : ℕ) (x : G) : (B ^ j) (S x) = S ((A ^ j) x) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ', pow_succ']
      change B ((B ^ j) (S x)) = S (A ((A ^ j) x))
      rw [ih, hi]
  apply ContinuousLinearMap.ext
  intro x
  change V (S.adjoint ((B ^ d) ((V.comp S.adjoint).adjoint x))) = V ((A ^ d) (V.adjoint x))
  rw [adjoint_comp, adjoint_adjoint, comp_apply, hp, hs]

/-- Transport of the target requires no isometry assumption: the observation
rows are composed with exactly the same target map. -/
theorem finiteRowFilter_target_transport (J : K →L[ℂ] H) (V : G →L[ℂ] K)
    (qs : Finset ι) (L : ι → H →L[ℂ] E) (b : ι → ℝ) (d : ℕ) :
    (J.comp V).comp ((finiteRowFilter qs L b (J.comp V) d).comp (J.comp V).adjoint) =
    J.comp ((V.comp ((finiteRowFilter qs (fun i => (L i).comp J) b V d).comp V.adjoint)).comp J.adjoint) := by
  have hg : finiteRowGram qs L (J.comp V) = finiteRowGram qs (fun i => (L i).comp J) V := by
    simp only [finiteRowGram, comp_assoc]
  simp only [finiteRowFilter, hg, adjoint_comp, comp_assoc]

#print axioms finiteRowFilter_source_transport
#print axioms finiteRowFilter_target_transport

end QuantitativeHolomorphic
