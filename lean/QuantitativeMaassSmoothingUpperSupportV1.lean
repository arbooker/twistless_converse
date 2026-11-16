module

public import QuantitativeMaassSmoothingSupportV1
public import QuantitativeMaassPoincareChartExtensionV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Metric UpperHalfPlane
open scoped Pointwise

namespace QuantitativeMaass
open MaassDifferential

theorem compact_upperCoordinates_preimage {K : Set Point} (hK : IsCompact K)
    (hp : K⊆{Z : Point | 0<Z.2}) : IsCompact (upperCoordinates⁻¹' K) := by
  have hr : K⊆range upperCoordinates := by
    intro Z hZ
    exact ⟨⟨⟨Z.1,Z.2⟩,hp hZ⟩,rfl⟩
  apply upperCoordinates_openEmbedding.isEmbedding.isCompact_iff.mpr
  rw [image_preimage_eq_of_subset hr]
  exact hK

/-- One actual compact subset of the upper half-plane contains all the
small-radius smooth approximations of a fixed compact coordinate seed. -/
theorem smoothBumpAverage_common_upper_support {f : Point → ℂ}
    (hf : HasCompactSupport f) {r R : ℝ} (hRr : R<r)
    (hr : ∀ Z∈tsupport f,r≤Z.2) :
    ∃ K : Set ℍ,IsCompact K ∧ ∀ φ : ContDiffBump (0 : Point),φ.rOut≤R →
      tsupport (upperFunction (smoothBumpAverage φ f))⊆K := by
  let S := closedBall (0 : Point) R+tsupport f
  have hS : IsCompact S := (isCompact_closedBall (0 : Point) R).add hf.isCompact
  have hp : S⊆{Z : Point | 0<Z.2} := by
    rintro Z ⟨x,hx,y,hy,rfl⟩
    have hxnorm : ‖x‖≤R := by simpa only [mem_closedBall,dist_zero_right] using hx
    have hx2 : -R≤x.2 := by
      have hh := (norm_snd_le x).trans hxnorm
      rw [Real.norm_eq_abs] at hh
      exact (abs_le.mp hh).1
    have hy2 := hr y hy
    change 0<x.2+y.2
    linarith
  refine ⟨upperCoordinates⁻¹' S,compact_upperCoordinates_preimage hS hp,?_⟩
  intro φ hφ
  apply closure_minimal _ (hS.isClosed.preimage upperCoordinates_openEmbedding.continuous)
  intro z hz
  exact smoothBumpAverage_support φ hf hφ
    (subset_tsupport (smoothBumpAverage φ f) hz)

#print axioms compact_upperCoordinates_preimage
#print axioms smoothBumpAverage_common_upper_support

end QuantitativeMaass
