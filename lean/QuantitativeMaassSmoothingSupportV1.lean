module

public import QuantitativeMaassLipschitzSmoothingV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Metric ContinuousLinearMap
open scoped Convolution Pointwise

namespace QuantitativeMaass

/-- Every sufficiently small smoothing has support in one fixed compact
neighborhood of the original seed support. -/
theorem smoothBumpAverage_support (φ : ContDiffBump (0 : ℝ×ℝ))
    {f : (ℝ×ℝ) → ℂ} (hf : HasCompactSupport f) {R : ℝ} (hR : φ.rOut≤R) :
    tsupport (smoothBumpAverage φ f)⊆closedBall (0 : ℝ×ℝ) R+tsupport f := by
  apply closure_minimal _ ((isCompact_closedBall (0 : ℝ×ℝ) R).add hf.isCompact).isClosed
  apply (support_convolution_subset (lsmul ℝ ℝ)).trans
  apply add_subset_add _ subset_closure
  rw [φ.support_normed_eq]
  exact ball_subset_closedBall.trans (closedBall_subset_closedBall hR)

/-- Smoothing on a radius smaller than the support's lower height keeps
the entire topological support inside the upper half-plane. -/
theorem smoothBumpAverage_support_positive (φ : ContDiffBump (0 : ℝ×ℝ))
    {f : (ℝ×ℝ) → ℂ} (hf : HasCompactSupport f) {r R : ℝ}
    (hR : φ.rOut≤R) (hRr : R<r) (hr : ∀ Z∈tsupport f,r≤Z.2) :
    tsupport (smoothBumpAverage φ f)⊆{Z : ℝ×ℝ | 0<Z.2} := by
  intro Z hZ
  obtain ⟨x,hx,y,hy,rfl⟩ := smoothBumpAverage_support φ hf hR hZ
  have hxnorm : ‖x‖≤R := by simpa only [mem_closedBall,dist_zero_right] using hx
  have hx2 : -R≤x.2 := by
    have hh := (norm_snd_le x).trans hxnorm
    rw [Real.norm_eq_abs] at hh
    exact (abs_le.mp hh).1
  have hy2 := hr y hy
  change 0<x.2+y.2
  linarith

#print axioms smoothBumpAverage_support
#print axioms smoothBumpAverage_support_positive

end QuantitativeMaass
