module

public import AsymptoticCylinderUpperCutoffV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinder

open ContinuousLinearMap Filter AsymptoticObservation AsymptoticDiagonalTrace AsymptoticFourierNorm
open scoped Topology

theorem upperCutError_tendsto_zero (A B C : ℝ) :
    Tendsto (upperCutError A B C) (𝓝 0) (𝓝 0) := by
  have hc : Continuous (upperCutError A B C) := by unfold upperCutError; fun_prop
  simpa only [upperCutError, mul_zero, Real.sqrt_zero, add_zero] using hc.tendsto 0

theorem upperCutError_small (A B C : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ r : ℝ, 0 ≤ r → r < η → upperCutError A B C r < δ := by
  have he := (tendsto_order.mp (upperCutError_tendsto_zero A B C)).2 δ hδ
  obtain ⟨η, hη, hh⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨η, hη, ?_⟩
  intro r hr hrη
  exact hh (by simpa only [dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_nonneg hr] using hrη)

variable {G σ : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- Choose the upper cutoff first and then take the large-weight limit.
The estimate is uniform over every auxiliary parameter for which the
reconstruction and middle operators have the stated common norm bounds.
In particular it is uniform over sectors, finite fold sets and depths. -/
theorem factored_upperCut_trace_small (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (R₀ : ℕ → σ → G →L[ℂ] Space) (I : ℕ → σ → G →L[ℂ] G)
    {B C : ℝ} (hR : ∀ a e, ‖R₀ a e‖ ≤ B) (hI : ∀ a e, ‖I a e‖ ≤ C)
    (t : ℕ) {scale ε : ℝ} (hs : 0 < scale) (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ H : ℝ, H₀ ≤ H → ∀ᶠ a : ℕ in atTop, ∀ e : σ,
      ‖trace (fourierBasis (w a) t hs hε)
          (compressedSandwich ((inclusion hε).comp (R₀ a e)) (I a e) (holomorphicSpace (w a) t hs hε)) -
        upperCutTrace ((inclusion hε).comp (R₀ a e)) (I a e) (w a) t hs hε H‖/(w a+2:ℕ) < δ := by
  obtain ⟨η, hη, herr⟩ := upperCutError_small (B^2*(1+majorantConstant t scale ε)) B C hδ
  obtain ⟨H₀, hH₀, htail⟩ := upperCompression_normalized_small t hs hε hη
  refine ⟨H₀, hH₀, ?_⟩
  intro H hH
  have hHp : 0 < H := hH₀.trans_le hH
  filter_upwards [hw.eventually (htail H hH)] with a ha
  intro e
  apply (factored_upperCut_trace_bound (R₀ a e) (I a e) (hR a e) (hI a e) (w a) t hs hε hHp).trans_lt
  exact herr _ (div_nonneg (upperCompression_trace_nonneg (w a) t hs hε H) (by positivity)) ha

#print axioms upperCutError_tendsto_zero
#print axioms factored_upperCut_trace_small

end AsymptoticCylinder
