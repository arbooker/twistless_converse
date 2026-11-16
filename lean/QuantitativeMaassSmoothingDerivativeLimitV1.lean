module

public import QuantitativeMaassLipschitzSmoothingDerivativeV1
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set Metric ContinuousLinearMap Filter
open scoped Convolution Topology

namespace QuantitativeMaass

local instance : Measure.IsAddHaarMeasure (volume : Measure (ℝ×ℝ)) := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- Shrinking smooth averages recover the actual derivative almost everywhere. -/
theorem smoothBumpAverage_fderiv_tendsto_ae {K : NNReal} {f : (ℝ×ℝ) → ℂ}
    (hf : LipschitzWith K f) {φ : ℕ → ContDiffBump (0 : ℝ×ℝ)} {C : ℝ}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    (hφC : ∀ᶠ n in atTop,(φ n).rOut≤C*(φ n).rIn) :
    ∀ᵐ x ∂(volume : Measure (ℝ×ℝ)),
      Tendsto (fun n => fderiv ℝ (smoothBumpAverage (φ n) f) x) atTop
        (𝓝 (fderiv ℝ f x)) := by
  simpa only [smoothBumpAverage_fderiv _ hf] using
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      hφ hφC (lipschitz_fderiv_locallyIntegrable hf)

/-- On each compact region the derivative error converges in square integral.
The common bound is derived from the unchanged Lipschitz constant. -/
theorem smoothBumpAverage_fderiv_square_tendsto {K : NNReal} {f : (ℝ×ℝ) → ℂ}
    (hf : LipschitzWith K f) {φ : ℕ → ContDiffBump (0 : ℝ×ℝ)} {C : ℝ}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    (hφC : ∀ᶠ n in atTop,(φ n).rOut≤C*(φ n).rIn)
    {S : Set (ℝ×ℝ)} (hS : IsCompact S) :
    Tendsto (fun n => ∫ x in S,
      ‖fderiv ℝ (smoothBumpAverage (φ n) f) x-fderiv ℝ f x‖^2)
      atTop (𝓝 0) := by
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun x => ‖fderiv ℝ (smoothBumpAverage (φ n) f) x-fderiv ℝ f x‖^2)
      (volume.restrict S) :=
    (((measurable_fderiv ℝ _).sub (measurable_fderiv ℝ _)).norm.pow_const 2).aestronglyMeasurable
  have hb (n : ℕ) : ∀ᵐ x ∂volume.restrict S,
      ‖‖fderiv ℝ (smoothBumpAverage (φ n) f) x-fderiv ℝ f x‖^2‖≤(2*(K:ℝ))^2 := by
    filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    calc
      ‖fderiv ℝ (smoothBumpAverage (φ n) f) x-fderiv ℝ f x‖ ≤
          ‖fderiv ℝ (smoothBumpAverage (φ n) f) x‖+‖fderiv ℝ f x‖ := norm_sub_le _ _
      _ ≤ (K:ℝ)+(K:ℝ) := add_le_add
        (norm_fderiv_le_of_lipschitz ℝ (smoothBumpAverage_lipschitz (φ n) hf))
        (norm_fderiv_le_of_lipschitz ℝ hf)
      _ = 2*(K:ℝ) := by ring
  have hl : ∀ᵐ x ∂volume.restrict S,
      Tendsto (fun n => ‖fderiv ℝ (smoothBumpAverage (φ n) f) x-fderiv ℝ f x‖^2)
        atTop (𝓝 (0:ℝ)) := by
    filter_upwards [ae_restrict_of_ae (smoothBumpAverage_fderiv_tendsto_ae hf hφ hφC)] with x hx
    simpa only [sub_self,norm_zero,zero_pow (by decide : 2≠0)] using
      (hx.sub (tendsto_const_nhds (x := fderiv ℝ f x))).norm.pow 2
  simpa only [integral_zero] using
    tendsto_integral_of_dominated_convergence (fun _ : ℝ×ℝ => (2*(K:ℝ))^2)
      hm (integrableOn_const hS.measure_ne_top) hb hl

#print axioms smoothBumpAverage_fderiv_tendsto_ae
#print axioms smoothBumpAverage_fderiv_square_tendsto

end QuantitativeMaass
