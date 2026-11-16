module

public import QuantitativeMaassLipschitzSmoothingV1
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set Metric ContinuousLinearMap Filter
open scoped Convolution ContDiff Topology

namespace QuantitativeMaass

local instance : Measure.IsAddHaarMeasure (volume : Measure (ℝ×ℝ)) := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- The actual a.e. derivative of a Lipschitz seed is locally integrable. -/
theorem lipschitz_fderiv_locallyIntegrable {K : NNReal} {f : (ℝ×ℝ) → ℂ}
    (hf : LipschitzWith K f) : LocallyIntegrable (fderiv ℝ f) volume := by
  apply (continuous_const : Continuous (fun _ : ℝ×ℝ => (K:ℝ))).locallyIntegrable.mono
    (measurable_fderiv ℝ f).aestronglyMeasurable
  filter_upwards with x
  simpa only [Real.norm_of_nonneg K.coe_nonneg] using norm_fderiv_le_of_lipschitz ℝ hf (x₀ := x)

/-- Differentiation commutes with smooth averaging of a Lipschitz seed.
The derivative on the right is the actual measurable Fréchet derivative. -/
theorem smoothBumpAverage_fderiv (φ : ContDiffBump (0 : ℝ×ℝ))
    {K : NNReal} {f : (ℝ×ℝ) → ℂ} (hf : LipschitzWith K f) (x : ℝ×ℝ) :
    fderiv ℝ (smoothBumpAverage φ f) x =
      (φ.normed volume ⋆[lsmul ℝ ℝ,volume] fderiv ℝ f) x := by
  have hi : Integrable (fun a => φ.normed volume a • f (x-a)) volume :=
    (φ.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ)
      φ.continuous_normed hf.continuous.locallyIntegrable x).integrable
  have hm : AEStronglyMeasurable
      (fun a => φ.normed volume a • fderiv ℝ f (x-a)) volume :=
    (φ.continuous_normed.measurable.smul
      ((measurable_fderiv ℝ f).comp (measurable_const.sub measurable_id))).aestronglyMeasurable
  have hd : ∀ᵐ a ∂(volume : Measure (ℝ×ℝ)),
      HasFDerivAt (fun y => φ.normed volume a • f (y-a))
        (φ.normed volume a • fderiv ℝ f (x-a)) x := by
    filter_upwards [(Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae
      (hf.ae_differentiableAt (μ := volume))] with a ha
    simpa only [ContinuousLinearMap.comp_id,Function.comp_def] using
      (ha.hasFDerivAt.comp x (hasFDerivAt_sub_const a)).fun_const_smul (φ.normed volume a)
  have hl : ∀ᵐ a ∂(volume : Measure (ℝ×ℝ)), ∀ y ∈ (univ : Set (ℝ×ℝ)),
      ‖φ.normed volume a • f (y-a)-φ.normed volume a • f (x-a)‖≤
        (φ.normed volume a*(K:ℝ))*‖y-x‖ := by
    filter_upwards with a y _
    rw [←smul_sub,norm_smul,Real.norm_of_nonneg (φ.nonneg_normed a),mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed a)
    simpa only [dist_eq_norm,sub_sub_sub_cancel_right] using hf.dist_le_mul (y-a) (x-a)
  have hh := hasFDerivAt_integral_of_dominated_loc_of_lip'
    (F := fun y a => φ.normed volume a • f (y-a))
    (F' := fun a => φ.normed volume a • fderiv ℝ f (x-a))
    (bound := fun a => φ.normed volume a*(K:ℝ)) (x₀ := x)
    (s := univ) (Filter.univ_mem)
    (fun y _ => (φ.continuous_normed.smul
      (hf.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
    hi hm hl (φ.integrable_normed.mul_const (K:ℝ)) hd
  exact hh.2.fderiv

#print axioms lipschitz_fderiv_locallyIntegrable
#print axioms smoothBumpAverage_fderiv

end QuantitativeMaass
