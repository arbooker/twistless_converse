module

public import QuantitativeMaassSmoothingDerivativeLimitV1
public import QuantitativeMaassSmoothingSupportV1
public import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set Metric Filter
open scoped Topology Pointwise

namespace QuantitativeMaass

local instance : Measure.IsAddHaarMeasure (volume : Measure (ℝ×ℝ)) := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- The global derivative error converges in square integral: all derivatives
are supported in one compact neighborhood of the original support. -/
theorem smoothBumpAverage_fderiv_global_square_tendsto
    {K : NNReal} {f : (ℝ×ℝ) → ℂ} (hf : LipschitzWith K f) (hc : HasCompactSupport f)
    {φ : ℕ → ContDiffBump (0 : ℝ×ℝ)} {C R : ℝ}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    (hφC : ∀ᶠ n in atTop,(φ n).rOut≤C*(φ n).rIn)
    (hR : ∀ n,(φ n).rOut≤R) :
    Tendsto (fun n => ∫ x,
      ‖fderiv ℝ (smoothBumpAverage (φ n) f) x-fderiv ℝ f x‖^2)
      atTop (𝓝 0) := by
  let S : Set (ℝ×ℝ) := closedBall 0 R+tsupport f
  have hS : IsCompact S := (isCompact_closedBall (0 : ℝ×ℝ) R).add hc.isCompact
  have hR0 : 0≤R := (φ 0).rOut_pos.le.trans (hR 0)
  have hfS : tsupport f⊆S := by
    intro x hx
    exact ⟨0,by simpa only [mem_closedBall,dist_self] using hR0,x,hx,zero_add x⟩
  have he (n : ℕ) : (∫ x in S,
      ‖fderiv ℝ (smoothBumpAverage (φ n) f) x-fderiv ℝ f x‖^2)=
      ∫ x,‖fderiv ℝ (smoothBumpAverage (φ n) f) x-fderiv ℝ f x‖^2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have h1 : x∉tsupport (smoothBumpAverage (φ n) f) :=
      fun h => hx (smoothBumpAverage_support (φ n) hc (hR n) h)
    have h2 : x∉tsupport f := fun h => hx (hfS h)
    rw [fderiv_of_notMem_tsupport ℝ h1,fderiv_of_notMem_tsupport ℝ h2,sub_zero,norm_zero]
    norm_num
  simpa only [he] using smoothBumpAverage_fderiv_square_tendsto hf hφ hφC hS

#print axioms smoothBumpAverage_fderiv_global_square_tendsto

/-- Compactly supported Lipschitz seeds also converge in the mass term. -/
theorem smoothBumpAverage_global_square_tendsto
    {K : NNReal} {f : (ℝ×ℝ) → ℂ} (hf : LipschitzWith K f) (hc : HasCompactSupport f)
    {φ : ℕ → ContDiffBump (0 : ℝ×ℝ)} {R : ℝ}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    (hR : ∀ n,(φ n).rOut≤R) :
    Tendsto (fun n => ∫ x,‖smoothBumpAverage (φ n) f x-f x‖^2) atTop (𝓝 0) := by
  let S : Set (ℝ×ℝ) := closedBall 0 R+tsupport f
  have hS : IsCompact S := (isCompact_closedBall (0 : ℝ×ℝ) R).add hc.isCompact
  have hR0 : 0≤R := (φ 0).rOut_pos.le.trans (hR 0)
  have hfS : tsupport f⊆S := by
    intro x hx
    exact ⟨0,by simpa only [mem_closedBall,dist_self] using hR0,x,hx,zero_add x⟩
  have he (n : ℕ) : (∫ x in S,‖smoothBumpAverage (φ n) f x-f x‖^2)=
      ∫ x,‖smoothBumpAverage (φ n) f x-f x‖^2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have h1 : smoothBumpAverage (φ n) f x=0 := by
      by_contra hn
      exact hx (smoothBumpAverage_support (φ n) hc (hR n) (subset_tsupport _ hn))
    have h2 : f x=0 := by
      by_contra hn
      exact hx (hfS (subset_tsupport _ hn))
    simp only [h1,h2,sub_zero,norm_zero,zero_pow (by decide : 2≠0)]
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun x => ‖smoothBumpAverage (φ n) f x-f x‖^2) (volume.restrict S) :=
    (((smoothBumpAverage_lipschitz (φ n) hf).continuous.sub hf.continuous).norm.pow 2).aestronglyMeasurable
  have hb (n : ℕ) : ∀ᵐ x ∂volume.restrict S,
      ‖‖smoothBumpAverage (φ n) f x-f x‖^2‖≤((K:ℝ)*R)^2 := by
    filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    have hh := (smoothBumpAverage_error (φ n) hf x).trans
      (mul_le_mul_of_nonneg_left (hR n) K.coe_nonneg)
    simpa only [dist_eq_norm] using hh
  have hl : ∀ᵐ x ∂volume.restrict S,
      Tendsto (fun n => ‖smoothBumpAverage (φ n) f x-f x‖^2) atTop (𝓝 (0:ℝ)) := by
    filter_upwards with x
    have ht : Tendsto (fun n => smoothBumpAverage (φ n) f x) atTop (𝓝 (f x)) :=
      ContDiffBump.convolution_tendsto_right_of_continuous hφ hf.continuous x
    simpa only [sub_self,norm_zero,zero_pow (by decide : 2≠0)] using
      (ht.sub (tendsto_const_nhds (x := f x))).norm.pow 2
  have ht := tendsto_integral_of_dominated_convergence (fun _ : ℝ×ℝ => ((K:ℝ)*R)^2)
    hm (integrableOn_const hS.measure_ne_top) hb hl
  simpa only [he,integral_zero] using ht

#print axioms smoothBumpAverage_global_square_tendsto

end QuantitativeMaass
