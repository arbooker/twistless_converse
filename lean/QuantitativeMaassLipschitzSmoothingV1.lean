module

public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set Metric ContinuousLinearMap Filter
open scoped Convolution ContDiff

namespace QuantitativeMaass

local instance : Measure.IsAddHaarMeasure (volume : Measure (ℝ×ℝ)) := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- Normalized smooth averaging of a real-coordinate seed. -/
def smoothBumpAverage (φ : ContDiffBump (0 : ℝ×ℝ)) (f : (ℝ×ℝ) → ℂ) : (ℝ×ℝ) → ℂ :=
  φ.normed volume ⋆[lsmul ℝ ℝ, volume] f

/-- Smooth averaging preserves the actual Lipschitz constant. -/
theorem smoothBumpAverage_lipschitz (φ : ContDiffBump (0 : ℝ×ℝ))
    {K : NNReal} {f : (ℝ×ℝ) → ℂ} (hf : LipschitzWith K f) :
    LipschitzWith K (smoothBumpAverage φ f) := by
  have hi (x : ℝ×ℝ) : Integrable (fun t => φ.normed volume t • f (x-t)) volume :=
    (φ.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ)
      φ.continuous_normed hf.continuous.locallyIntegrable x).integrable
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  change ‖(∫ t,φ.normed volume t • f (x-t))-
    (∫ t,φ.normed volume t • f (y-t))‖≤(K:ℝ)*dist x y
  rw [←integral_sub (hi x) (hi y)]
  have hp (t : ℝ×ℝ) : ‖φ.normed volume t • f (x-t)-φ.normed volume t • f (y-t)‖≤
      φ.normed volume t*((K:ℝ)*dist x y) := by
    rw [←smul_sub,norm_smul,Real.norm_of_nonneg (φ.nonneg_normed t)]
    apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed t)
    simpa only [dist_eq_norm,sub_sub_sub_cancel_right] using hf.dist_le_mul (x-t) (y-t)
  exact (norm_integral_le_of_norm_le ((φ.integrable_normed).mul_const ((K:ℝ)*dist x y))
    (Eventually.of_forall hp)).trans_eq (by rw [integral_mul_const,φ.integral_normed,one_mul])

theorem smoothBumpAverage_smooth (φ : ContDiffBump (0 : ℝ×ℝ))
    {f : (ℝ×ℝ) → ℂ} (hf : Continuous f) :
    ContDiff ℝ ∞ (smoothBumpAverage φ f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hf.locallyIntegrable

theorem smoothBumpAverage_error (φ : ContDiffBump (0 : ℝ×ℝ))
    {K : NNReal} {f : (ℝ×ℝ) → ℂ} (hf : LipschitzWith K f) (x : ℝ×ℝ) :
    dist (smoothBumpAverage φ f x) (f x)≤(K:ℝ)*φ.rOut := by
  apply φ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable
  intro y hy
  exact (hf.dist_le_mul y x).trans (mul_le_mul_of_nonneg_left hy.le K.coe_nonneg)

theorem smoothBumpAverage_compact (φ : ContDiffBump (0 : ℝ×ℝ))
    {f : (ℝ×ℝ) → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (smoothBumpAverage φ f) :=
  φ.hasCompactSupport_normed.convolution (lsmul ℝ ℝ) hf

/-- Concrete smooth approximations of a Lipschitz seed, with simultaneous
uniform error, derivative, and compact-support control. -/
theorem lipschitz_seed_smooth_approximation {K : NNReal} {f : (ℝ×ℝ) → ℂ}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) {δ : ℝ} (hδ : 0<δ) :
    ∃ g : (ℝ×ℝ) → ℂ,ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ LipschitzWith K g ∧
      (∀ x,dist (g x) (f x)≤(K:ℝ)*δ) ∧ (∀ x,‖fderiv ℝ g x‖≤K) := by
  let φ : ContDiffBump (0 : ℝ×ℝ) := ⟨δ/2,δ,half_pos hδ,half_lt_self hδ⟩
  refine ⟨smoothBumpAverage φ f,smoothBumpAverage_smooth φ hf.continuous,
    smoothBumpAverage_compact φ hc,smoothBumpAverage_lipschitz φ hf,
    smoothBumpAverage_error φ hf,?_⟩
  intro x
  exact norm_fderiv_le_of_lipschitz ℝ (smoothBumpAverage_lipschitz φ hf)

#print axioms smoothBumpAverage_lipschitz
#print axioms smoothBumpAverage_smooth
#print axioms smoothBumpAverage_error
#print axioms smoothBumpAverage_compact
#print axioms lipschitz_seed_smooth_approximation

end QuantitativeMaass
