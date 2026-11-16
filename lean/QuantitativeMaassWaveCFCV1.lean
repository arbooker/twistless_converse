module

public import QuantitativeMaassFriedrichsCoreV1
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

/-- Resolvent-damped wave multiplier. Its zero value at the endpoint removes
the oscillatory discontinuity of the undamped unbounded wave multiplier. -/
def dampedCosine (t s : ℝ) : ℝ := s*Real.cos (t*Real.sqrt (s⁻¹-1))

theorem dampedCosine_norm_le (t s : ℝ) : ‖dampedCosine t s‖≤‖s‖ := by
  unfold dampedCosine
  rw [norm_mul,Real.norm_eq_abs (Real.cos _)]
  exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (norm_nonneg s)).trans_eq (mul_one _)

theorem dampedCosine_continuous (t : ℝ) : Continuous (dampedCosine t) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  by_cases hs : s=0
  · subst s
    change Tendsto (dampedCosine t) (𝓝 0) (𝓝 (dampedCosine t 0))
    simp only [dampedCosine,zero_mul]
    apply squeeze_zero_norm (dampedCosine_norm_le t)
    simpa only [norm_zero] using
      (continuous_norm.continuousAt : ContinuousAt (fun s : ℝ => ‖s‖) 0).tendsto
  · exact continuousAt_id.mul (Real.continuous_cos.continuousAt.comp
      (continuousAt_const.mul ((continuousAt_id.inv₀ hs).sub continuousAt_const).sqrt))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem cfc_square_inner (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (f : ℝ → ℝ) (hf : Continuous f) (v : H) :
    (inner ℂ v (cfc (fun s => (f s)^2) A v)).re=‖cfc f A v‖^2 := by
  rw [cfc_pow f 2 A hf.continuousOn hA,pow_two]
  have hs : (cfc (p := IsSelfAdjoint) f A).adjoint=cfc (p := IsSelfAdjoint) f A := cfc_predicate f A
  change (inner ℂ v (cfc (p := IsSelfAdjoint) f A (cfc (p := IsSelfAdjoint) f A v))).re=_
  rw [← hs,ContinuousLinearMap.adjoint_inner_right,hs]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

/-- Pointwise square domination implies a vectorwise CFC bound. This is
stronger than an operator-norm estimate and permits extension from the
actual resolvent range without a Borel-calculus assumption. -/
theorem cfc_apply_norm_le_of_sq_le (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ s∈spectrum ℝ A, (f s)^2≤(g s)^2) (v : H) :
    ‖cfc f A v‖≤‖cfc g A v‖ := by
  have hm : cfc (fun s => (f s)^2) A≤cfc (fun s => (g s)^2) A :=
    cfc_mono hfg (hf.pow 2).continuousOn (hg.pow 2).continuousOn
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive.mp (sub_nonneg.mpr hm)).re_inner_nonneg_right v
  simp only [sub_apply,inner_sub_right,RCLike.re_to_complex,Complex.sub_re] at hp
  rw [cfc_square_inner A hA g hg v,cfc_square_inner A hA f hf v] at hp
  nlinarith [norm_nonneg (cfc f A v),norm_nonneg (cfc g A v)]

theorem dampedCosine_apply_norm_le (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (t : ℝ) (v : H) : ‖cfc (dampedCosine t) A v‖≤‖A v‖ := by
  have h := cfc_apply_norm_le_of_sq_le A hA (dampedCosine t) id
    (dampedCosine_continuous t) continuous_id (fun s _ => by
      have hs := dampedCosine_norm_le t s
      simpa only [Real.norm_eq_abs,id_eq,sq_abs] using sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hs) v
  simpa only [cfc_id ℝ A hA] using h

#print axioms dampedCosine_continuous
#print axioms dampedCosine_apply_norm_le

end QuantitativeMaass.Wave
