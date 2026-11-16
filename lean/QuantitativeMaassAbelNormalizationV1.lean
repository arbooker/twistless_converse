module

public import QuantitativeMaassAbelMassV1
public import Mathlib.Analysis.SpecialFunctions.Arsinh

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The regular square coordinate in the inverse Abel integral. -/
def abelTimeCoordinate (t : ℝ) : ℝ := Real.sqrt 2*Real.sinh (t/2)

theorem abelTimeCoordinate_sq (t : ℝ) : 1+(abelTimeCoordinate t)^2=Real.cosh t := by
  have h := Real.cosh_two_mul (t/2)
  rw [show 2*(t/2)=t by ring,Real.cosh_sq'] at h
  dsimp [abelTimeCoordinate]
  rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  linarith

theorem abelTimeCoordinate_hasDerivAt (t : ℝ) :
    HasDerivAt abelTimeCoordinate (Real.sqrt 2/2*Real.cosh (t/2)) t := by
  convert ((Real.hasDerivAt_sinh (t/2)).comp t
    ((hasDerivAt_id t).div_const 2)).const_mul (Real.sqrt 2) using 1
  · rfl
  · ring

theorem coshWeightedTest_integrable (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) :
    Integrable (fun t => (Real.cosh (t/2):ℂ)*coshTimeTest F t) := by
  have hc : HasCompactSupport (coshTimeTest F) :=
    (isCompact_Icc : IsCompact (Icc (-R) R)).of_isClosed_subset isClosed_closure
      (closure_minimal (coshTimeTest_support F R hR hs) isClosed_Icc)
  have hcont : Continuous (fun t => (Real.cosh (t/2):ℂ)*coshTimeTest F t) := by
    unfold coshTimeTest
    fun_prop
  exact hcont.integrable_of_hasCompactSupport hc.mul_left

/-- The square substitution at q=1 is exactly the half-line cosh-weighted
time test, with its Jacobian proved and both integrals absolutely integrable. -/
theorem abelIntegral_one_time (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    abelIntegral F 1=(Real.sqrt 2/2:ℂ)*
      ∫ t in Ioi (0:ℝ), (Real.cosh (t/2):ℂ)*coshTimeTest F t := by
  have ht : Tendsto abelTimeCoordinate atTop atTop := by
    have hd : Tendsto (fun t : ℝ => t/2) atTop atTop :=
      tendsto_id.atTop_div_const (by norm_num)
    exact (Real.sinhOrderIso.tendsto_atTop.comp hd).const_mul_atTop (by positivity)
  have hcont : Continuous abelTimeCoordinate := by unfold abelTimeCoordinate; fun_prop
  have he (t : ℝ) :
      (Real.sqrt 2/2*Real.cosh (t/2)) • F (1+(abelTimeCoordinate t)^2)=
        (Real.sqrt 2/2:ℂ)*((Real.cosh (t/2):ℂ)*coshTimeTest F t) := by
    rw [abelTimeCoordinate_sq]
    simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_div,
      Complex.ofReal_ofNat,coshTimeTest]
    ring
  have hi : Integrable (fun t => (Real.sqrt 2/2*Real.cosh (t/2)) •
      F (1+(abelTimeCoordinate t)^2)) := by
    simp_rw [he]
    exact (coshWeightedTest_integrable F hF R hR hs).const_mul _
  have h := integral_deriv_smul_comp_Ioi (a:=0) (g:=fun s : ℝ => F (1+s^2))
    hcont.continuousOn ht
    (fun t _ => (abelTimeCoordinate_hasDerivAt t).hasDerivWithinAt)
    (hF.continuous.comp (by fun_prop)).continuousOn
    (quadratic_integrable F hF.continuous hc 1).integrableOn hi.integrableOn
  simp only [Function.comp_def] at h
  simp_rw [he] at h
  have hz : abelTimeCoordinate 0=0 := by simp [abelTimeCoordinate]
  rw [integral_const_mul,hz] at h
  exact h.symm

/-- The candidate radial profile has the exact scalar normalization of the
shifted spectral wave packet. The geometric measure/operator bridge is separate. -/
theorem abelProfile_time_mass (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    (2*Real.pi:ℂ)*(∫ q in Ioi (1:ℝ), abelProfile F q)=
      ∫ t, coshTimeTest F t*(Real.cosh (t/2):ℂ) := by
  let g : ℝ → ℂ := fun t => (Real.cosh (t/2):ℂ)*coshTimeTest F t
  have hi : Integrable g := coshWeightedTest_integrable F hF R hR hs
  have he (t : ℝ) : g (-t)=g t := by
    simp only [g,coshTimeTest,neg_div,Real.cosh_neg]
  have hneg : (∫ t in Iic (0:ℝ), g t)=∫ t in Ioi (0:ℝ),g t := by
    have h := integral_comp_neg_Ioi (0:ℝ) g
    simpa only [neg_zero,he] using h.symm
  have hfull : (∫ t,g t)=2*∫ t in Ioi (0:ℝ),g t := by
    rw [← intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hi.integrableOn,hneg]
    ring
  have hsqrt : (Real.sqrt 2:ℂ)^2=2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hpi : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  rw [abelProfile_integral_Ioi F hF hc,abelIntegral_one_time F hF hc R hR hs]
  have hr : (∫ t,coshTimeTest F t*(Real.cosh (t/2):ℂ))=∫ t,g t := by
    apply integral_congr_ae
    filter_upwards with t
    exact mul_comm _ _
  rw [hr,hfull]
  dsimp only [g]
  field_simp
  linear_combination hsqrt*(∫ t in Ioi (0:ℝ), (Real.cosh (t/2):ℂ)*coshTimeTest F t)

#print axioms abelTimeCoordinate_hasDerivAt
#print axioms abelIntegral_one_time
#print axioms abelProfile_time_mass

end QuantitativeMaass
