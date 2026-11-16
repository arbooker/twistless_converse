module

public import QuantitativeMaassRadialWeightIntegralV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Elementary upper control complementary to x<=sinh(x). -/
theorem sinh_le_self_cosh (u : ℝ) (hu : 0≤u) : Real.sinh u≤u*Real.cosh u := by
  have hh := intervalIntegral.integral_mono_on hu (Real.continuous_cosh.intervalIntegrable (μ:=volume) 0 u)
    (intervalIntegrable_const (c:=Real.cosh u)) (fun r hr =>
      Real.cosh_le_cosh.mpr (by simpa only [abs_of_nonneg hr.1,abs_of_nonneg hu] using hr.2))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r (_ : r∈uIcc (0:ℝ) u) => Real.hasDerivAt_sinh r)
    (Real.continuous_cosh.intervalIntegrable (μ:=volume) 0 u)
  rw [he,Real.sinh_zero,sub_zero,intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hh
  exact hh

/-- Explicit quadratic bound on cosh(u)-1 with a visible endpoint constant. -/
theorem cosh_sub_one_le_quadratic (u : ℝ) (hu : 0≤u) :
    Real.cosh u-1≤Real.cosh u*u^2/2 := by
  have hi := (continuous_id.mul_const (Real.cosh u)).intervalIntegrable (μ:=volume) 0 u
  have hh := intervalIntegral.integral_mono_on hu (Real.continuous_sinh.intervalIntegrable (μ:=volume) 0 u)
    hi (fun r hr => (sinh_le_self_cosh r hr.1).trans
      (mul_le_mul_of_nonneg_left (Real.cosh_le_cosh.mpr
        (by simpa only [abs_of_nonneg hr.1,abs_of_nonneg hu] using hr.2)) hr.1))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r (_ : r∈uIcc (0:ℝ) u) => Real.hasDerivAt_cosh r)
    (Real.continuous_sinh.intervalIntegrable (μ:=volume) 0 u)
  have hid : (∫ r in (0:ℝ)..u,r)=u^2/2 := by
    have hd (r : ℝ) : HasDerivAt (fun r : ℝ => r^2/2) r r := by
      convert ((hasDerivAt_id r).pow 2).div_const 2 using 1 <;> simp
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
      (continuous_id.intervalIntegrable (μ:=volume) 0 u)
    simpa only [zero_pow (by norm_num : 2≠0),zero_div,sub_zero] using h
  rw [he,Real.cosh_zero,intervalIntegral.integral_mul_const] at hh
  change Real.cosh u-1≤(∫ r in (0:ℝ)..u,r)*Real.cosh u at hh
  rw [hid] at hh
  convert hh using 1
  ring

/-- Cancellation in the derivative of u/sinh(u) is cubic at the origin. -/
theorem sinh_cosh_cancellation (u : ℝ) (hu : 0≤u) :
    0≤u*Real.cosh u-Real.sinh u ∧
      u*Real.cosh u-Real.sinh u≤u^3*Real.cosh u := by
  refine ⟨sub_nonneg.mpr (sinh_le_self_cosh u hu),?_⟩
  have h1 := Real.self_le_sinh_iff.mpr hu
  have h2 := mul_le_mul_of_nonneg_left (cosh_sub_one_le_quadratic u hu) hu
  have h3 : 0≤u^3*Real.cosh u := by positivity
  nlinarith

#print axioms sinh_le_self_cosh
#print axioms cosh_sub_one_le_quadratic
#print axioms sinh_cosh_cancellation

end QuantitativeMaass
