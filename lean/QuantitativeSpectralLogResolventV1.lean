module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public section

namespace QuantitativeSpectralLogResolvent

open MeasureTheory Set

/-- The affine path from one to a positive scalar stays positive. -/
theorem affine_pos {r t : ℝ} (hr : 0 < r) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < 1+t*(r-1) := by
  by_cases h : r ≤ 1
  · have := mul_le_mul_of_nonpos_right ht.2 (sub_nonpos.mpr h)
    nlinarith
  · have := mul_nonneg ht.1 (sub_nonneg.mpr (le_of_not_ge h))
    linarith

/-- A compact-parameter resolvent representation of the scalar logarithm.
The parameter interval is fixed, unlike an improper resolvent integral. -/
theorem scalar_log_resolvent {r : ℝ} (hr : 0 < r) :
    Real.log r = ∫ t in Icc (0 : ℝ) 1, (r-1)/(1+t*(r-1)) := by
  have hden (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) : 1+t*(r-1) ≠ 0 :=
    (affine_pos hr (by simpa only [uIcc_of_le zero_le_one] using ht)).ne'
  have hcont : ContinuousOn (fun t : ℝ => (r-1)/(1+t*(r-1))) (uIcc (0 : ℝ) 1) :=
    continuousOn_const.div (by fun_prop) hden
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => Real.log (1+t*(r-1)))
    (f' := fun t : ℝ => (r-1)/(1+t*(r-1)))
    (fun t ht => by
      have hd := (((hasDerivAt_id t).mul_const (r-1)).const_add 1).log (hden t ht)
      simpa only [one_mul, id_eq] using hd)
    hcont.intervalIntegrable
  simp only [one_mul, zero_mul, add_zero, Real.log_one, sub_zero] at h
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have he : 1+(r-1) = r := by ring
  rw [he] at h
  exact h.symm

/-- The integrated square of the resolvent is the reciprocal scalar.
This is the coefficient appearing after cyclically moving the derivative
inside the trace of the logarithm. -/
theorem scalar_inverse_resolvent_sq {r : ℝ} (hr : 0 < r) :
    r⁻¹ = ∫ t in Icc (0 : ℝ) 1, (1+t*(r-1))⁻¹^2 := by
  have hden (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) : 1+t*(r-1) ≠ 0 :=
    (affine_pos hr (by simpa only [uIcc_of_le zero_le_one] using ht)).ne'
  have hcont : ContinuousOn (fun t : ℝ => (1+t*(r-1))⁻¹^2) (uIcc (0 : ℝ) 1) :=
    ((ContinuousOn.inv₀ (by fun_prop) hden).pow 2)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => t/(1+t*(r-1)))
    (f' := fun t : ℝ => (1+t*(r-1))⁻¹^2)
    (fun t ht => by
      have hd := (hasDerivAt_id t).div
        (((hasDerivAt_id t).mul_const (r-1)).const_add 1) (hden t ht)
      change HasDerivAt (fun y : ℝ => y/(1+y*(r-1))) _ t at hd
      simpa only [id_eq, one_mul, add_sub_cancel_right, one_div, inv_pow] using hd)
    hcont.intervalIntegrable
  have he : 1+(r-1) = r := by ring
  simp only [one_mul, zero_mul, add_zero, zero_div, sub_zero, he, one_div] at h
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  exact h.symm

variable {𝔄 : Type*} [CStarAlgebra 𝔄]

/-- The same representation lifted to actual bounded Hilbert-space operators.
All interchange and integrability hypotheses are proved from positivity of
the compact spectrum; no trace-log identity is assumed. -/
theorem operator_log_resolvent (A : 𝔄) (hA : IsSelfAdjoint A)
    (hpos : ∀ r ∈ spectrum ℝ A, 0 < r) :
    CFC.log A = ∫ t in Icc (0 : ℝ) 1,
      cfc (fun r : ℝ => (r-1)/(1+t*(r-1))) A := by
  let f := fun t r : ℝ => (r-1)/(1+t*(r-1))
  have hc : ContinuousOn (Function.uncurry f) (Icc (0 : ℝ) 1 ×ˢ spectrum ℝ A) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro p hp
    exact (affine_pos (hpos p.2 hp.2) hp.1).ne'
  have hk : IsCompact (Icc (0 : ℝ) 1 ×ˢ spectrum ℝ A) :=
    isCompact_Icc.prod (spectrum.isCompact A)
  obtain ⟨C, hC⟩ := hk.exists_bound_of_continuousOn hc
  have hb : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ∀ r ∈ spectrum ℝ A, ‖f t r‖ ≤ C := by
    apply ae_restrict_of_forall_mem measurableSet_Icc
    intro t ht r hr
    exact hC (t,r) ⟨ht,hr⟩
  have hi := cfc_setIntegral (μ := volume) measurableSet_Icc f (fun _ => C) A hc hb
    (integrable_const C).hasFiniteIntegral hA
  rw [← hi]
  apply cfc_congr
  intro r hr
  exact scalar_log_resolvent (hpos r hr)

/-- The functional-calculus integrand is the literal bounded resolvent
of the affine positive operator. -/
theorem resolvent_integrand_eq (A : 𝔄) (hA : IsSelfAdjoint A)
    (hpos : ∀ r ∈ spectrum ℝ A, 0 < r) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    cfc (fun r : ℝ => (r-1)/(1+t*(r-1))) A =
      (A-1) * Ring.inverse (1+t • (A-1)) := by
  have hn : cfc (fun r : ℝ => r-1) A = A-1 := by
    rw [cfc_sub (fun r : ℝ => r) (fun _ => 1) A, cfc_id' ℝ A, cfc_const_one ℝ A]
  rw [cfc_map_div (fun r : ℝ => r-1) (fun r : ℝ => 1+t*(r-1)) A
    (fun r hr => (affine_pos (hpos r hr) ht).ne'), hn,
    cfc_const_add 1 (fun r : ℝ => t*(r-1)) A,
    cfc_const_mul t (fun r : ℝ => r-1) A, hn, map_one]

/-- A genuine operator resolvent integral for the logarithm. This is the
analytic starting point for proving the tracial logarithmic derivative. -/
theorem operator_log_eq_integral_inverse (A : 𝔄) (hA : IsSelfAdjoint A)
    (hpos : ∀ r ∈ spectrum ℝ A, 0 < r) :
    CFC.log A = ∫ t in Icc (0 : ℝ) 1, (A-1) * Ring.inverse (1+t • (A-1)) := by
  rw [operator_log_resolvent A hA hpos]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact resolvent_integrand_eq A hA hpos ht

/-- The integrated square of the literal affine operator resolvent is
the inverse operator. This identity is what turns the integrated cyclic
trace derivative into `trace(A⁻¹ A')`. -/
theorem operator_inverse_eq_integral_resolvent_sq (A : 𝔄) (hA : IsSelfAdjoint A)
    (hpos : ∀ r ∈ spectrum ℝ A, 0 < r) :
    Ring.inverse A = ∫ t in Icc (0 : ℝ) 1, Ring.inverse (1+t • (A-1))^2 := by
  let f := fun t r : ℝ => (1+t*(r-1))⁻¹^2
  have hc : ContinuousOn (Function.uncurry f) (Icc (0 : ℝ) 1 ×ˢ spectrum ℝ A) := by
    apply ContinuousOn.pow
    apply ContinuousOn.inv₀ (by fun_prop)
    intro p hp
    exact (affine_pos (hpos p.2 hp.2) hp.1).ne'
  have hk : IsCompact (Icc (0 : ℝ) 1 ×ˢ spectrum ℝ A) :=
    isCompact_Icc.prod (spectrum.isCompact A)
  obtain ⟨C, hC⟩ := hk.exists_bound_of_continuousOn hc
  have hb : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ∀ r ∈ spectrum ℝ A, ‖f t r‖ ≤ C := by
    apply ae_restrict_of_forall_mem measurableSet_Icc
    intro t ht r hr
    exact hC (t,r) ⟨ht,hr⟩
  have hi := cfc_setIntegral (μ := volume) measurableSet_Icc f (fun _ => C) A hc hb
    (integrable_const C).hasFiniteIntegral hA
  have hunit : IsUnit A := spectrum.isUnit_of_zero_notMem (R := ℝ)
    (fun hz => (lt_irrefl (0 : ℝ)) (hpos 0 hz))
  have he : cfc (fun r : ℝ => r⁻¹) A =
      cfc (fun r => ∫ t in Icc (0 : ℝ) 1, f t r) A := by
    apply cfc_congr
    intro r hr
    exact scalar_inverse_resolvent_sq (hpos r hr)
  rw [cfc_ringInverse_id A hunit hA] at he
  rw [he, hi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hn : cfc (fun r : ℝ => r-1) A = A-1 := by
    rw [cfc_sub (fun r : ℝ => r) (fun _ => 1) A, cfc_id' ℝ A, cfc_const_one ℝ A]
  have hcinv : ContinuousOn (fun r : ℝ => (1+t*(r-1))⁻¹) (spectrum ℝ A) :=
    ContinuousOn.inv₀ (by fun_prop) (fun r hr => (affine_pos (hpos r hr) ht).ne')
  dsimp [f]
  rw [cfc_pow (fun r : ℝ => (1+t*(r-1))⁻¹) 2 A hcinv hA,
    cfc_inv (fun r : ℝ => 1+t*(r-1)) A (fun r hr => (affine_pos (hpos r hr) ht).ne'),
    cfc_const_add 1 (fun r : ℝ => t*(r-1)) A,
    cfc_const_mul t (fun r : ℝ => r-1) A, hn, map_one]

#print axioms affine_pos
#print axioms scalar_log_resolvent
#print axioms scalar_inverse_resolvent_sq
#print axioms operator_log_resolvent
#print axioms resolvent_integrand_eq
#print axioms operator_log_eq_integral_inverse
#print axioms operator_inverse_eq_integral_resolvent_sq

end QuantitativeSpectralLogResolvent
