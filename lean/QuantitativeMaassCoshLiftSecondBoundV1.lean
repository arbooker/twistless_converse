module

public import QuantitativeMaassEvenRadialBoundsV1
public import QuantitativeMaassHyperbolicSmallRadiusV1
public import QuantitativeMaassAbelRadialDerivativeV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The apparent singularities in the second cosh-lift derivative cancel by
evenness. The resulting bound uses only second and fourth time derivatives. -/
theorem evenCoshLift_second_bound (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f) (M2 M4 : ℝ)
    (hM2 : 0≤M2) (hM4 : 0≤M4)
    (hb2 : ∀ u,‖deriv (deriv f) u‖≤M2)
    (hb4 : ∀ u,‖deriv (deriv (deriv (deriv f))) u‖≤M4) (u : ℝ) (hu : 0<u) :
    ‖deriv (deriv (evenCoshLift f)) (Real.cosh u)‖≤M4+M2*Real.cosh u := by
  let E := evenRadialDerivative f
  have hE : ContDiff ℝ ∞ E := evenRadialDerivative_smooth f hf hc
  have hfun : (fun x : ℝ => (x:ℂ)*E x)=deriv f := by
    funext x
    simpa only [Complex.real_smul] using evenRadialDerivative_identity f hf he x
  have hfirst : deriv f u=(u:ℂ)*E u := congrFun hfun.symm u
  have hder := ((hasDerivAt_id u).ofReal_comp.mul
    ((hE.differentiable (by simp)).differentiableAt.hasDerivAt)).deriv
  simp only [id_eq,Complex.ofReal_one,one_mul] at hder
  change deriv (fun x : ℝ => (x:ℂ)*E x) u=E u+(u:ℂ)*deriv E u at hder
  rw [hfun] at hder
  have hs := Real.sinh_pos_iff.mpr hu
  have hsle := Real.self_le_sinh_iff.mpr hu.le
  have hsn : (Real.sinh u:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have heq : deriv (deriv (evenCoshLift f)) (Real.cosh u)=
      E u*((Real.sinh u-u*Real.cosh u)/(Real.sinh u)^3:ℝ)+
        deriv E u*(u/(Real.sinh u)^2:ℝ) := by
    rw [evenCoshLift_second_deriv_cosh f hf he hc u hu,hder,hfirst]
    simp only [Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_pow]
    field_simp
    ring
  have hcancel := sinh_cosh_cancellation u hu.le
  have hpow : u^3≤(Real.sinh u)^3 := pow_le_pow_left₀ hu.le hsle 3
  have hfrac1 : (u*Real.cosh u-Real.sinh u)/(Real.sinh u)^3≤Real.cosh u := by
    apply (div_le_iff₀ (pow_pos hs 3)).mpr
    exact hcancel.2.trans (by nlinarith [mul_le_mul_of_nonneg_right hpow (Real.cosh_pos u).le])
  have hfrac2 : u*(u/(Real.sinh u)^2)≤1 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (pow_pos hs 2)).mpr
    nlinarith [pow_le_pow_left₀ hu.le hsle 2]
  have hb := evenRadialDerivative_bounds f hf he hc M2 M4 hM2 hM4 hb2 hb4 u hu.le
  rw [heq]
  calc
    _ ≤ ‖E u*((Real.sinh u-u*Real.cosh u)/(Real.sinh u)^3:ℝ)‖+
        ‖deriv E u*(u/(Real.sinh u)^2:ℝ)‖ := norm_add_le _ _
    _ = ‖E u‖*((u*Real.cosh u-Real.sinh u)/(Real.sinh u)^3)+
        ‖deriv E u‖*(u/(Real.sinh u)^2) := by
      rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith [hcancel.1]) (by positivity)),
        abs_of_nonneg (by positivity : 0≤u/(Real.sinh u)^2)]
      ring
    _ ≤ M2*Real.cosh u+(u*M4)*(u/(Real.sinh u)^2) := add_le_add
      (mul_le_mul hb.1 hfrac1 (div_nonneg hcancel.1 (by positivity)) hM2)
      (mul_le_mul_of_nonneg_right hb.2 (by positivity))
    _ ≤ M4+M2*Real.cosh u := by nlinarith [mul_le_mul_of_nonneg_left hfrac2 hM4]

/-- Uniform physical second-derivative bound from support and time derivatives. -/
theorem evenCoshLift_second_bound_physical (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f) (L M2 M4 : ℝ) (hL : 0≤L)
    (hs : Function.support f⊆Icc (-L) L) (hM2 : 0≤M2) (hM4 : 0≤M4)
    (hb2 : ∀ u,‖deriv (deriv f) u‖≤M2)
    (hb4 : ∀ u,‖deriv (deriv (deriv (deriv f))) u‖≤M4) :
    ∀ q,1<q → ‖deriv (deriv (evenCoshLift f)) q‖≤M4+M2*Real.cosh L := by
  have hsF := evenCoshLift_support_of_time_support f L hL hs
  have hsD : Function.support (deriv (evenCoshLift f))⊆Iic (Real.cosh L) :=
    support_deriv_subset.trans (closure_minimal hsF isClosed_Iic)
  have hsDD : Function.support (deriv (deriv (evenCoshLift f)))⊆Iic (Real.cosh L) :=
    support_deriv_subset.trans (closure_minimal hsD isClosed_Iic)
  intro q hq
  by_cases hqL : q≤Real.cosh L
  · have hu : 0<Real.arcosh q := Real.arcosh_pos hq
    have hh := evenCoshLift_second_bound f hf he hc M2 M4 hM2 hM4 hb2 hb4 (Real.arcosh q) hu
    rw [Real.cosh_arcosh hq.le] at hh
    exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hqL hM2))
  · have hz : deriv (deriv (evenCoshLift f)) q=0 := by
      by_contra hn
      exact hqL (hsDD hn)
    rw [hz,norm_zero]
    positivity

#print axioms evenCoshLift_second_bound
#print axioms evenCoshLift_second_bound_physical

end QuantitativeMaass
