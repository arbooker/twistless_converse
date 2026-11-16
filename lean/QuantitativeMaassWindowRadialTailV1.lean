module

public import QuantitativeMaassWindowRadialDerivativeV1
public import QuantitativeMaassRadialWeightIntegralV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- The physical radial window profile is smooth across radius zero. -/
theorem windowTimeSquareProfile_cosh_smooth (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) :
    ContDiff ℝ ∞ (fun r => windowTimeSquareProfile K hc R hR a b (Real.cosh r)) := by
  apply ContDiffOn.comp_contDiff (windowTimeSquareProfile_smoothOn K he hc R hR a b)
    (by fun_prop)
  exact fun r => Real.one_le_cosh r

/-- Quantitative variation outside an arbitrary positive radial cutoff. -/
theorem windowTimeSquareProfile_radial_tail (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ C : ℝ,0<C ∧ ∀ R : ℝ,∀ hR : 1≤R,∀ ε : ℝ,0≤ε → ε≤1 →
      ∀ t : ℝ,1≤t → ∀ δ L : ℝ,0<δ → δ≤L →
      (∫ r in δ..L,‖deriv (fun r => windowTimeSquareProfile K hc R (lt_of_lt_of_le zero_lt_one hR)
        (t-ε) (t+ε) (Real.cosh r)) r‖)≤
        C*R^2*ε^2*Real.sqrt t*(t*Real.sqrt L+1/Real.sqrt δ) := by
  obtain ⟨D,hD,hbound⟩ := windowTimeSquareProfile_radial_derivative_bound K he hc
  refine ⟨2*D,by positivity,?_⟩
  intro R hR ε hε hε1 t ht δ L hδ hL
  have ht0 : 0<t := lt_of_lt_of_le zero_lt_one ht
  have hreg := windowTimeSquareProfile_cosh_smooth K he hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε)
  have hi := ((contDiff_infty_iff_deriv.mp hreg).2.continuous.norm).intervalIntegrable (μ:=volume) δ L
  let p : ℝ → ℝ := fun r => (Real.sqrt (Real.sinh r))⁻¹
  let q : ℝ → ℝ := fun r => Real.cosh r/(Real.sinh r*Real.sqrt (Real.sinh r))
  have hp := inverse_sqrt_sinh_integral δ L hδ hL
  have hq := cosh_inverse_sinh_sqrt_integral δ L hδ hL
  have hqi := cosh_inverse_sinh_sqrt_bound δ L hδ hL
  have hmajor : IntervalIntegrable (fun r => D*R^2*ε^2*(t*Real.sqrt t*p r+Real.sqrt t*q r)) volume δ L :=
    ((hp.1.const_mul (t*Real.sqrt t)).add (hq.1.const_mul (Real.sqrt t))).const_mul _
  have hb := intervalIntegral.integral_mono_on hL hi hmajor (fun r hr => by
    convert hbound R hR ε hε hε1 t ht r (hδ.trans_le hr.1) using 1
    dsimp only [p,q]
    ring)
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hp.1.const_mul (t*Real.sqrt t)) (hq.1.const_mul (Real.sqrt t)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hb
  apply hb.trans
  have hm : 0≤D*R^2*ε^2 := by positivity
  have hh := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hp.2 (by positivity : 0≤t*Real.sqrt t))
      (mul_le_mul_of_nonneg_left hqi (Real.sqrt_nonneg t))) hm
  convert hh using 1
  ring

/-- The inverse-square spectral cutoff keeps the complete outer variation at
the t^(3/2) scale, with only polynomial dependence on the support radius. -/
theorem windowTimeSquareProfile_inverse_square_tail (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ C : ℝ,0<C ∧ ∀ R : ℝ,∀ hR : 1≤R,∀ ε : ℝ,0≤ε → ε≤1 →
      ∀ t : ℝ,1≤t → ∀ L : ℝ,1≤L →
      (∫ r in (1/t)^2..L,‖deriv (fun r => windowTimeSquareProfile K hc R (lt_of_lt_of_le zero_lt_one hR)
        (t-ε) (t+ε) (Real.cosh r)) r‖)≤
        C*R^2*ε^2*t*Real.sqrt t*(Real.sqrt L+1) := by
  obtain ⟨C,hC,hbound⟩ := windowTimeSquareProfile_radial_tail K he hc
  refine ⟨C,hC,?_⟩
  intro R hR ε hε hε1 t ht L hL
  have ht0 : 0<t := lt_of_lt_of_le zero_lt_one ht
  have hti : 0<1/t := one_div_pos.mpr ht0
  have hti1 : 1/t≤1 := (div_le_one ht0).mpr ht
  have hδL : (1/t)^2≤L := (by nlinarith : (1/t)^2≤1).trans hL
  have hh := hbound R hR ε hε hε1 t ht ((1/t)^2) L (sq_pos_of_pos hti) hδL
  rw [Real.sqrt_sq hti.le,one_div_one_div] at hh
  convert hh using 1
  ring

#print axioms windowTimeSquareProfile_cosh_smooth
#print axioms windowTimeSquareProfile_radial_tail
#print axioms windowTimeSquareProfile_inverse_square_tail

end QuantitativeMaass
