module

public import QuantitativeMaassWindowVariationGrowthV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- All propagation dependence in the explicit variation majorant is at most
one exponential times a polynomial, uniformly before choosing R(t). -/
theorem window_variation_radius_majorant (B R t : ℝ) (hB : 0<B) (hR : 1≤R) (ht : 1≤t) :
    (Real.cosh (B*R)+1)^2+t*Real.sqrt t*(Real.sqrt (B*R)+1)≤
      (B+6)*R*t*Real.sqrt t*Real.exp (2*B*R) := by
  have hBR : 0≤B*R := by positivity
  have he1 : 1≤Real.exp (B*R) := Real.one_le_exp_iff.mpr hBR
  have he2 : 1≤Real.exp (2*B*R) := Real.one_le_exp_iff.mpr (by positivity)
  have hcosh : Real.cosh (B*R)≤Real.exp (B*R) := by
    rw [Real.cosh_eq]
    have hh : Real.exp (-(B*R))≤Real.exp (B*R) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hexp : (Real.exp (B*R))^2=Real.exp (2*B*R) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have hfirst : (Real.cosh (B*R)+1)^2≤4*Real.exp (2*B*R) := by
    have hh := pow_le_pow_left₀ (by positivity : 0≤Real.cosh (B*R)+1)
      (by linarith : Real.cosh (B*R)+1≤2*Real.exp (B*R)) 2
    nlinarith [hexp]
  have hsqrt : Real.sqrt (B*R)+1≤(B+2)*R := by
    have hs := Real.sq_sqrt hBR
    have hn := sq_nonneg (Real.sqrt (B*R)-1)
    nlinarith
  have hst : 1≤Real.sqrt t := Real.one_le_sqrt.mpr ht
  have hF : 1≤R*t*Real.sqrt t := by
    calc
      (1:ℝ)=1*1*1 := by ring
      _ ≤ R*t*Real.sqrt t := by gcongr
  have hsecond := mul_le_mul_of_nonneg_left hsqrt (show 0≤t*Real.sqrt t by positivity)
  have hm1 := mul_le_mul_of_nonneg_right hF (Real.exp_pos (2*B*R)).le
  have hm2 := mul_le_mul_of_nonneg_left he2 (show 0≤(B+2)*(R*t*Real.sqrt t) by positivity)
  nlinarith

/-- Explicit uniform O(R^3 epsilon^2 t^(3/2) exp(CR)) total variation for the
actual window profile. No smoothness or transform estimate is assumed. -/
theorem windowTimeSquareProfile_variation_exponential (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ C D : ℝ,0<C ∧ 0<D ∧ ∀ R : ℝ,∀ hR : 1≤R,∀ ε : ℝ,0≤ε → ε≤1 →
      ∀ t : ℝ,1≤t →
      (∫ v : ℝ,‖deriv (parabolicLineProfile (windowTimeSquareProfile K hc R
        (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε)) 1) v‖)≤
        D*R^3*ε^2*t*Real.sqrt t*Real.exp (C*R) := by
  obtain ⟨B,D,hB,hD,hbound⟩ := windowTimeSquareProfile_variation_growth K he hc
  refine ⟨2*B,D*(B+6),by positivity,by positivity,?_⟩
  intro R hR ε hε hε1 t ht
  apply (hbound R hR ε hε hε1 t ht).trans
  have hh := mul_le_mul_of_nonneg_left (window_variation_radius_majorant B R t hB hR ht)
    (show 0≤D*R^2*ε^2 by positivity)
  convert hh using 1
  ring

#print axioms window_variation_radius_majorant
#print axioms windowTimeSquareProfile_variation_exponential

end QuantitativeMaass
