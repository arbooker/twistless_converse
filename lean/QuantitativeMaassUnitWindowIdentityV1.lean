module

public import QuantitativeMaassWindowIdentityTermV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- The fixed enlarged unit-window identity term is at most linear in its
centre. Its constant is chosen before that centre. -/
theorem windowIdentityContribution_unit_bound (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (R : ℝ) (hR : 0<R) :
    ∃ C : ℝ,0<C ∧ ∀ t : ℝ,1≤t →
      (windowIdentityContribution K hc R hR (t-3/4) (t+3/4)).re≤C*t := by
  let m₁ := ∫ u,|u| * K u
  let m₂ := ∫ u,|u|^2*K u
  have hm₁ : 0≤m₁ := integral_nonneg (fun u => mul_nonneg (abs_nonneg _) (hK u))
  have hm₂ : 0≤m₂ := integral_nonneg (fun u => mul_nonneg (sq_nonneg _) (hK u))
  refine ⟨(6+24*m₁/R+8*m₂/R^2)/(4*Real.pi),by positivity,?_⟩
  intro t ht
  have hb := windowIdentityContribution_error K he hc hK hm R hR
    (t-3/4) (t+3/4) (by linarith) (by linarith)
  have hb' : ‖((4*Real.pi:ℝ):ℂ)*windowIdentityContribution K hc R hR (t-3/4) (t+3/4)-
      (((t+3/4)^2-(t-3/4)^2:ℝ):ℂ)‖≤
      8*(1+(t+3/4))*m₁/R+8*m₂/R^2+2*((t+3/4)-(t-3/4)) := by
    simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using hb
  have hr := (Complex.re_le_norm (((4*Real.pi:ℝ):ℂ)*
    windowIdentityContribution K hc R hR (t-3/4) (t+3/4)-(((t+3/4)^2-(t-3/4)^2:ℝ):ℂ))).trans hb'
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at hr
  have hlin : 8*(1+(t+3/4))*m₁/R≤24*t*m₁/R := by
    apply div_le_div_of_nonneg_right _ hR.le
    exact mul_le_mul_of_nonneg_right (by linarith : 8*(1+(t+3/4))≤24*t) hm₁
  have hquad : 8*m₂/R^2≤t*(8*m₂/R^2) :=
    le_mul_of_one_le_left (by positivity) ht
  have heq : ((6+24*m₁/R+8*m₂/R^2)/(4*Real.pi))*t=
      ((6+24*m₁/R+8*m₂/R^2)*t)/(4*Real.pi) := by ring
  rw [heq]
  apply (le_div_iff₀ (by positivity : 0<4*Real.pi)).mpr
  rw [show 24*t*m₁/R=t*(24*m₁/R) by ring] at hlin
  nlinarith only [hr,hlin,hquad,ht]

#print axioms windowIdentityContribution_unit_bound

end QuantitativeMaass
