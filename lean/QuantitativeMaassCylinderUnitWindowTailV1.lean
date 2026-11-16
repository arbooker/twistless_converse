module

public import QuantitativeMaassCylinderSharpTraceV1
public import QuantitativeMaassUnitWindowIdentityV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology FourierTransform SchwartzMap ENNReal

namespace QuantitativeMaass

/-- The unit-window diagonal bound is uniform in every smoothing scale R
at least one, as well as in the window centre. -/
theorem windowIdentityContribution_unit_uniform_bound (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) :
    ∃ C : ℝ,0<C ∧ ∀ (R : ℝ) (hR : 0<R),1≤R → ∀ t : ℝ,1≤t →
      (windowIdentityContribution K hc R hR (t-3/4) (t+3/4)).re≤C*t := by
  let m₁ := ∫ u,|u| * K u
  let m₂ := ∫ u,|u|^2*K u
  have hm₁ : 0≤m₁ := integral_nonneg (fun u => mul_nonneg (abs_nonneg _) (hK u))
  have hm₂ : 0≤m₂ := integral_nonneg (fun u => mul_nonneg (sq_nonneg _) (hK u))
  refine ⟨(6+24*m₁+8*m₂)/(4*Real.pi),by positivity,?_⟩
  intro R hR hR1 t ht
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
  have hlin : 8*(1+(t+3/4))*m₁/R≤24*t*m₁ := by
    calc
      _≤8*(1+(t+3/4))*m₁ := div_le_self (by positivity) hR1
      _≤_ := mul_le_mul_of_nonneg_right (by linarith) hm₁
  have hquad : 8*m₂/R^2≤t*(8*m₂) := by
    calc
      _≤8*m₂ := div_le_self (by positivity) (by nlinarith)
      _≤_ := le_mul_of_one_le_left (by positivity) ht
  rw [show ((6+24*m₁+8*m₂)/(4*Real.pi))*t=
    ((6+24*m₁+8*m₂)*t)/(4*Real.pi) by ring]
  apply (le_div_iff₀ (by positivity : 0<4*Real.pi)).mpr
  nlinarith only [hr,hlin,hquad,ht]

/-- The actual centered cylinder column for the symmetric window packet. -/
def cylinderWindowCenteredColumn (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R : ℝ) (hR : 0<R) (a b : ℝ) :=
  cylinderCenteredTimeColumn (windowTimeSchwartz K hc R hR a b)
    (symmetricWindowTimeTest_compact K hc R a b hR) (symmetricWindowTimeTest_even K he R a b)
    ((symmetricWindowTimeTest_uniform_support K hc).choose*R)
    (mul_nonneg (symmetricWindowTimeTest_uniform_support K hc).choose_spec.1.le hR.le)
    ((symmetricWindowTimeTest_uniform_support K hc).choose_spec.2 R hR a b)

/-- Exact diagonal/H bound for the actual centered window column. -/
theorem cylinderWindowCenteredColumn_tail (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R : ℝ) (hR : 0<R) (a b H : ℝ) (hH : 0<H) :
    (∫⁻ z in AsymptoticHyperbolicArea.closedTerminal H,
      ENNReal.ofReal (‖cylinderWindowCenteredColumn K he hc R hR a b z‖^2))≤
      ENNReal.ofReal H⁻¹*ENNReal.ofReal (windowIdentityContribution K hc R hR a b).re :=
  cylinderTimeColumn_centered_sharp_tail (windowTimeSchwartz K hc R hR a b)
    (symmetricWindowTimeTest_compact K hc R a b hR) (symmetricWindowTimeTest_even K he R a b)
    (symmetricWindowTimeTest_real K he R a b)
    ((symmetricWindowTimeTest_uniform_support K hc).choose*R)
    (mul_nonneg (symmetricWindowTimeTest_uniform_support K hc).choose_spec.1.le hR.le)
    ((symmetricWindowTimeTest_uniform_support K hc).choose_spec.2 R hR a b) H hH

/-- The genuine nonzero-cylinder unit-window cusp energy is O(t/H),
uniformly in H, the window centre, and every smoothing scale at least one. -/
theorem cylinderWindowCenteredColumn_unit_tail (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) :
    ∃ C : ℝ,0<C ∧ ∀ (R : ℝ) (hR : 0<R),1≤R → ∀ t : ℝ,1≤t → ∀ H : ℝ,0<H →
      (∫⁻ z in AsymptoticHyperbolicArea.closedTerminal H,
        ENNReal.ofReal (‖cylinderWindowCenteredColumn K he hc R hR (t-3/4) (t+3/4) z‖^2))≤
        ENNReal.ofReal (C*t/H) := by
  obtain ⟨C,hC,hb⟩ := windowIdentityContribution_unit_uniform_bound K he hc hK hm
  refine ⟨C,hC,?_⟩
  intro R hR hR1 t ht H hH
  calc
    _≤ENNReal.ofReal H⁻¹*ENNReal.ofReal
        (windowIdentityContribution K hc R hR (t-3/4) (t+3/4)).re :=
      cylinderWindowCenteredColumn_tail K he hc R hR _ _ H hH
    _≤ENNReal.ofReal H⁻¹*ENNReal.ofReal (C*t) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hb R hR hR1 t ht))
    _=_ := by rw [←ENNReal.ofReal_mul (inv_nonneg.mpr hH.le)]; congr 1; ring

#print axioms windowIdentityContribution_unit_uniform_bound
#print axioms cylinderWindowCenteredColumn_tail
#print axioms cylinderWindowCenteredColumn_unit_tail

end QuantitativeMaass
