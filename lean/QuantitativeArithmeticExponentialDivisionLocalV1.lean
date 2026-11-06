module
public import QuantitativeArithmeticQuadraticTwistQuotientGeometryV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticExponentialDivision
open Complex Set Metric QuantitativeArithmeticQuadraticTwistQuotient

private theorem quotient_norm {x y b : ℂ} {δ : ℝ} (hδ : 0<δ)
    (hxy : x*y=b) (hx : δ≤‖x‖) : ‖y‖≤δ⁻¹*‖b‖ := by
  have hn := congrArg norm hxy
  rw [norm_mul] at hn
  rw [inv_mul_eq_div,le_div_iff₀ hδ]
  nlinarith [norm_nonneg y]

/-- Division by an exponential factor has a local uniform sup-norm estimate,
including at its zeros. The constants depend only on the exponential rate. -/
theorem local_envelope (a : ℂ) (ha : a≠0) :
    ∃ K R : ℝ, 0<K ∧ 0<R ∧ ∀ (c : ℂ) (A G : ℂ → ℂ),
      Differentiable ℂ G →
      (∀ z : ℂ,(1-c*exp (a*z))*G z=A z) →
      ∀ (z : ℂ) (M : ℝ), 0≤M →
      (∀ v : ℂ,‖v-z‖≤R → ‖A v‖≤M) → ‖G z‖≤K*M := by
  obtain ⟨δ,hδ,hcircle⟩ := exponential_circle_lower
  let r : ℝ := ‖a‖⁻¹
  have ha' : 0<‖a‖ := norm_pos_iff.mpr ha
  have hr : 0<r := inv_pos.mpr ha'
  let K : ℝ := 4+δ⁻¹
  refine ⟨K,2*r,by dsimp [K]; positivity,by positivity,?_⟩
  intro c A G hG hAG z M hM hbound
  by_cases hz : ‖1-c*exp (a*z)‖≤1/4
  · obtain ⟨w,hw,hzw⟩ := nearby_zero a c z ha hz
    have hzw' : ‖z-w‖<r := by
      change ‖z-w‖≤(3/8)/‖a‖ at hzw
      rw [div_eq_mul_inv] at hzw
      change ‖z-w‖≤(3/8)*r at hzw
      linarith
    have hsphere : ∀ v∈frontier (ball w r),‖G v‖≤K*M := by
      intro v hv
      have hv' : ‖v-w‖=r := by
        simpa only [mem_sphere,dist_eq_norm] using frontier_ball_subset_sphere hv
      have hunit : ‖a*(v-w)‖=1 := by
        rw [norm_mul,hv']
        exact mul_inv_cancel₀ ha'.ne'
      have hd : δ≤‖1-c*exp (a*v)‖ := by
        rw [denominator_at_zero a c w v hw]
        exact hcircle _ hunit
      have hvz : ‖v-z‖≤2*r := by
        have ht := norm_add_le (v-w) (w-z)
        have hwz : ‖w-z‖<r := by simpa only [norm_sub_rev] using hzw'
        rw [sub_add_sub_cancel] at ht
        linarith
      calc
        ‖G v‖≤δ⁻¹*‖A v‖ := quotient_norm hδ (hAG v) hd
        _ ≤ δ⁻¹*M := mul_le_mul_of_nonneg_left (hbound v hvz) (inv_nonneg.mpr hδ.le)
        _ ≤ K*M := mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) hM
    exact norm_le_of_forall_mem_frontier_norm_le isBounded_ball hG.diffContOnCl hsphere
      (subset_closure (by simpa only [mem_ball,dist_eq_norm] using hzw'))
  · have hd : (1/4:ℝ)≤‖1-c*exp (a*z)‖ := le_of_lt (lt_of_not_ge hz)
    calc
      ‖G z‖≤(1/4:ℝ)⁻¹*‖A z‖ := quotient_norm (by norm_num) (hAG z) hd
      _ ≤ 4*M := by
        norm_num only [one_div,inv_inv]
        exact mul_le_mul_of_nonneg_left (hbound z (by simp; positivity)) (by norm_num)
      _ ≤ K*M := mul_le_mul_of_nonneg_right (by dsimp [K]; linarith [inv_pos.mpr hδ]) hM

/-- The local estimate preserves polynomial vertical growth after a fixed
strip enlargement; no bound on the quotient is assumed. -/
theorem polynomial_strip (a : ℂ) (ha : a≠0) :
    ∃ K R : ℝ,0<K ∧ 0<R ∧ ∀ (c : ℂ) (A G : ℂ → ℂ),
      Differentiable ℂ G → (∀ z : ℂ,(1-c*exp (a*z))*G z=A z) →
      ∀ (l u C : ℝ) (d : ℕ),0≤C →
      (∀ z : ℂ,l-R≤z.re → z.re≤u+R → ‖A z‖≤C*(1+‖z‖)^d) →
      ∀ z : ℂ,l≤z.re → z.re≤u → ‖G z‖≤(K*C*(1+R)^d)*(1+‖z‖)^d := by
  obtain ⟨K,R,hK,hR,hlocal⟩ := local_envelope a ha
  refine ⟨K,R,hK,hR,?_⟩
  intro c A G hG hAG l u C d hC hA z hzl hzu
  have hb : ∀ v : ℂ,‖v-z‖≤R → ‖A v‖≤C*(1+R)^d*(1+‖z‖)^d := by
    intro v hv
    have hvre : |v.re-z.re|≤R := by
      simpa only [Complex.sub_re] using (abs_re_le_norm (v-z)).trans hv
    have hnorm : ‖v‖≤‖z‖+R := by
      have ht := norm_add_le (v-z) z
      rw [sub_add_cancel] at ht
      linarith
    calc
      ‖A v‖≤C*(1+‖v‖)^d := hA v (by linarith [(abs_le.mp hvre).1]) (by linarith [(abs_le.mp hvre).2])
      _ ≤ C*((1+R)*(1+‖z‖))^d := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply pow_le_pow_left₀ (by positivity)
        nlinarith [norm_nonneg z]
      _ = C*(1+R)^d*(1+‖z‖)^d := by rw [mul_pow]; ring
  have hh := hlocal c A G hG hAG z (C*(1+R)^d*(1+‖z‖)^d) (by positivity) hb
  convert hh using 1
  ring
#print axioms local_envelope
#print axioms polynomial_strip
end QuantitativeArithmeticExponentialDivision
