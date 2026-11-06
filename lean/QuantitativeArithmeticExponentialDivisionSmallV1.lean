module
public import QuantitativeArithmeticExponentialDivisionLocalV1
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

theorem small_circle_lower (ρ : ℝ) (hρ : 0<ρ) (hρ1 : ρ≤1) :
    ∃ δ : ℝ,0<δ ∧ ∀ w : ℂ,‖w‖=ρ → δ≤‖1-exp w‖ := by
  have hn : (sphere (0:ℂ) ρ).Nonempty := ⟨(ρ:ℂ),by simp [hρ.le]⟩
  have hc : Continuous (fun w : ℂ => ‖1-exp w‖) := by fun_prop
  obtain ⟨w,hw,hmin⟩ := (isCompact_sphere (0:ℂ) ρ).exists_isMinOn hn hc.continuousOn
  have hw' : ‖w‖=ρ := by simpa only [mem_sphere,dist_zero_right] using hw
  have hne : 1-exp w≠0 := by
    intro h
    have he : exp w=exp 0 := by simpa only [exp_zero] using (sub_eq_zero.mp h).symm
    have hw0 : w=0 := exp_inj_of_neg_pi_lt_of_le_pi (x:=w) (y:=0)
      (by have ht := (abs_le.mp (abs_im_le_norm w)).1; linarith [Real.two_le_pi])
      (by linarith [im_le_norm w,Real.two_le_pi])
      (by simpa using (neg_neg_of_pos Real.pi_pos))
      (by simpa using Real.pi_pos.le) he
    simp [hw0] at hw'
    linarith
  refine ⟨‖1-exp w‖,norm_pos_iff.mpr hne,?_⟩
  intro v hv
  exact hmin (by simpa only [mem_sphere,dist_zero_right] using hv)

theorem small_nearby_zero (a c z : ℂ) (ha : a≠0) (ε : ℝ) (hε : ε≤1/4)
    (hsmall : ‖1-c*exp (a*z)‖≤ε) :
    ∃ w : ℂ,c*exp (a*w)=1 ∧ ‖z-w‖≤(3/2*ε)/‖a‖ := by
  let h : ℂ := c*exp (a*z)
  have hnorm : ‖h-1‖≤ε := by simpa only [h,norm_sub_rev] using hsmall
  have hh : h≠0 := by
    intro hz
    norm_num [hz] at hnorm
    linarith
  have hlog : ‖log h‖≤3/2*ε := by
    have ht := norm_log_one_add_half_le_self (z:=h-1) (by linarith)
    simp only [add_sub_cancel] at ht
    linarith
  refine ⟨z-log h/a,?_,?_⟩
  · rw [show a*(z-log h/a)=a*z-log h by field_simp,
      exp_sub,← mul_div_assoc,exp_log hh]
    exact div_self hh
  · rw [show z-(z-log h/a)=log h/a by ring,norm_div]
    exact div_le_div_of_nonneg_right hlog (norm_nonneg a)

/-- Division by an exponential factor has a local uniform sup-norm estimate,
including at its zeros. The constants depend only on the exponential rate. -/
theorem small_local_envelope (a : ℂ) (ha : a≠0) (r : ℝ) (hr : 0<r) (har : ‖a‖*r≤1) :
    ∃ K : ℝ, 0<K ∧ ∀ (c : ℂ) (A G : ℂ → ℂ),
      Differentiable ℂ G →
      (∀ z : ℂ,(1-c*exp (a*z))*G z=A z) →
      ∀ (z : ℂ) (M : ℝ), 0≤M →
      (∀ v : ℂ,‖v-z‖≤2*r → ‖A v‖≤M) → ‖G z‖≤K*M := by
  have ha' : 0<‖a‖ := norm_pos_iff.mpr ha
  obtain ⟨δ,hδ,hcircle⟩ := small_circle_lower (‖a‖*r) (mul_pos ha' hr) har
  let ε : ℝ := min (1/4) (‖a‖*r/4)
  have hε : 0<ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε≤1/4 := min_le_left _ _
  have hεr : ε≤‖a‖*r/4 := min_le_right _ _
  let K : ℝ := ε⁻¹+δ⁻¹
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  intro c A G hG hAG z M hM hbound
  by_cases hz : ‖1-c*exp (a*z)‖≤ε
  · obtain ⟨w,hw,hzw⟩ := small_nearby_zero a c z ha ε hε1 hz
    have hzw' : ‖z-w‖<r := by
      have hh : (3/2*ε)/‖a‖≤(3/8)*r := by
        apply (div_le_iff₀ ha').mpr
        nlinarith
      linarith [hzw.trans hh]
    have hsphere : ∀ v∈frontier (ball w r),‖G v‖≤K*M := by
      intro v hv
      have hv' : ‖v-w‖=r := by
        simpa only [mem_sphere,dist_eq_norm] using frontier_ball_subset_sphere hv
      have hunit : ‖a*(v-w)‖=‖a‖*r := by rw [norm_mul,hv']
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
        _ ≤ K*M := mul_le_mul_of_nonneg_right (by dsimp [K]; linarith [inv_pos.mpr hε]) hM
    exact norm_le_of_forall_mem_frontier_norm_le isBounded_ball hG.diffContOnCl hsphere
      (subset_closure (by simpa only [mem_ball,dist_eq_norm] using hzw'))
  · have hd : ε≤‖1-c*exp (a*z)‖ := le_of_lt (lt_of_not_ge hz)
    calc
      ‖G z‖≤ε⁻¹*‖A z‖ := quotient_norm hε (hAG z) hd
      _ ≤ ε⁻¹*M := mul_le_mul_of_nonneg_left (hbound z (by simp; positivity)) (inv_nonneg.mpr hε.le)
      _ ≤ K*M := mul_le_mul_of_nonneg_right (by dsimp [K]; linarith [inv_pos.mpr hδ]) hM

#print axioms small_local_envelope
end QuantitativeArithmeticExponentialDivision
