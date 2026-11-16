module

public import QuantitativeMaassParityErrorV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- Explicit normalized identity error for the literal interval, with constants
chosen before its centre, width and propagation radius. -/
theorem windowIdentityContribution_interval_bound (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (R : ℝ) (hR : 0<R) (hR1 : 1≤R) (t ε : ℝ) (ht : 1≤t) (hε : 0<ε) (hε1 : ε≤1) :
    ‖(4*Real.pi:ℂ)*windowIdentityContribution K hc R hR t (t+ε)-((2*t*ε:ℝ):ℂ)‖/(t*ε) ≤
      (24*(∫ u,|u| * K u)+8*(∫ u,|u|^2*K u))/(R*ε)+3/t := by
  let m₁ := ∫ u,|u| * K u
  let m₂ := ∫ u,|u|^2*K u
  have hm₁ : 0≤m₁ := integral_nonneg (fun u => mul_nonneg (abs_nonneg _) (hK u))
  have hm₂ : 0≤m₂ := integral_nonneg (fun u => mul_nonneg (sq_nonneg _) (hK u))
  have ht0 : 0<t := lt_of_lt_of_le zero_lt_one ht
  have hmass := windowIdentityContribution_error K he hc hK hm R hR t (t+ε) ht0 (by linarith)
  have hdiff : ‖(((t+ε)^2-t^2:ℝ):ℂ)-((2*t*ε:ℝ):ℂ)‖=ε^2 := by
    rw [← Complex.ofReal_sub,show (t+ε)^2-t^2-2*t*ε=ε^2 by ring,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ε)]
  have htri := dist_triangle ((4*Real.pi:ℂ)*windowIdentityContribution K hc R hR t (t+ε))
    (((t+ε)^2-t^2:ℝ):ℂ) ((2*t*ε:ℝ):ℂ)
  simp only [dist_eq_norm,hdiff] at htri
  have hraw : ‖(4*Real.pi:ℂ)*windowIdentityContribution K hc R hR t (t+ε)-((2*t*ε:ℝ):ℂ)‖ ≤
      8*(1+t+ε)*m₁/R+8*m₂/R^2+3*ε := by
    rw [show 1+(t+ε)=1+t+ε by ring,show t+ε-t=ε by ring] at hmass
    calc
      _ ≤ _ := htri
      _ ≤ (8*(1+t+ε)*m₁/R+8*m₂/R^2+2*ε)+ε^2 := add_le_add hmass (le_refl _)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hε1 hε.le]
  have hlinear : 8*(1+t+ε)*m₁/R ≤ 24*t*m₁/R := by
    apply div_le_div_of_nonneg_right _ hR.le
    exact mul_le_mul_of_nonneg_right (by linarith : 8*(1+t+ε)≤24*t) hm₁
  have hquadratic : 8*m₂/R^2≤8*t*m₂/R := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hR) hR).mpr
    have hRR : R≤t*R^2 := by
      calc
        R ≤ R^2 := by nlinarith
        _ ≤ t*R^2 := by nlinarith [mul_le_mul_of_nonneg_right ht (sq_nonneg R)]
    calc
      _ ≤ 8*m₂*(t*R^2) := mul_le_mul_of_nonneg_left hRR (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (24*t*m₁/R+8*t*m₂/R+3*ε)/(t*ε) :=
      div_le_div_of_nonneg_right (hraw.trans (by linarith)) (mul_pos ht0 hε).le
    _ = _ := by
      dsimp [m₁,m₂]
      field_simp [hR.ne',ht0.ne',hε.ne']

/-- The original literal-interval spherical identity has negligible normalized
error at the prescribed radius, from the original width/product hypotheses. -/
theorem windowIdentityContribution_interval_scaled_negligible
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t =>
      ‖(4*Real.pi:ℂ)*windowIdentityContribution K hc (positiveWindowRadius ε t)
        (positiveWindowRadius_pos ε t) t (t+ε t)-((2*t*ε t:ℝ):ℂ)‖/(t*ε t))
      atTop (𝓝 0) := by
  have hi := tendsto_inv_atTop_zero.comp
    (positiveWindowRadius_resolves_width ε (hε.mono (fun _ h => h.1)) hproduct)
  have hmain := (hi.const_mul (24*(∫ u,|u| * K u)+8*(∫ u,|u|^2*K u))).add
    (tendsto_inv_atTop_zero.const_mul (3:ℝ))
  simp only [mul_zero,add_zero] at hmain
  simp only [← div_eq_mul_inv] at hmain
  apply squeeze_zero' _ _ hmain
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t ht hp
    exact div_nonneg (norm_nonneg _) (mul_pos hp ht.1).le
  · filter_upwards [hε,eventually_ge_atTop (1:ℝ)] with t ht hp
    exact windowIdentityContribution_interval_bound K he hc hK hm _
      (positiveWindowRadius_pos ε t) (le_max_left _ _) t (ε t) hp ht.1 ht.2

/-- The actual spherical identity has the expected leading coefficient for
literal [t,t+epsilon(t)], with no main-term hypothesis supplied. -/
theorem windowIdentityContribution_interval_normalized
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => (windowIdentityContribution K hc (positiveWindowRadius ε t)
      (positiveWindowRadius_pos ε t) t (t+ε t)).re/(t*ε t)) atTop (𝓝 (1/(2*Real.pi))) := by
  have hscaled := windowIdentityContribution_interval_scaled_negligible K he hc hK hm ε hε hproduct
  have hmajor := hscaled.div_const (4*Real.pi)
  rw [zero_div] at hmajor
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hmajor
  filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t ht hp
  let I := windowIdentityContribution K hc (positiveWindowRadius ε t)
    (positiveWindowRadius_pos ε t) t (t+ε t)
  have hεpos : 0<ε t := ht.1
  have hid : I.re/(t*ε t)-1/(2*Real.pi)=
      (((4*Real.pi:ℂ)*I-((2*t*ε t:ℝ):ℂ)).re)/(4*Real.pi*(t*ε t)) := by
    rw [show (4*Real.pi:ℂ)=((4*Real.pi:ℝ):ℂ) by
      simp only [Complex.ofReal_mul,Complex.ofReal_ofNat]]
    simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero]
    field_simp [Real.pi_ne_zero,hp.ne',ht.1.ne']
    ring
  change ‖I.re/(t*ε t)-1/(2*Real.pi)‖≤_
  rw [hid,Real.norm_eq_abs,abs_div,abs_of_pos (by positivity : 0<4*Real.pi*(t*ε t))]
  calc
    _ ≤ ‖(4*Real.pi:ℂ)*I-((2*t*ε t:ℝ):ℂ)‖/(4*Real.pi*(t*ε t)) :=
      div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) (by positivity)
    _ = _ := by ring


#print axioms windowIdentityContribution_interval_bound
#print axioms windowIdentityContribution_interval_scaled_negligible
#print axioms windowIdentityContribution_interval_normalized

end QuantitativeMaass
