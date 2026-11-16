module

public import QuantitativeMaassMixedHeckeTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- The spherical density is nonnegative on the entire real spectral line. -/
theorem windowPlancherelWeight_nonneg (r : ℝ) : 0≤windowPlancherelWeight r := by
  have hp (x : ℝ) (hx : 0≤x) : 0≤windowPlancherelWeight x := by
    unfold windowPlancherelWeight
    rw [Real.tanh_eq_sinh_div_cosh]
    exact mul_nonneg hx (div_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg Real.pi_pos.le hx))
      (Real.cosh_pos _).le)
  by_cases hr : 0≤r
  · exact hp r hr
  · rw [← windowPlancherelWeight_even r]
    exact hp (-r) (neg_nonneg.mpr (le_of_not_ge hr))

/-- The actual translated identity is precisely the original squared window
mass with its cosine multiplier, including the spherical normalization. -/
theorem translatedWindowIdentity_eq_mass (τ : ℝ) (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (ha : 0<a) :
    translatedWindowIdentity τ K hc R hR a b=
      ((1/(4*Real.pi)*(∫ r : ℝ,Real.cos (τ*r)*
        ((smoothedWindow K R (Icc a b∪Icc (-b) (-a)) r)^2*windowPlancherelWeight r)):ℝ):ℂ) := by
  let f := windowTimeSchwartz K hc R hR a b
  have hf : Function.Even f := symmetricWindowTimeTest_even K he R a b
  have hfc : HasCompactSupport (f : ℝ → ℂ) := symmetricWindowTimeTest_compact K hc R a b hR
  change abelProfile (evenCoshLift (evenTimeTranslate τ (timeConvolution f f))) 1=_
  rw [evenTimeTranslate_spherical_identity _ ((timeConvolution f f).smooth ⊤)
    (timeConvolution_even f f hf hf) (timeConvolution_compact f f hfc hfc)]
  simp_rw [cosinePacket_timeConvolution f f hf hf]
  have hcos (r : ℝ) : cosinePacket f r=(smoothedWindow K R (Icc a b∪Icc (-b) (-a)) r:ℂ) :=
    symmetricWindowTimeTest_cosinePacket K he hc R a b r hR ha
  simp_rw [hcos]
  rw [Complex.ofReal_mul,← integral_complex_ofReal]
  congr 1
  · simp only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_one,Complex.ofReal_ofNat]
  · apply integral_congr_ae
    exact Eventually.of_forall (fun r => by
      simp only [windowPlancherelWeight,Complex.ofReal_mul,Complex.ofReal_pow]
      ring)

/-- Every real time shift is dominated by the unshifted positive spherical
mass; the bound is uniform in the shift and window parameters. -/
theorem translatedWindowIdentity_abs_le (τ : ℝ) (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (R : ℝ) (hR : 0<R) (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    |(translatedWindowIdentity τ K hc R hR a b).re|≤
      (windowIdentityContribution K hc R hR a b).re := by
  let w := fun r => (smoothedWindow K R (Icc a b∪Icc (-b) (-a)) r)^2*windowPlancherelWeight r
  have hw (r : ℝ) : 0≤w r := mul_nonneg (sq_nonneg _) (windowPlancherelWeight_nonneg r)
  have hi : Integrable w := (symmetric_squaredWindow_plancherel_mass a b ha hab K hK hm R hR).1
  have hb : |∫ r,Real.cos (τ*r)*w r|≤∫ r,w r := by
    rw [← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le hi
    exact Eventually.of_forall (fun r => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hw r)]
      exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (hw r)).trans_eq (one_mul _))
  rw [translatedWindowIdentity_eq_mass τ K he hc R hR a b ha,
    windowIdentityContribution_eq_mass K he hc R hR a b ha]
  have hcast : (1/(4*Real.pi):ℂ)=((1/(4*Real.pi):ℝ):ℂ) := by push_cast; rfl
  rw [hcast,← Complex.ofReal_mul]
  simp only [Complex.ofReal_re,abs_mul,abs_of_pos (by positivity : 0<(1/(4*Real.pi):ℝ))]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

/-- Replacing expanding-ball volume by the full actual quotient volume costs
little-o of the original window normalization, even for oscillating shifts. -/
theorem translatedWindowIdentity_volume_error (τ : ℝ) (N : ℕ) [NeZero N]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t =>
      (((quotientMeasure N).real (Metric.closedBall o (positiveWindowRadius ε t))-
        (quotientMeasure N).real univ)*
      (translatedWindowIdentity τ K hc (positiveWindowRadius ε t)
        (positiveWindowRadius_pos ε t) t (t+ε t)).re)/(t*ε t)) atTop (𝓝 0) := by
  have hV := (quotientMeasure_expanding_ball_limit N o (positiveWindowRadius ε)
    (positiveWindowRadius_tendsto_atTop ε hε hproduct)).sub_const ((quotientMeasure N).real univ)
  rw [sub_self] at hV
  have hlim := hV.norm.mul (windowIdentityContribution_interval_normalized K he hc hK hm ε hε hproduct)
  simp only [norm_zero,zero_mul] at hlim
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t ht hp
  rw [norm_div,norm_mul,Real.norm_eq_abs (t*ε t),abs_of_pos (mul_pos hp ht.1),mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [Real.norm_eq_abs]
  exact div_le_div_of_nonneg_right
    (translatedWindowIdentity_abs_le τ K he hc hK hm _ (positiveWindowRadius_pos ε t)
      t (t+ε t) hp (le_add_of_nonneg_right ht.1.le)) (mul_pos hp ht.1).le

#print axioms windowPlancherelWeight_nonneg
#print axioms translatedWindowIdentity_eq_mass
#print axioms translatedWindowIdentity_abs_le
#print axioms translatedWindowIdentity_volume_error

end QuantitativeMaass
