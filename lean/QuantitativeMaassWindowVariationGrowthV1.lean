module

public import QuantitativeMaassWindowInitialVariationV1
public import QuantitativeMaassWindowRadialTailV1
public import QuantitativeMaassRadialVariationCoordinateV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- Quantitative total variation for the actual squared-window profile.
The spectral growth is t^(3/2), with explicit propagation-radius dependence. -/
theorem windowTimeSquareProfile_variation_growth (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ B D : ℝ,0<B ∧ 0<D ∧ ∀ R : ℝ,∀ hR : 1≤R,∀ ε : ℝ,0≤ε → ε≤1 →
      ∀ t : ℝ,1≤t →
      (∫ v : ℝ,‖deriv (parabolicLineProfile (windowTimeSquareProfile K hc R
        (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε)) 1) v‖)≤
        D*R^2*ε^2*((Real.cosh (B*R)+1)^2+t*Real.sqrt t*(Real.sqrt (B*R)+1)) := by
  obtain ⟨B0,C0,hB0,hC0,hinner⟩ := windowTimeSquareProfile_initial_variation K he hc
  obtain ⟨C1,hC1,houter⟩ := windowTimeSquareProfile_inverse_square_tail K he hc
  obtain ⟨S,hS,hsupport⟩ := symmetricWindowTimeTest_uniform_support K hc
  let B := 1+B0+2*S
  have hB : 0<B := by dsimp only [B];positivity
  refine ⟨B,2*(C0+C1),hB,by positivity,?_⟩
  intro R hR ε hε hε1 t ht
  have hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  have ht0 : 0<t := lt_of_lt_of_le zero_lt_one ht
  have hL : 1≤B*R := by dsimp only [B];nlinarith
  have hB0R : B0*R≤B*R := by dsimp only [B];nlinarith
  have hSR : S*R+S*R≤B*R := by dsimp only [B];nlinarith
  let g := windowTimeSquareProfile K hc R hRp (t-ε) (t+ε)
  let k := fun r => g (Real.cosh r)
  let w := windowTimeSchwartz K hc R hRp (t-ε) (t+ε)
  have hps : Function.support g⊆Iic (Real.cosh (S*R+S*R)) :=
    abelProfile_support _ _ (evenCoshLift_support_of_time_support _ _ (by positivity)
      (timeConvolution_support w w (S*R) (S*R) (hsupport R hRp (t-ε) (t+ε)) (hsupport R hRp (t-ε) (t+ε))))
  have hks : Function.support k⊆Icc (-(B*R)) (B*R) := by
    intro r hr
    have hh := Real.cosh_le_cosh.mp (hps hr)
    rw [abs_of_nonneg (by positivity : 0≤S*R+S*R)] at hh
    exact abs_le.mp (hh.trans hSR)
  have hke : Function.Even k := by intro r;simp only [k,Real.cosh_neg]
  have hk : ContDiff ℝ ∞ k := windowTimeSquareProfile_cosh_smooth K he hc R hRp (t-ε) (t+ε)
  have hH : ContDiff ℝ ∞ (parabolicLineProfile g 1) := parabolicLineProfile_smooth _
    (windowTimeSquareProfile_smoothOn K he hc R hRp (t-ε) (t+ε)) 1
  change (∫ v : ℝ,‖deriv (parabolicLineProfile g 1) v‖)≤_
  rw [parabolicLineProfile_variation_radial g hH,even_compact_radial_variation k hke (B*R) (by positivity) hks]
  have hi := hinner R hR ε hε hε1 t ht
  have ho := houter R hR ε hε hε1 t ht (B*R) hL
  change (∫ r in (0:ℝ)..(1/t)^2,‖deriv k r‖)≤_ at hi
  change (∫ r in (1/t)^2..(B*R),‖deriv k r‖)≤_ at ho
  have hic := ((contDiff_infty_iff_deriv.mp hk).2.continuous.norm)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hic.intervalIntegrable (μ:=volume) 0 ((1/t)^2))
    (hic.intervalIntegrable (μ:=volume) ((1/t)^2) (B*R))]
  have hcosh : Real.cosh (B0*R)≤Real.cosh (B*R) := Real.cosh_le_cosh.mpr (by
    simpa only [abs_of_nonneg (by positivity : 0≤B0*R),abs_of_nonneg (by positivity : 0≤B*R)] using hB0R)
  have hi' : (∫ r in (0:ℝ)..(1/t)^2,‖deriv k r‖)≤C0*R^2*ε^2*(Real.cosh (B*R)+1)^2 := by
    apply hi.trans
    gcongr
    nlinarith
  have hbound := mul_le_mul_of_nonneg_left (add_le_add hi' ho) (by norm_num : (0:ℝ)≤2)
  apply hbound.trans
  have hX : 0≤R^2*ε^2*(Real.cosh (B*R)+1)^2 := by positivity
  have hY : 0≤R^2*ε^2*(t*Real.sqrt t*(Real.sqrt (B*R)+1)) := by positivity
  nlinarith [mul_nonneg hC1.le hX,mul_nonneg hC0.le hY]

#print axioms windowTimeSquareProfile_variation_growth

end QuantitativeMaass
