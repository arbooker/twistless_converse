module

public import QuantitativeMaassTranslatedWindowV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson QuantitativeArithmeticMaassOverlap
open scoped Topology ContDiff FourierTransform SchwartzMap ENNReal

namespace QuantitativeMaass

/-- Actual nonscalar correspondence remainder for a fixed cosine time translation. -/
def translatedWindowIntegralRemainder (s : ℝ) (N : ℕ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) : ℍ → ℂ :=
  radialIntegralRemainder N M hM
    (abelProfile (evenCoshLift (translatedWindowSquare K hc R hR a b s)))

/-- Integrated translated error, with constants before all matrices, levels
and window parameters. The fixed time shift is absorbed into the support constant. -/
theorem translatedWindowIntegralRemainder_integrated_bound (s : ℝ)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ U C : ℝ,0<U ∧ 0<C ∧ ∀ (N : ℕ) [NeZero N]
      (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
      (o : ℍ) (L R ε t : ℝ) (hR : 1≤R),0≤ε → ε≤1 → 1≤t →
    (∫ z in Metric.closedBall o L,‖translatedWindowIntegralRemainder s N M hM K hc R
      (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) z‖ ∂quotientMeasure N)≤
      (energyMultiplicity o 0 (2*(U*R)+2*L+dist (positiveIntegralGL M hM • o) o):ℝ)*
        (C*Real.sqrt t*R^2*ε^2)*
        (Real.pi*(volume.real (Metric.closedBall o L)+hyperbolicSublevelConstant o L
          (2*(U*R)+2*L+dist (positiveIntegralGL M hM • o) o+2*Real.log (2*integralMatrixHeight M)))) := by
  obtain ⟨U₀,hU₀,hs⟩ := translatedWindowSquare_uniform_support K hc
  obtain ⟨C,hC,hbound⟩ := translatedWindowSquare_abel_decay K he hc s
  let U := U₀+|s|
  have hU : 0<U := by dsimp only [U];positivity
  refine ⟨U,C,hU,hC,?_⟩
  intro N _ M hM o L R ε t hR hε hε1 ht
  have hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  have hheight := integralMatrixHeight_bounds M
  have hB : 0< integralMatrixHeight M := lt_of_lt_of_le zero_lt_one hheight.1
  have hgs : Function.support (translatedWindowSquare K hc R hRp (t-ε) (t+ε) s)⊆
      Icc (-(2*(U*R))) (2*(U*R)) := by
    intro u hu
    have hh := hs R hRp (t-ε) (t+ε) s hu
    have hlen : 2*(U₀*R)+|s|≤2*(U*R) := by
      dsimp only [U]
      nlinarith [abs_nonneg s,mul_le_mul_of_nonneg_left hR (abs_nonneg s)]
    constructor <;> linarith [hh.1,hh.2]
  have hps : Function.support (abelProfile (evenCoshLift
      (translatedWindowSquare K hc R hRp (t-ε) (t+ε) s)))⊆Iic (Real.cosh (2*(U*R))) :=
    abelProfile_support _ _ (evenCoshLift_support_of_time_support _ _ (by positivity) hgs)
  apply radialIntegralRemainder_quotient_integral_bound N M hM (integralMatrixHeight M) hB hheight.2
    o L (2*(U*R)) (by positivity) _
    (translatedWindowSquare_profile_continuous K he hc R hRp (t-ε) (t+ε) s) hps
    (C*Real.sqrt t*R^2*ε^2) (by positivity)
  intro d hd
  exact hbound R ε t d hR hε hε1 ht hd

theorem translatedWindowIntegralRemainder_exp_bound (s : ℝ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ) :
    ∃ A C : ℝ,0<A ∧ 0<C ∧ ∀ (N : ℕ) [NeZero N] (L R ε t : ℝ) (hR : 1≤R),
      0≤L → 0≤ε → ε≤1 → 1≤t →
      (∫ z in Metric.closedBall o L,‖translatedWindowIntegralRemainder s N M hM K hc R
        (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) z‖ ∂quotientMeasure N)≤
        C*Real.sqrt t*ε^2*Real.exp (A*R+30*L) := by
  obtain ⟨U,C,hU,hC,hbound⟩ := translatedWindowIntegralRemainder_integrated_bound s K he hc
  have hB : 0≤2*Real.log (2*integralMatrixHeight M) := by
    have h := (integralMatrixHeight_bounds M).1
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  obtain ⟨G,hG,hgeom⟩ := correspondence_geometry_exp o (dist (positiveIntegralGL M hM • o) o)
    (2*Real.log (2*integralMatrixHeight M)) dist_nonneg hB
  refine ⟨20*U+2,C*G,by positivity,mul_pos hC hG,?_⟩
  intro N _ L R ε t hR hL hε hε1 ht
  have hg := hgeom L (2*(U*R)+2*L) hL (by positivity)
  have hb := hbound N M hM o L R ε t hR hε hε1 ht
  apply hb.trans
  calc
    _ = (C*Real.sqrt t*R^2*ε^2)*((energyMultiplicity o 0
        (2*(U*R)+2*L+dist (positiveIntegralGL M hM • o) o):ℝ)*
      (Real.pi*(volume.real (Metric.closedBall o L)+hyperbolicSublevelConstant o L
        (2*(U*R)+2*L+dist (positiveIntegralGL M hM • o) o+2*Real.log (2*integralMatrixHeight M))))) := by ring
    _ ≤ (C*Real.sqrt t*R^2*ε^2)*(G*Real.exp (10*((2*(U*R)+2*L)+L))) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ ≤ _ := by
      have hr : R^2≤Real.exp (2*R) := by
        have hh := Real.add_one_le_exp R
        have hle : R≤Real.exp R := by linarith
        have hp := pow_le_pow_left₀ (by linarith : 0≤R) hle 2
        simpa only [← Real.exp_nat_mul,Nat.cast_ofNat] using hp
      calc
        _ ≤ (C*Real.sqrt t*(Real.exp (2*R))*ε^2)*(G*Real.exp (10*((2*(U*R)+2*L)+L))) := by gcongr
        _ = _ := by
          rw [show Real.exp ((20*U+2)*R+30*L)=Real.exp (2*R)*Real.exp (10*((2*(U*R)+2*L)+L)) from by
            rw [← Real.exp_add];congr 1;ring]
          ring

/-- For any fixed time translation and fixed positive integral correspondence, the actual nonscalar
quotient error is o(t epsilon(t)) for the literal original interval [t,t+epsilon(t)]
and the prescribed expanding balls, from the original width/product hypotheses. -/
theorem translatedWindowIntegralRemainder_interval_negligible (s : ℝ) (N : ℕ) [NeZero N]
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t =>
      (∫ z in Metric.closedBall o (positiveWindowRadius ε t),‖translatedWindowIntegralRemainder s N M hM K hc
        (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
        t (t+ε t) z‖ ∂quotientMeasure N)/(t*ε t)) atTop (𝓝 0) := by
  obtain ⟨A,C,hA,hC,hbound⟩ := translatedWindowIntegralRemainder_exp_bound s M hM K he hc o
  have hεp := hε.mono (fun _ h => h.1)
  have hR := positiveWindowRadius_div_scale ε hεp hproduct
  have hRp : ∀ᶠ t in atTop,0≤positiveWindowRadius ε t :=
    Eventually.of_forall (fun t => (positiveWindowRadius_pos ε t).le)
  have hmajor := geometric_majorant_tendsto ε (positiveWindowRadius ε) (positiveWindowRadius ε)
    A (2*C) hA.le (by positivity) hε hRp hRp hR hR
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    exact div_nonneg (integral_nonneg (fun _ => norm_nonneg _)) (mul_pos ht he.1).le
  · filter_upwards [hε,eventually_ge_atTop (1:ℝ)] with t he ht
    have hεpos : 0<ε t := he.1
    have htpos : 0<t := lt_of_lt_of_le zero_lt_one ht
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hb := hbound N (positiveWindowRadius ε t) (positiveWindowRadius ε t) (ε t/2)
      (t+ε t/2) (le_max_left _ _) (positiveWindowRadius_pos ε t).le (by positivity)
      (by linarith) (by linarith)
    rw [show t+ε t/2-ε t/2=t by ring,show t+ε t/2+ε t/2=t+ε t by ring] at hb
    apply hb.trans
    have hs : Real.sqrt (t+ε t/2)≤2*Real.sqrt t := by
      have ht0 : 0≤t := by linarith
      have hts : 0≤t+ε t/2 := by positivity
      nlinarith [Real.sq_sqrt ht0,Real.sq_sqrt hts,Real.sqrt_nonneg t,Real.sqrt_nonneg (t+ε t/2)]
    have hw : (ε t/2)^2≤(ε t)^2 := by nlinarith [sq_nonneg (ε t)]
    calc
      _ ≤ C*(2*Real.sqrt t)*(ε t)^2*
        Real.exp (A*positiveWindowRadius ε t+30*positiveWindowRadius ε t) := by gcongr
      _ = _ := by ring

#print axioms translatedWindowIntegralRemainder_integrated_bound
#print axioms translatedWindowIntegralRemainder_exp_bound
#print axioms translatedWindowIntegralRemainder_interval_negligible

end QuantitativeMaass
