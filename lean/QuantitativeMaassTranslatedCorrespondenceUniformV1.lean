module

public import QuantitativeMaassTranslatedWindowUniformV1
public import QuantitativeMaassTranslatedCorrespondenceV1
public import QuantitativeMaassCorrespondenceHeightV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson QuantitativeArithmeticMaassOverlap
open scoped Topology ContDiff FourierTransform SchwartzMap ENNReal
namespace QuantitativeMaass

/-- Uniform translated raw-volume trace error, retaining the time shift
in the propagation radius and the explicit amplitude bound. -/
theorem translatedWindowIntegralRemainder_uniform_raw_bound (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ U C : ℝ,0<U ∧ 0<C ∧ ∀ (s : ℝ) (N : ℕ) [NeZero N]
      (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
      (o : ℍ) (L R ε t : ℝ) (hR : 1≤R),0≤ε → ε≤1 → 1≤t →
    IntegrableOn (translatedWindowIntegralRemainder s N M hM K hc R
      (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε)) (Metric.closedBall o L) ∧
    (∫ z in Metric.closedBall o L,‖translatedWindowIntegralRemainder s N M hM K hc R
      (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) z‖)≤
      (energyMultiplicity o 0 ((2*(U*R)+|s|)+2*L+dist (positiveIntegralGL M hM • o) o):ℝ)*
        (C*(1+|s|)*Real.sqrt t*R^2*ε^2)*
        (Real.pi*(volume.real (Metric.closedBall o L)+hyperbolicSublevelConstant o L
          ((2*(U*R)+|s|)+2*L+dist (positiveIntegralGL M hM • o) o+2*Real.log (2*integralMatrixHeight M)))) := by
  obtain ⟨U,hU,hs⟩ := translatedWindowSquare_uniform_support K hc
  obtain ⟨C,hC,hbound⟩ := translatedWindowSquare_abel_decay_uniform K he hc
  refine ⟨U,C,hU,hC,?_⟩
  intro s N _ M hM o L R ε t hR hε hε1 ht
  have hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  have hheight := integralMatrixHeight_bounds M
  have hB : 0< integralMatrixHeight M := lt_of_lt_of_le zero_lt_one hheight.1
  have hgs := hs R hRp (t-ε) (t+ε) s
  have hps : Function.support (abelProfile (evenCoshLift (translatedWindowSquare K hc R hRp (t-ε) (t+ε) s)))⊆Iic (Real.cosh ((2*(U*R)+|s|))) :=
    abelProfile_support _ _ (evenCoshLift_support_of_time_support _ _ (by positivity) hgs)
  apply radialIntegralRemainder_integral_bound N M hM (integralMatrixHeight M) hB hheight.2
    o L ((2*(U*R)+|s|)) (by positivity) (abelProfile (evenCoshLift (translatedWindowSquare K hc R hRp (t-ε) (t+ε) s)))
    (translatedWindowSquare_profile_continuous K he hc R hRp (t-ε) (t+ε) s) hps (C*(1+|s|)*Real.sqrt t*R^2*ε^2) (by positivity)
  intro d hd
  exact hbound s R ε t d hR hε hε1 ht hd

/-- The matrix height and time shift are both quantified after the
constants. This bound supports growing Hecke and LV degrees. -/
theorem translatedWindowIntegralRemainder_uniform_height_bound
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ) :
    ∃ A C : ℝ,0<A ∧ 0<C ∧ ∀ (s : ℝ) (N : ℕ) [NeZero N]
      (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
      (L R ε t : ℝ) (hR : 1≤R),0≤L → 0≤ε → ε≤1 → 1≤t →
      IntegrableOn (translatedWindowIntegralRemainder s N M hM K hc R
        (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε)) (Metric.closedBall o L) ∧
      (∫ z in Metric.closedBall o L,‖translatedWindowIntegralRemainder s N M hM K hc R
        (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) z‖)≤
        C*(integralMatrixHeight M)^40*(1+|s|)*Real.sqrt t*ε^2*Real.exp (A*R+30*L+10*|s|) := by
  obtain ⟨U,C,hU,hC,hbound⟩ := translatedWindowIntegralRemainder_uniform_raw_bound K he hc
  obtain ⟨G,hG,hgeom⟩ := correspondence_geometry_uniform_exp o
  obtain ⟨J,hJ,hheight⟩ := correspondence_height_cost o
  refine ⟨20*U+2,C*G*J,by positivity,by positivity,?_⟩
  intro s N _ M hM L R ε t hR hL hε hε1 ht
  have hB := integralMatrixHeight_bounds M
  have hb : 0≤2*Real.log (2*integralMatrixHeight M) :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by linarith only [hB.1]))
  obtain ⟨hi,hiBound⟩ := hbound s N M hM o L R ε t hR hε hε1 ht
  refine ⟨hi,hiBound.trans ?_⟩
  have hg := hgeom L ((2*(U*R)+|s|)+2*L) (dist (positiveIntegralGL M hM•o) o)
    (2*Real.log (2*integralMatrixHeight M)) hL (by positivity) dist_nonneg hb
  have hj := hheight M hM _ hB.1 hB.2
  have hr : R^2≤Real.exp (2*R) := by
    have hh := Real.add_one_le_exp R
    have hle : R≤Real.exp R := by linarith only [hh]
    have hp := pow_le_pow_left₀ (by linarith only [hR] : 0≤R) hle 2
    simpa only [←Real.exp_nat_mul,Nat.cast_ofNat] using hp
  have heq : Real.exp (10*(((2*(U*R)+|s|)+2*L)+L+dist (positiveIntegralGL M hM•o) o+
      2*Real.log (2*integralMatrixHeight M)))=
      Real.exp (10*(((2*(U*R)+|s|)+2*L)+L))*
      Real.exp (10*(dist (positiveIntegralGL M hM•o) o+2*Real.log (2*integralMatrixHeight M))) := by
    rw [←Real.exp_add];congr 1;ring
  rw [heq] at hg
  have hg' := hg.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hj (Real.exp_pos _).le) hG.le)
  calc
    _ = (C*(1+|s|)*Real.sqrt t*R^2*ε^2)*((energyMultiplicity o 0
        ((2*(U*R)+|s|)+2*L+dist (positiveIntegralGL M hM•o) o):ℝ)*
      (Real.pi*(volume.real (Metric.closedBall o L)+hyperbolicSublevelConstant o L
        ((2*(U*R)+|s|)+2*L+dist (positiveIntegralGL M hM•o) o+2*Real.log (2*integralMatrixHeight M))))) := by ring
    _ ≤ (C*(1+|s|)*Real.sqrt t*R^2*ε^2)*(G*(Real.exp (10*(((2*(U*R)+|s|)+2*L)+L))*(J*(integralMatrixHeight M)^40))) :=
      mul_le_mul_of_nonneg_left hg' (by positivity)
    _ ≤ (C*(1+|s|)*Real.sqrt t*Real.exp (2*R)*ε^2)*(G*(Real.exp (10*(((2*(U*R)+|s|)+2*L)+L))*(J*(integralMatrixHeight M)^40))) := by
      gcongr
    _ = _ := by
      rw [show Real.exp ((20*U+2)*R+30*L+10*|s|)=Real.exp (2*R)*Real.exp (10*(((2*(U*R)+|s|)+2*L)+L)) from by
        rw [←Real.exp_add];congr 1;ring]
      ac_rfl

#print axioms translatedWindowIntegralRemainder_uniform_raw_bound
#print axioms translatedWindowIntegralRemainder_uniform_height_bound
end QuantitativeMaass
