module

public import QuantitativeArithmeticRetainedTraceComparisonV1
public import QuantitativeArithmeticRetainedCutoffScheduleV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedScheduledTrace
open QuantitativeArithmeticEnvelope QuantitativeHolomorphic QuantitativeHolomorphic.Schedule
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedFiniteNormalization QuantitativeArithmeticRetainedPreparedReconstruction
open QuantitativeArithmeticRetainedApproximationSchedule QuantitativeArithmeticRetainedCutoffSchedule
open AsymptoticCylinder AsymptoticCylinderModeComparison AsymptoticFourierNorm
variable {N Q : ℕ} {R₀ : Finset ℕ} {hQ : 0<Q}
    (A : Certificate N R₀ Q hQ) (P : Parameters A)

/-- The accuracy parameter for reconstruction is independent of the degree
of the terminal filter. -/
theorem accuracy_le_half {s : ℝ} (hs : 0≤s) : 2*tolerance s 0≤1 := by
  have he : Real.exp (-8*s)≤1 := Real.exp_le_one_iff.mpr (by linarith)
  simpa only [tolerance,Nat.cast_zero,mul_zero,zero_add,mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0)] using he

/-- No exponential of an exponential is needed for the lower-height
coefficient; retaining this sharper envelope is essential for the count. -/
theorem lower_mode_coefficient_growth : Exp 4 (fun s =>
    2*Real.sqrt (localizedErrorBound (exponent A P+4) (4*Real.pi) (lowerHeight A P (tolerance s 0)))*
      Real.sqrt (massSlope (exponent A P+4) (4*Real.pi) (lowerHeight A P (tolerance s 0)))) := by
  have hd : Exp 2 (fun _ : ℝ => ((0:ℕ):ℝ)) := by simpa only [Nat.cast_zero] using Exp.const 0 2
  have hu := logAccuracy_growth (fun _ => 0) hd
  have hy : Exp 4 (fun s => (lowerHeight A P (tolerance s 0))⁻¹) := by
    have hh := (QuantitativeArithmeticRetainedScheduleGrowth.height_inverse_growth A P).compPoly hu.1 hu.2
    simpa only [QuantitativeArithmeticRetainedScheduleGrowth.height,←tolerance_eq] using hh
  let C := localizedCoefficient (exponent A P+4) (4*Real.pi)+slopeCoefficient (exponent A P+4) (4*Real.pi)
  have hb := (Exp.const C 4).mul ((Exp.const 1 4).add hy) (fun s _ => by
    have := lowerHeight_pos A P (tolerance_pos s 0)
    positivity)
  apply hb.mono
  intro s _
  exact localized_sqrt_product_le (exponent A P+4) (by positivity : 0<4*Real.pi)
    (lowerHeight_pos A P (tolerance_pos s 0))

/-- Reconstruction trace replacement decays exponentially, independently
of the terminal filter depth. -/
theorem reconstruction_rate : ∃B : ℝ,0≤B ∧ ∀s : ℝ,1≤s →
    (2+2*QuantitativeArithmeticRetainedFilterTrace.traceMajorant A P (newtonDepth A P (tolerance s 0))*
      fixedMajorant A P)*Real.sqrt (2*tolerance s 0)≤B*Real.exp (-3*s) := by
  obtain ⟨B,hB,hmajor⟩ := majorant_growth A P (C:=0) (by norm_num)
  let M := fixedMajorant A P
  have hM : 0≤M := fixedMajorant_nonneg A P
  refine ⟨24*(2+2*B*M),by positivity,?_⟩
  intro s hs
  have hq := QuantitativeHolomorphic.Schedule.quartic_exp_decay (zero_le_one.trans hs)
  have hm := hmajor s hs 0 (by norm_num)
  have hfront : 2+2*QuantitativeArithmeticRetainedFilterTrace.traceMajorant A P
      (newtonDepth A P (tolerance s 0))*M≤(2+2*B*M)*s^4 := by
    have h := mul_le_mul_of_nonneg_right hm hM
    have hs4 : 1≤s^4 := one_le_pow₀ hs
    nlinarith only [h,hs4]
  have hsqrt : Real.sqrt (2*tolerance s 0)=Real.exp (-4*s) := by
    have he : 2*tolerance s 0=(Real.exp (-4*s))^2 := by
      simp only [tolerance,Nat.cast_zero,mul_zero,zero_add]
      rw [←Real.exp_nat_mul]
      have hh : -8*s=(2:ℕ)*(-4*s) := by norm_num; ring
      rw [hh]
      ring
    rw [he,Real.sqrt_sq (Real.exp_nonneg _)]
  rw [hsqrt]
  calc
    _ ≤ ((2+2*B*M)*s^4)*Real.exp (-4*s) := mul_le_mul_of_nonneg_right hfront (Real.exp_nonneg _)
    _ = (2+2*B*M)*(s^4*Real.exp (-4*s)) := by ring
    _ ≤ (2+2*B*M)*(24*Real.exp (-3*s)) := mul_le_mul_of_nonneg_left hq (by positivity)
    _ = _ := by ring


/-- The upper cutoff has the same single-exponential weight coefficient. -/
theorem upper_cut_rate : ∃B K : ℝ,0≤B ∧ 0≤K ∧ ∀s : ℝ,1≤s → ∀h : ℕ,
    let n := newtonDepth A P (tolerance s 0)
    let b := (3/2:ℝ)^n
    upperCutError (b^2*(1+fixedMajorant A P)) b 1
      (massBound (2*h) (exponent A P+4) (4*Real.pi) (Real.exp (16*s))/(2*h+2:ℝ))≤
      B*Real.exp (-3*s)+Real.exp (K*s^4)*(Real.sqrt (2*h+2:ℝ))⁻¹ := by
  obtain ⟨b,hb,hmajor⟩ := majorant_growth A P (C:=0) (by norm_num)
  let M := fixedMajorant A P
  let a := upperMassCoefficient (exponent A P+4) (4*Real.pi)
  let c := b*upperWeightCoefficient M
  have hM : 0≤M := fixedMajorant_nonneg A P
  have ha : 0≤a := upperMassCoefficient_nonneg _ (by positivity)
  have hc : 0≤c := by dsimp only [c,upperWeightCoefficient]; positivity
  refine ⟨24*b*upperHeightCoefficient M a,c,?_,hc,?_⟩
  · dsimp only [upperHeightCoefficient]; positivity
  intro s hs h n B
  have hB2 : B^2≤b*s^4 := (le_max_right _ _).trans (hmajor s hs 0 (by norm_num))
  have ht := upperCutError_split (by positivity : 0≤B) hM ha hb hs
    (show (1:ℝ)≤2*h+2 by nlinarith [Nat.cast_nonneg (α:=ℝ) h]) hB2
    (scheduled_upper_mass h (exponent A P+4) (zero_le_one.trans hs))
  apply ht.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  change c*s^4≤Real.exp (c*s^4)
  linarith [Real.add_one_le_exp (c*s^4)]

/-- Combined analytic error with the sharp dependence on the common
accuracy scale. This is uniform over all terminal contractions. -/
theorem trace_error_rate : ∃B K : ℝ,0≤B ∧ 0≤K ∧ ∀s : ℝ,1≤s → ∀h : ℕ,
    QuantitativeArithmeticRetainedTraceComparison.traceError A P (tolerance s 0) (Real.exp (16*s)) h≤
      B*Real.exp (-3*s)+2*Real.exp (K*s^4)*(Real.sqrt (2*h+2:ℝ))⁻¹ := by
  obtain ⟨Br,hBr,hr⟩ := reconstruction_rate A P
  obtain ⟨Bu,Ku,hBu,hKu,hu⟩ := upper_cut_rate A P
  obtain ⟨Kl,hKl,hl⟩ := lower_mode_coefficient_growth A P
  refine ⟨2*Br+Bu,Ku+Kl,by positivity,by positivity,?_⟩
  intro s hs h
  have heU : Real.exp (Ku*s^4)≤Real.exp ((Ku+Kl)*s^4) := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (s^2)])
  have heL : Real.exp (Kl*s^4)≤Real.exp ((Ku+Kl)*s^4) := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (s^2)])
  have hz : 0≤(Real.sqrt (2*h+2:ℝ))⁻¹ := by positivity
  have hr' := hr s hs
  have hu' := hu s hs h
  have hl' := mul_le_mul_of_nonneg_right ((hl s hs).trans heL) hz
  have heU' := mul_le_mul_of_nonneg_right heU hz
  unfold QuantitativeArithmeticRetainedTraceComparison.traceError
  dsimp only
  dsimp only [QuantitativeArithmeticRetainedCutoffSchedule.fixedMajorant] at hr' hu'
  nlinarith only [hr',hu',hl',heU']

#print axioms upper_cut_rate
#print axioms trace_error_rate
#print axioms accuracy_le_half
#print axioms lower_mode_coefficient_growth
#print axioms reconstruction_rate
end QuantitativeArithmeticRetainedScheduledTrace
