module

public import QuantitativeArithmeticRetainedNestedCountComparisonV1
public import QuantitativeEulerEndpointCommonAnalyticScaleV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedHorizonScale
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns
open QuantitativeArithmeticRetainedApproximationSchedule QuantitativeArithmeticRetainedFiniteNormalization
open QuantitativeEulerEndpointCommonReconstruction
open QuantitativeHolomorphic QuantitativeHolomorphic.Schedule AsymptoticFiniteBranch
variable {N Q : ℕ} {R₀ : Finset ℕ} {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A)

/-- Reciprocal lower cutoff keeps a single exponential envelope in accuracy. -/
theorem lower_inverse_growth : QuantitativeArithmeticEnvelope.Exp 4 (fun s =>
    (lowerHeight A P (tolerance s 0))⁻¹) := by
  have hd : QuantitativeArithmeticEnvelope.Exp 2 (fun _ : ℝ => ((0:ℕ):ℝ)) := by
    simpa only [Nat.cast_zero] using QuantitativeArithmeticEnvelope.Exp.const 0 2
  have hu := QuantitativeArithmeticRetainedApproximationSchedule.logAccuracy_growth (fun _ => 0) hd
  have hh := (QuantitativeArithmeticRetainedScheduleGrowth.height_inverse_growth A P).compPoly hu.1 hu.2
  simpa only [QuantitativeArithmeticRetainedScheduleGrowth.height,←tolerance_eq] using hh

/-- The SAME common lower and upper cutoffs, the matrix separation cost,
and the mass bound all have one horizon envelope. -/
theorem exists_horizon_trace_geometry {K a : ℝ} (hK : 0≤K) (ha : 0≤a) :
    ∃ C : ℝ,0≤C ∧ ∀ n : ℕ,
      let s := Real.exp ((K+1)*(4:ℝ)^n)
      let H := Real.exp (16*s)
      let Y := lowerHeight A P (tolerance s 0)
      let M := Real.exp (Real.exp (a*(4:ℝ)^n))
      let L := Real.exp (Real.exp (C*(4:ℝ)^n))
      M*(H+2)≤L ∧ H≤L ∧ Y⁻¹≤L ∧ M≤L := by
  obtain ⟨d,hd,hheight⟩ := lower_inverse_growth A P
  let b := d+4*(K+1)+(K+17)
  have hb : 0≤b := by dsimp only [b]; positivity
  refine ⟨a+b+7,by positivity,?_⟩
  intro n s H Y M L
  let R : ℝ := (4:ℝ)^n
  let V := Real.exp (Real.exp (b*R))
  have hR : 1≤R := one_le_pow₀ (by norm_num)
  have hR0 : 0≤R := by linarith
  have hs : 1≤s := Real.one_le_exp (by positivity)
  have hV : 1≤V := Real.one_le_exp (Real.exp_pos _).le
  have hH : H≤V := by
    apply Real.exp_le_exp.mpr
    have hh := QuantitativeEulerEndpointPolynomialGrowth.scaled_exp_le
      (a:=K+1) (by norm_num : (0:ℝ)≤16) hR
    apply hh.trans
    apply Real.exp_le_exp.mpr
    dsimp only [b]
    nlinarith
  have hY : Y⁻¹≤V := by
    have hh := hheight s hs
    apply hh.trans
    apply Real.exp_le_exp.mpr
    have he : s^4=Real.exp ((4*(K+1))*R) := by
      dsimp only [s,R]
      rw [←Real.exp_nat_mul]
      congr 1
      norm_num
      ring
    rw [he]
    apply (QuantitativeEulerEndpointPolynomialGrowth.scaled_exp_le hd hR).trans
    apply Real.exp_le_exp.mpr
    dsimp only [b]
    nlinarith
  have hVL : V≤L := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by nlinarith))
  have hML : M≤L := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by nlinarith))
  refine ⟨?_,hH.trans hVL,hY.trans hVL,hML⟩
  have hp : H+2≤4*V^2 := by nlinarith [sq_nonneg (V-1)]
  have hh := mul_le_mul_of_nonneg_left hp (Real.exp_pos (Real.exp (a*R))).le
  have hc := double_exp_sandwich_cost ha hb hR
  apply hh.trans
  convert hc using 1
  ring

/-- The actual common cutoff geometry pays the canonical periodization
error and finite-weight separation at a double-logarithmic block horizon.
The constant is chosen before horizon and weight. -/
theorem exists_horizon_trace_scale {K a : ℝ} (hK : 0≤K) (ha : 0≤a) :
    ∃ C : ℝ,0≤C ∧ ∀ n h : ℕ,∀ c : ℝ,0<h →
      1≤Real.log (observationScale c (h+1)) →
      32≤Real.log (Real.log (h+1:ℝ)) →
      (4:ℝ)^n≤(Real.log (observationScale c (h+1)))^2 →
      (geometryGrowthCoefficient+29+C)*c^2≤1/2 →
      let s := Real.exp ((K+1)*(4:ℝ)^n)
      let M := Real.exp (Real.exp (a*(4:ℝ)^n))
      let Y := lowerHeight A P (tolerance s 0)
      let H := Real.exp (16*s)
      (h+1:ℝ)^(-(1/3:ℝ))*(M*(H+2))≤1 ∧
        M*uniformRetainedTraceError (M*(H+2)) Y H h (periodizationSet Y H).card≤
          Real.exp (-Real.log (h+1:ℝ)/4) := by
  obtain ⟨C,hC,hgeom⟩ := exists_horizon_trace_geometry A P hK ha
  refine ⟨C,hC,?_⟩
  intro n h c hh hs hlog hn hscale s M Y H
  have hg := hgeom n
  have hm : Real.exp (Real.exp (C*(4:ℝ)^n))≤
      Real.exp (Real.exp (C*(Real.log (observationScale c (h+1)))^2)) :=
    Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn hC))
  exact growing_retained_trace_at_scale h hh (by positivity) (lowerHeight_pos A P (tolerance_pos s 0))
    (Real.exp_pos _) (Real.exp_pos _).le hC hs hlog hscale
    (hg.1.trans hm) (hg.2.1.trans hm) (hg.2.2.1.trans hm) (hg.2.2.2.trans hm)


/-- Analytic reconstruction error at the common horizon. -/
theorem exists_horizon_analytic_error {K : ℝ} (hK : 0≤K) :
    ∃ C D : ℝ,0≤C ∧ 0≤D ∧ ∀n h : ℕ,
      let s := Real.exp ((K+1)*(4:ℝ)^n)
      QuantitativeArithmeticRetainedTraceComparison.traceError A P (tolerance s 0) (Real.exp (16*s)) h≤
        C/(4:ℝ)^n+2*Real.exp (Real.exp (D*(4:ℝ)^n))*(Real.sqrt (2*h+2:ℝ))⁻¹ := by
  obtain ⟨C,d,hC,hd,herr⟩ := QuantitativeArithmeticRetainedScheduledTrace.trace_error_rate A P
  refine ⟨C,d+4*(K+1),hC,by positivity,?_⟩
  intro n h s
  have hR : 1≤(4:ℝ)^n := one_le_pow₀ (by norm_num)
  have hs : 1≤s := Real.one_le_exp (by positivity)
  have he : s^4=Real.exp ((4*(K+1))*(4:ℝ)^n) := by
    dsimp only [s]
    rw [←Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hd' : Real.exp (d*s^4)≤Real.exp (Real.exp ((d+4*(K+1))*(4:ℝ)^n)) := by
    apply Real.exp_le_exp.mpr
    rw [he]
    exact QuantitativeEulerEndpointPolynomialGrowth.scaled_exp_le hd hR
  have hc : C*Real.exp (-3*s)≤C/(4:ℝ)^n := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left (scheduled_exp_error hK hR) hC
  have ht := mul_le_mul_of_nonneg_right hd' (by positivity : 0≤(Real.sqrt (2*h+2:ℝ))⁻¹)
  have hh := herr s hs h
  nlinarith only [hc,ht,hh]

/-- The same double-logarithmic observation scale controls analytic errors. -/
theorem exists_horizon_analytic_scale {K : ℝ} (hK : 0≤K) :
    ∃ C D : ℝ,0≤C ∧ 0≤D ∧ ∀n h : ℕ,∀c : ℝ,0<h →
      32≤Real.log (Real.log (h+1:ℝ)) →
      (4:ℝ)^n≤(Real.log (observationScale c (h+1)))^2 → D*c^2≤1/2 →
      let s := Real.exp ((K+1)*(4:ℝ)^n)
      QuantitativeArithmeticRetainedTraceComparison.traceError A P (tolerance s 0) (Real.exp (16*s)) h≤
        C/(4:ℝ)^n+2*Real.exp (-Real.log (h+1:ℝ)/4) := by
  obtain ⟨C,D,hC,hD,herr⟩ := exists_horizon_analytic_error A P hK
  refine ⟨C,D,hC,hD,?_⟩
  intro n h c hh hlog hn hscale s
  have hp := horizon_sqrt_error_at_scale hD n h hh hlog hn hscale
  have he := herr n h
  dsimp only at he
  nlinarith only [hp,he]

#print axioms lower_inverse_growth
#print axioms exists_horizon_trace_geometry
#print axioms exists_horizon_trace_scale
#print axioms exists_horizon_analytic_error
#print axioms exists_horizon_analytic_scale
end QuantitativeArithmeticRetainedHorizonScale
