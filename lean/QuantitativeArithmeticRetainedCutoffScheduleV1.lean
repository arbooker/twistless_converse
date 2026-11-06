module

public import QuantitativeArithmeticRetainedGeometricScheduleV1
public import QuantitativeHolomorphicUpperCutScalarRateV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedCutoffSchedule
open QuantitativeArithmeticEnvelope QuantitativeHolomorphic QuantitativeHolomorphic.Schedule
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedFiniteNormalization QuantitativeArithmeticRetainedFilterTrace
open QuantitativeArithmeticRetainedPreparedReconstruction
open QuantitativeArithmeticRetainedApproximationSchedule
open AsymptoticFourierNorm AsymptoticCylinderModeComparison AsymptoticCylinder

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ) (P : Parameters A)

def fixedMajorant : ℝ := majorantConstant (exponent A P+4) (4*Real.pi) P.ε

theorem fixedMajorant_nonneg : 0≤fixedMajorant A P := by unfold fixedMajorant majorantConstant; positivity

/-- The retained weighted/unweighted Fourier comparison has the same
scaled bridge error as the finite branch geometry. -/
theorem lower_mode_bridge (d : ℝ → ℕ) (hd : Exp 2 (fun s => (d s:ℝ))) :
    ∃K : ℝ,0≤K ∧ ∀s : ℝ,1≤s → ∀h : ℕ,
      let Y := lowerHeight A P (tolerance s (d s))
      let t := exponent A P+4
      (2*Real.sqrt (localizedErrorBound t (4*Real.pi) Y)*Real.sqrt (massSlope t (4*Real.pi) Y))*
        (Real.sqrt (2*h+2:ℝ))⁻¹≤bridgeErrorThird K (h+1) (Real.exp s) := by
  have hu := logAccuracy_growth d hd
  have hy : DoubleExp (fun s => (lowerHeight A P (tolerance s (d s)))⁻¹) := by
    have hh := ((QuantitativeArithmeticRetainedScheduleGrowth.height_inverse_growth A P).compPoly hu.1 hu.2).toDoubleExp
    simpa only [QuantitativeArithmeticRetainedScheduleGrowth.height,←tolerance_eq] using hh
  let C := localizedCoefficient (exponent A P+4) (4*Real.pi)+slopeCoefficient (exponent A P+4) (4*Real.pi)
  have hc : 0≤C := add_nonneg (localizedCoefficient_nonneg _ (by positivity)) (slopeCoefficient_nonneg _ (by positivity))
  have hb := (DoubleExp.const C).mul ((DoubleExp.const 1).add hy) (fun s _ => by
    have := lowerHeight_pos A P (tolerance_pos s (d s))
    positivity)
  obtain ⟨K,hK,hk⟩ := hb
  refine ⟨K,hK,fun s hs h => ?_⟩
  have hl := localized_sqrt_product_le (exponent A P+4) (by positivity : 0<4*Real.pi)
    (lowerHeight_pos A P (tolerance_pos s (d s)))
  have hcoeff := hl.trans (hk s hs)
  have he := mul_le_mul hcoeff (inverse_sqrt_weight_le_trace_power h) (by positivity) (Real.exp_nonneg _)
  exact he.trans_eq (double_exp_mul_trace_power _ _ h)

/-- Explicit upper-cusp error, with a constant height term and the same
weight-decaying bridge. The actual Newton polynomial majorant is used. -/
theorem upper_cut_bridge {C : ℝ} (hC : 0≤C) : ∃B K : ℝ,0≤B ∧ 0≤K ∧
    ∀s : ℝ,1≤s → ∀d h : ℕ,(d:ℝ)≤Real.exp (C*s^2) →
      let n := newtonDepth A P (tolerance s d)
      let b := (3/2:ℝ)^n
      upperCutError (b^2*(1+fixedMajorant A P)) b 1
        (massBound (2*h) (exponent A P+4) (4*Real.pi) (Real.exp (16*s))/(2*h+2:ℝ))≤
      B*Real.exp (-3*s)+bridgeErrorThird K (h+1) (Real.exp s) := by
  obtain ⟨b,hb,hmajor⟩ := majorant_growth A P hC
  let M := fixedMajorant A P
  let A₀ := upperMassCoefficient (exponent A P+4) (4*Real.pi)
  let c := b*upperWeightCoefficient M
  have hM : 0≤M := fixedMajorant_nonneg A P
  have ha : 0≤A₀ := upperMassCoefficient_nonneg _ (by positivity)
  have hc : 0≤c := by dsimp only [c,upperWeightCoefficient]; positivity
  refine ⟨24*b*upperHeightCoefficient M A₀,c+4,?_,by positivity,fun s hs d h hd => ?_⟩
  · dsimp only [upperHeightCoefficient]
    positivity
  · have hB2 : ((3/2:ℝ)^newtonDepth A P (tolerance s d))^2≤b*s^4 :=
      (le_max_right _ _).trans (hmajor s hs d hd)
    have hsplit := upperCutError_split (by positivity) hM ha hb hs
      (show (1:ℝ)≤2*h+2 by nlinarith [Nat.cast_nonneg (α:=ℝ) h]) hB2
      (scheduled_upper_mass h (exponent A P+4) (zero_le_one.trans hs))
    apply hsplit.trans
    apply add_le_add le_rfl
    have hcoeff : c*s^4≤Real.exp (Real.exp ((c+4)*s^2)) := by
      have hp : c*s^4≤Real.exp ((c+4)*s^2) := by
        simpa using polynomial_mul_exp_quadratic_le 4 (b:=c) (C:=0) hc hs
      apply hp.trans
      apply Real.exp_le_exp.mpr
      linarith [Real.add_one_le_exp ((c+4)*s^2)]
    have hm := mul_le_mul hcoeff (inverse_sqrt_weight_le_trace_power h) (by positivity) (Real.exp_nonneg _)
    exact hm.trans_eq (double_exp_mul_trace_power _ _ h)

#print axioms fixedMajorant_nonneg
#print axioms lower_mode_bridge
#print axioms upper_cut_bridge
end QuantitativeArithmeticRetainedCutoffSchedule
