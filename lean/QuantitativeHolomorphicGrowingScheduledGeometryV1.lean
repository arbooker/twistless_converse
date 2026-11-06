module

public import QuantitativeHolomorphicGrowingScaledTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Schedule

open FinitenessCertificate FinitenessGlobalHeight AsymptoticCompactObservationCount

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) {ι : Type*}

def commonGeometryGrowthConstant (hN : 0<N) (P : Parameters A) (b C : ℝ) : ℝ :=
  (26+4*normalizedMatrixGrowthConstant A hN P C+2*b+C)+
  (16+4*normalizedComplexityGrowthConstant A P C+b+C)+
  |lowerInverseGrowthConstant A P C|+21

theorem commonGeometryGrowthConstant_nonneg (hN : 0<N) (P : Parameters A) {b C : ℝ}
    (hb : 0≤b) (hC : 0≤C) : 0≤commonGeometryGrowthConstant A hN P b C := by
  have hm := normalizedMatrixGrowthConstant_nonneg A hN P hC
  have hc := normalizedComplexityGrowthConstant_nonneg A P hC
  unfold commonGeometryGrowthConstant
  positivity

/-- All four concrete geometric inputs to the scaled trace estimate are
derived from actual scheduled cutoffs and the three literal row aggregates.
The upper strip height is explicitly X^16. -/
theorem growing_scheduled_geometry (hN : 0<N) (P : Parameters A)
    (qs : Finset ι) (r : ι → Row N) (L U : ℝ) {b C s : ℝ}
    (hb : 0≤b) (hC : 0≤C) (hs : 1≤s) (d : ℕ)
    (hd : (d:ℝ)≤Real.exp (C*s^2))
    (hrowsH : (∑ i∈qs,quantifiedRowHeight hN (r i) L U)≤Real.exp (b*s^2))
    (hrowsM : (∑ i∈qs,(quantifiedRowMass hN (r i) L U
      ((AsymptoticReconstructedCount.parameters A P).s+4))^2)≤Real.exp (b*s^2))
    (hrowsL : (∑ i∈qs,(quantifiedRowLength hN (r i) L U:ℝ)^2)≤Real.exp (b*s^2)) :
    let D₀ : ℝ := 2*d+2
    let n := newtonDepth A P D₀ (Real.exp (-8*s))
    let j := reconstructionDepth A P D₀ (Real.exp (-8*s)) n
    let J := foldCutoff A P D₀ (Real.exp (-8*s)) j n
    let Y := lowerCutoff A P D₀ (Real.exp (-8*s)) n
    let H := Real.exp (16*s)
    let B := quantifiedFilterMatrixHeight A hN qs r L U j J n d
    let F := closedFilterComplexity A hN P qs r L U j J n d
    let M := Real.exp (Real.exp ((commonGeometryGrowthConstant A hN P b C+5)*s^2))
    0<Y ∧ B*(H+2)≤M ∧ H≤M ∧ Y⁻¹≤M ∧ F≤M := by
  let D₀ : ℝ := 2*d+2
  let n := newtonDepth A P D₀ (Real.exp (-8*s))
  let j := reconstructionDepth A P D₀ (Real.exp (-8*s)) n
  let J := foldCutoff A P D₀ (Real.exp (-8*s)) j n
  let Y := lowerCutoff A P D₀ (Real.exp (-8*s)) n
  let H := Real.exp (16*s)
  let B := quantifiedFilterMatrixHeight A hN qs r L U j J n d
  let F := closedFilterComplexity A hN P qs r L U j J n d
  let K := commonGeometryGrowthConstant A hN P b C
  let M₀ := Real.exp (Real.exp (K*s^2))
  have hK : 0≤K := commonGeometryGrowthConstant_nonneg A hN P hb hC
  have hm := normalizedMatrixGrowthConstant_nonneg A hN P hC
  have hc := normalizedComplexityGrowthConstant_nonneg A P hC
  have hMK : 26+4*normalizedMatrixGrowthConstant A hN P C+2*b+C≤K := by
    dsimp [K,commonGeometryGrowthConstant]; nlinarith [abs_nonneg (lowerInverseGrowthConstant A P C)]
  have hCK : 16+4*normalizedComplexityGrowthConstant A P C+b+C≤K := by
    dsimp [K,commonGeometryGrowthConstant]; nlinarith [abs_nonneg (lowerInverseGrowthConstant A P C)]
  have hYK : |lowerInverseGrowthConstant A P C|+4≤K := by
    dsimp [K,commonGeometryGrowthConstant]; nlinarith
  have hHK : (17:ℝ)≤K := by
    dsimp [K,commonGeometryGrowthConstant]; nlinarith [abs_nonneg (lowerInverseGrowthConstant A P C)]
  have hfull := growing_full_filter A hN P qs r L U hb hC hs d hd hrowsH hrowsM hrowsL
  have hB : B≤M₀ := hfull.1.trans (double_exp_mono hMK)
  have hF : F≤M₀ := hfull.2.trans (double_exp_mono hCK)
  have hY : 0<Y := (countFilterError_schedule A P d (Real.exp_pos (-8*s))).2.1
  have hYi : Y⁻¹≤M₀ := by
    apply (growing_lower_inverse A P hC hs d hd).trans
    apply (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity : 0≤s^4))).trans
    apply (Real.exp_le_exp.mpr ?_).trans (double_exp_mono hYK)
    simpa using polynomial_mul_exp_quadratic_le 4 (C:=0)
      (abs_nonneg (lowerInverseGrowthConstant A P C)) hs
  have hH : H≤M₀ := by
    apply (Real.exp_le_exp.mpr ?_).trans (double_exp_mono hHK)
    have hp := polynomial_mul_exp_quadratic_le 1 (b:=16) (C:=0) (by norm_num) hs
    norm_num at hp
    exact hp
  have hM₀ : 1≤M₀ := Real.one_le_exp (Real.exp_nonneg _)
  have hstep : M₀≤Real.exp (Real.exp ((K+5)*s^2)) := double_exp_mono (by linarith)
  have hB0 : 0≤B := quantifiedFilterMatrixHeight_nonneg A hN qs r L U j J n d
  have hD : B*(H+2)≤Real.exp (Real.exp ((K+5)*s^2)) := by
    have hh : B*(H+2)≤3*M₀^2 := by
      have hmul := mul_le_mul hB (show H+2≤M₀+2 by linarith) (by dsimp [H]; positivity) (by positivity)
      nlinarith
    apply hh.trans
    convert polynomial_double_exp_le 2 (c:=3) (by norm_num) hK hs using 1
    congr 2
    ring
  exact ⟨hY,hD,hH.trans hstep,hYi.trans hstep,hF.trans hstep⟩

#print axioms growing_scheduled_geometry

end QuantitativeHolomorphic.Schedule
