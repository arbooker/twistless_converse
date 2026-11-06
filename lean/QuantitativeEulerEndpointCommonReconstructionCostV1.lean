module

public import QuantitativeEulerEndpointCommonReconstructionV1
public import QuantitativeHolomorphicGrowingFilterScheduleV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointCommonReconstruction
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic QuantitativeHolomorphic.Schedule AsymptoticFiniteBranch

theorem normalized_mass {E : Expression} (hE : expressionBound E≤1) (n : ℕ) :
    expressionBound (normalizedReconstructionExpression E n)≤(4:ℝ)^(4^n) := by
  have hm := expressionBound_nonneg E
  have hb : 3+expressionBound E^2≤4 := by nlinarith
  have hp := pow_le_pow_left₀ (by positivity : 0≤3+expressionBound E^2) hb (4^n)
  exact (normalizedReconstructionExpression_complexity E n).1.trans
    ((mul_le_mul hE hp (by positivity) zero_le_one).trans_eq (one_mul _))

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

/-- The same actual common approximation has coefficient mass and integer
matrix height at most exp(K*s^12), with K fixed before s and the sector. -/
theorem exists_cost_bound (hN : 0<N) :
    ∃ K : ℝ,0≤K ∧ ∀ s : ℝ,1≤s → ∀ e : Sector N,
      expressionBound (expression A P hN s e)≤Real.exp (K*s^12) ∧
      ExpressionMatrixBound (expression A P hN s e) (Real.exp (K*s^12)) := by
  let Kc := normalizedComplexityGrowthConstant A P 0
  let Km := normalizedMatrixGrowthConstant A hN P 0
  have hKc : 0≤Kc := normalizedComplexityGrowthConstant_nonneg A P (by norm_num : (0:ℝ)≤0)
  have hKm : 0≤Km := normalizedMatrixGrowthConstant_nonneg A hN P (by norm_num : (0:ℝ)≤0)
  refine ⟨Kc+Km,add_nonneg hKc hKm,?_⟩
  intro s hs e
  let t := Real.exp (-8*s)
  let n := newtonDepth A P 2 t
  let j := reconstructionDepth A P 2 t n
  let J := foldCutoff A P 2 t j n
  let Y := lowerCutoff A P 2 t n
  have hm : expressionBound (expression A P hN s e)≤(4:ℝ)^(4^n) :=
    normalized_mass (scaledCutCountExpression_mass_le_one A hN P e Y j J) n
  have hc := (growing_normalized_complexity A P (by norm_num : (0:ℝ)≤0) hs 0 (by norm_num)).1
  norm_num only [Nat.cast_zero,mul_zero,zero_add] at hc
  have hmatrix : ExpressionMatrixBound (expression A P hN s e)
      (normalizedCountMatrixHeight A hN j J n) :=
    expressionMatrixBound_normalized (rawCountMatrixHeight_one_le A hN j J)
      (scaledCutCountExpression_explicit_height A hN P e Y j J) n
  have hmg := growing_normalized_matrix_height A hN P (by norm_num : (0:ℝ)≤0) hs 0 (by norm_num)
  norm_num only [Nat.cast_zero,mul_zero,zero_add] at hmg
  have hce : Kc*s^12≤(Kc+Km)*s^12 := by nlinarith [pow_nonneg (by linarith : 0≤s) 12]
  have hme : Km*s^12≤(Kc+Km)*s^12 := by nlinarith [pow_nonneg (by linarith : 0≤s) 12]
  exact ⟨(hm.trans hc).trans (Real.exp_le_exp.mpr hce),
    hmatrix.mono (hmg.trans (Real.exp_le_exp.mpr hme))⟩

#print axioms normalized_mass
#print axioms exists_cost_bound
end QuantitativeEulerEndpointCommonReconstruction
