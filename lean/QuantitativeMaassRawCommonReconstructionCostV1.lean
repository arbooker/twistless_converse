module

public import QuantitativeMaassRawCommonReconstructionV1
public import QuantitativeEulerEndpointCommonReconstructionCostV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass.RawCommonReconstruction
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic QuantitativeHolomorphic.Schedule AsymptoticFiniteBranch
open QuantitativeMaass.EulerHilbert.FullTerminal

private theorem matrixBound_unscale {E : Expression} {B : ℝ} (a : ℂ)
    (h : ExpressionMatrixBound (scaleExpression a E) B) : ExpressionMatrixBound E B := by
  intro b hb
  exact h (scale a b) (List.mem_map.mpr ⟨b,hb,rfl⟩)

private theorem matrixBound_remove_identity {E : Expression} {B : ℝ}
    (u : Branch) (hu : u.label=1)
    (h : ExpressionMatrixBound (composeExpression [u] E) B) : ExpressionMatrixBound E B := by
  intro b hb
  have hm : compose u b∈composeExpression [u] E := by
    apply List.mem_flatMap.mpr
    exact ⟨u,by simp,List.mem_map.mpr ⟨b,hb,rfl⟩⟩
  obtain ⟨M,hM,hB⟩ := h (compose u b) hm
  refine ⟨M,?_,hB⟩
  simpa only [compose,hu,mul_one] using hM

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

theorem scaled_mass (hN : 0<N) (e : Sector N) (j J : ℕ) :
    expressionBound (scaledFullExpression A hN P e j J)≤1 := by
  have h := scaledCutCountExpression_mass_le_one A hN P e 0 j J
  simpa only [scaledCutCountExpression,scaledFullExpression,expressionBound_scale,
    expressionBound_cutFullExpression] using h

/-- Removing identity-labelled weight and height multipliers cannot enlarge
matrix height. This transfers the existing explicit certificate height. -/
theorem scaled_matrix (hN : 0<N) (e : Sector N) (j J : ℕ) :
    ExpressionMatrixBound (scaledFullExpression A hN P e j J)
      (rawCountMatrixHeight A hN j J) := by
  have h := scaledCutCountExpression_explicit_height A hN P e 0 j J
  have hu := matrixBound_unscale ((countReconstructionBound A P)⁻¹:ℝ) h
  have hh := matrixBound_remove_identity (heightCorner 0) rfl hu
  have hw := matrixBound_remove_identity
    (weight (AsymptoticReconstructedCount.parameters A P).epsilon_pos) rfl hh
  exact hw.scale _

/-- Coefficient mass and integer matrix height of the actual common RAW
Maass expression have a uniform exp(K*s^12) bound. -/
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
  have hm : expressionBound (expression A P hN s e)≤(4:ℝ)^(4^n) :=
    QuantitativeEulerEndpointCommonReconstruction.normalized_mass (scaled_mass A P hN e j J) n
  have hc := (growing_normalized_complexity A P (by norm_num : (0:ℝ)≤0) hs 0 (by norm_num)).1
  norm_num only [Nat.cast_zero,mul_zero,zero_add] at hc
  have hmatrix : ExpressionMatrixBound (expression A P hN s e)
      (normalizedCountMatrixHeight A hN j J n) :=
    expressionMatrixBound_normalized (rawCountMatrixHeight_one_le A hN j J)
      (scaled_matrix A P hN e j J) n
  have hmg := growing_normalized_matrix_height A hN P (by norm_num : (0:ℝ)≤0) hs 0 (by norm_num)
  norm_num only [Nat.cast_zero,mul_zero,zero_add] at hmg
  have hce : Kc*s^12≤(Kc+Km)*s^12 := by nlinarith [pow_nonneg (by linarith : 0≤s) 12]
  have hme : Km*s^12≤(Kc+Km)*s^12 := by nlinarith [pow_nonneg (by linarith : 0≤s) 12]
  exact ⟨(hm.trans hc).trans (Real.exp_le_exp.mpr hce),
    hmatrix.mono (hmg.trans (Real.exp_le_exp.mpr hme))⟩

#print axioms scaled_mass
#print axioms scaled_matrix
#print axioms exists_cost_bound
end QuantitativeMaass.RawCommonReconstruction
