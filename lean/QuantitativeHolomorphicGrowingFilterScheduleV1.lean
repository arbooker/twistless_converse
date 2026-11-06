module

public import QuantitativeHolomorphicGrowingClosedComplexityV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Schedule

open FinitenessCertificate FinitenessGlobalHeight AsymptoticCompactObservationCount

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) {ι : Type*}

theorem normalizedComplexityGrowthConstant_nonneg (P : Parameters A) {C : ℝ} (hC : 0≤C) :
    0≤normalizedComplexityGrowthConstant A P C := by
  have hL := reconstructionGrowthConstant_nonneg A P hC
  have hF := foldGrowthConstant_nonneg A P hC
  have hl : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  unfold normalizedComplexityGrowthConstant rawLengthGrowthConstant
  positivity

theorem normalizedMatrixGrowthConstant_nonneg (hN : 0<N) (P : Parameters A) {C : ℝ} (hC : 0≤C) :
    0≤normalizedMatrixGrowthConstant A hN P C := by
  have hL := reconstructionGrowthConstant_nonneg A P hC
  have hF := foldGrowthConstant_nonneg A P hC
  have hc : 0≤certificateMatrixBase A hN := le_trans zero_le_one
    (Classical.choose_spec (scaledCutCountExpression_uniform_matrix_height A hN)).1
  unfold normalizedMatrixGrowthConstant rawMatrixGrowthConstant
  positivity

/-- The literal scheduled filter: its integer matrix height and total
coefficient-mass/word complexity. Only the three concrete row aggregates
remain as growing arithmetic/geometric inputs. -/
theorem growing_full_filter (hN : 0<N) (P : Parameters A)
    (qs : Finset ι) (r : ι → Row N) (L U : ℝ) {b C s : ℝ}
    (hb : 0≤b) (hC : 0≤C) (hs : 1≤s) (d : ℕ)
    (hd : (d:ℝ)≤Real.exp (C*s^2))
    (hrowsH : (∑ i∈qs,quantifiedRowHeight hN (r i) L U)≤Real.exp (b*s^2))
    (hrowsM : (∑ i∈qs,(quantifiedRowMass hN (r i) L U
      ((AsymptoticReconstructedCount.parameters A P).s+4))^2)≤Real.exp (b*s^2))
    (hrowsL : (∑ i∈qs,(quantifiedRowLength hN (r i) L U:ℝ)^2)≤Real.exp (b*s^2)) :
    let D : ℝ := 2*d+2
    let n := newtonDepth A P D (Real.exp (-8*s))
    let j := reconstructionDepth A P D (Real.exp (-8*s)) n
    let J := foldCutoff A P D (Real.exp (-8*s)) j n
    quantifiedFilterMatrixHeight A hN qs r L U j J n d≤
      Real.exp (Real.exp ((26+4*normalizedMatrixGrowthConstant A hN P C+2*b+C)*s^2)) ∧
    closedFilterComplexity A hN P qs r L U j J n d≤
      Real.exp (Real.exp ((16+4*normalizedComplexityGrowthConstant A P C+b+C)*s^2)) := by
  dsimp only
  constructor
  · exact quantifiedFilterMatrixHeight_growth A hN qs r L U _ _ _ d
      (normalizedMatrixGrowthConstant_nonneg A hN P hC) hb hC hs hd
      (growing_normalized_matrix_height A hN P hC hs d hd) hrowsH
  · have hh := growing_normalized_complexity A P hC hs d hd
    exact closedFilterComplexity_growth A hN P qs r L U _ _ _ d
      (normalizedComplexityGrowthConstant_nonneg A P hC) hb hC hs hd hh.1 hh.2 hrowsM hrowsL

#print axioms growing_full_filter

end QuantitativeHolomorphic.Schedule
