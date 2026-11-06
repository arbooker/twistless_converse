module

public import QuantitativeHolomorphicObservationApproximationV1
public import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open FinitenessCertificate FinitenessGlobalHeight Filter
open scoped Topology

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)

/-- The explicit depth and fold error can be made small. This existence lemma
is used only for closure of measurable covariant operator families; the trace
estimates retain the explicit error and all three truncation parameters. -/
theorem exists_countReconstructionError_lt (P : Parameters A) {ε : ℝ} (hε : 0 < ε) :
    ∃ j J : ℕ, 0 < J ∧ countReconstructionError A P j J < ε := by
  have ht : Tendsto (fun j : ℕ =>
      2 * AsymptoticCertificateOperators.terminalConstant A
        (AsymptoticReconstructedCount.parameters A P) * (1 / 2 : ℝ)^j)
      atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)).const_mul
      (2 * AsymptoticCertificateOperators.terminalConstant A
        (AsymptoticReconstructedCount.parameters A P))
  obtain ⟨j, hj⟩ := (ht.eventually (gt_mem_nhds (by linarith : (0:ℝ) < ε/2))).exists
  have hf := tendsto_const_div_atTop_nhds_zero_nat
    (reconstructionFoldTailConstant A (AsymptoticReconstructedCount.parameters A P) j)
  obtain ⟨J, hJ, hsmall⟩ := ((eventually_gt_atTop (0:ℕ)).and
    (hf.eventually (gt_mem_nhds (by linarith : (0:ℝ) < ε/2)))).exists
  exact ⟨j,J,hJ,by dsimp [countReconstructionError]; linarith⟩

/-- Even the double-exponent Newton defect converges to zero, with the actual
positive Gram lower bound supplied by the reconstruction. -/
theorem normalized_newton_defect_tendsto (P : Parameters A) :
    Tendsto (fun n : ℕ => (1-countGramLower A P)^(2^n) /
      Real.sqrt (countGramLower A P)) atTop (𝓝 0) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
    (sub_nonneg.mpr (countGramLower_le_one A P))
    (by linarith [countGramLower_pos A P] : 1-countGramLower A P < 1)
  have hi := hpow.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℕ)<2))
  simpa using hi.div_const (Real.sqrt (countGramLower A P))

/-- Common finite parameters work in every regular orbit and every physical
weight. Height zero is sufficient for this closure statement; positive compact
cutoffs and their quantitative costs are retained in the trace comparison. -/
theorem exists_normalizedCutError_lt (P : Parameters A) {ε : ℝ} (hε : 0 < ε) :
    ∃ n j J : ℕ, 0 < J ∧ normalizedCutError A P 0 j J n < ε := by
  obtain ⟨n, hn⟩ := ((normalized_newton_defect_tendsto A P).eventually
    (gt_mem_nhds (by linarith : (0:ℝ) < ε/2))).exists
  let C : ℝ := (1+3*(3^n:ℕ)) * 7^(4^n)
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨j,J,hJ,hsmall⟩ := exists_countReconstructionError_lt A P
    (div_pos (by linarith : (0:ℝ)<ε/2) hC)
  refine ⟨n,j,J,hJ,?_⟩
  have hmul := (lt_div_iff₀ hC).mp hsmall
  simp only [normalizedCutError,cutCountReconstructionError,zero_div,zero_mul,add_zero]
  dsimp [C] at hmul
  nlinarith

#print axioms exists_normalizedCutError_lt

end QuantitativeHolomorphic
