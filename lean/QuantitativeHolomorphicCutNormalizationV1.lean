module

public import QuantitativeHolomorphicFiniteNormalizationV1
public import AsymptoticFiniteCylinderTransportV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open ContinuousLinearMap

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)

/-- The cutoff error is added to the explicit depth/fold error. -/
def cutCountReconstructionError (P : Parameters A) (Y : ℝ) (d J : ℕ) : ℝ :=
  countReconstructionError A P d J +
    Y / (AsymptoticReconstructedCount.parameters A P).ε * countReconstructionBound A P

def scaledCutFiniteCountReconstruction (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (Y : ℝ) (d J : ℕ) :=
  (countReconstructionBound A P)⁻¹ •
    AsymptoticReconstructedCount.finiteCutReconstruction A hN P h e Y d
      (Finset.Icc (-(J : ℤ)) J)

theorem cutFiniteCountReconstruction_error (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (Y : ℝ) (hY : 0 ≤ Y) (d J : ℕ) (hJ : 0 < J) :
    ‖AsymptoticReconstructedCount.finiteCutReconstruction A hN P h e Y d
        (Finset.Icc (-(J : ℤ)) J) - countReconstruction A hN P h e‖ ≤
      cutCountReconstructionError A P Y d J := by
  have hbase := AsymptoticReconstructedCount.finiteCutBaseReconstruction_error
    A hN P h e Y d (Finset.Icc (-(J : ℤ)) J)
  have hraw := physical_reconstruction_explicit_error A hN
    (AsymptoticReconstructedCount.parameters A P)
    (AsymptoticReconstructedCount.parameters_bound A P).le
    (multiplier e) (fun q _ => multiplier_norm e q) (h+1) d J hJ
  have hf : ‖AsymptoticReconstructedCount.finiteCutReconstruction A hN P h e Y d
      (Finset.Icc (-(J : ℤ)) J) -
      AsymptoticReconstructedCount.cutReconstruction A hN P h e Y‖ ≤
      countReconstructionError A P d J := by
    rw [AsymptoticReconstructedCount.finiteCutReconstruction,
      AsymptoticReconstructedCount.cutReconstruction_eq_weighted, ← comp_sub]
    apply (opNorm_comp_le _ _).trans
    apply (mul_le_mul_of_nonneg_right
      (AsymptoticCylinder.inclusion_norm_le _) (norm_nonneg _)).trans
    rw [one_mul]
    exact hbase.trans hraw
  have hc := AsymptoticReconstructedCount.cutReconstruction_error A hN P h e Y hY
  apply (norm_sub_le_norm_sub_add_norm_sub _
    (AsymptoticReconstructedCount.cutReconstruction A hN P h e Y) _).trans
  apply add_le_add hf
  rw [norm_sub_rev]
  simpa only [countReconstruction, AsymptoticReconstructedCount.includedReconstruction,
    countReconstructionBound] using hc

theorem scaledCutFiniteCountReconstruction_error (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (Y : ℝ) (hY : 0 ≤ Y) (d J : ℕ) (hJ : 0 < J) :
    ‖scaledCutFiniteCountReconstruction A hN P h e Y d J -
      scaledCountReconstruction A hN P h e‖ ≤ cutCountReconstructionError A P Y d J := by
  have hb := countReconstructionBound_one_le A P
  exact scaled_difference_norm_le _ _ (inv_nonneg.2 (zero_le_one.trans hb))
    (inv_le_one_of_one_le₀ hb) (cutFiniteCountReconstruction_error A hN P h e Y hY d J hJ)

theorem scaledCutFiniteCountReconstruction_norm_le (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (Y : ℝ) (d J : ℕ) :
    ‖scaledCutFiniteCountReconstruction A hN P h e Y d J‖ ≤ 1 :=
  scaled_norm_le_one _ (zero_lt_one.trans_le (countReconstructionBound_one_le A P))
    (AsymptoticReconstructedCount.finiteCutReconstruction_norm_le A hN P h e Y d _)

/-- The actual compact-height, finite-depth, finite-fold approximation is
normalized by an explicit polynomial.  No small-error assumption is needed:
its contraction bound follows from the actual finite reconstruction estimates. -/
theorem cut_normalizedCountReconstruction_closed_error (hN : 0 < N) (P : Parameters A)
    (h n : ℕ) (e : Sector N) (Y : ℝ) (hY : 0 ≤ Y) (d J : ℕ) (hJ : 0 < J) :
    ‖polynomialNormalizedReconstruction (scaledCutFiniteCountReconstruction A hN P h e Y d J) n -
      normalizedCountReconstruction A hN P h e‖ ≤
      cutCountReconstructionError A P Y d J * (1 + 3 * (3 ^ n : ℕ)) * (7 : ℝ) ^ (4 ^ n) +
        (1 - countGramLower A P) ^ (2 ^ n) / Real.sqrt (countGramLower A P) :=
  finite_polynomial_normalization_closed_error _ _ (countGramLower_pos A P)
    (countGramLower_le_one A P) (scaledCountReconstruction_bounds A hN P h e).2
    (scaledCountReconstruction_bounds A hN P h e).1
    ((scaledCutFiniteCountReconstruction_norm_le A hN P h e Y d J).trans (by norm_num))
    (scaledCutFiniteCountReconstruction_error A hN P h e Y hY d J hJ) n

#print axioms cutFiniteCountReconstruction_error
#print axioms cut_normalizedCountReconstruction_closed_error

end QuantitativeHolomorphic
