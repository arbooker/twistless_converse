module

public import QuantitativeMaassRegularOriginalRowFamilyV1
public import QuantitativeEulerEndpointPhysicalCompressedGramV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass.RawPrepared
open UpperHalfPlane ContinuousLinearMap AsymptoticSectorSigns
open FinitenessCertificate FinitenessGlobalHeight
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointPhysicalNormalization
open AsymptoticRegularCompactBranch (Space)
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (e : Sector N) (x : ℍ) (V E : Space→L[ℂ]Space)
    (hrows : ∀ (r : AsymptoticCompactObservationCount.Row N) (s : Set ℍ) (hs : IsCompact s),
      AsymptoticRegularObservationRows.row (NeZero.pos N) r e hs
        (AsymptoticReconstructedCount.parameters A P).epsilon_pos
        ((AsymptoticReconstructedCount.parameters A P).s+3) x*V*E=0)

include hrows in
theorem replacementGram_original_zero {s : Set ℍ} (hs : IsCompact s)
    (l : List (EligiblePrime N)) (C : ℕ→ℝ) : replacementGram A P e hs l C x V*E=0 := by
  rw [replacementGram_expansion,gram_sum_compression,gram_sum_compression,←add_mul,←mul_add]
  apply original_gram_kills
  · intro i
    ext1 v
    apply regular_baseline_zero_of_original_rows e
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+3) x (V (E v)) _ hs i
    intro r s hs
    exact congrArg (fun T : Space→L[ℂ]Space => T v) (hrows r s hs)
  · intro i
    ext1 v
    apply regular_packet_zero_of_original_rows e
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+3) x (V (E v)) _ hs l i
    intro r s hs
    exact congrArg (fun T : Space→L[ℂ]Space => T v) (hrows r s hs)

include hrows in
/-- Replacing the exact reconstruction costs only its operator norm error,
with no factor for the number of original rows. -/
theorem replacementGram_original_residual {s : Set ℍ} (hs : IsCompact s)
    (l : List (EligiblePrime N)) (C : ℕ→ℝ)
    (hC : ∀ i,‖uncomposedCombinedRows A P e hs l i x‖≤C i)
    (U : Space→L[ℂ]Space) (hV : ‖V‖≤1) (hU : ‖U‖≤1) :
    ‖replacementGram A P e hs l C x U*E‖≤2*‖U-V‖*‖E‖ := by
  have hz := replacementGram_original_zero A P e x V E hrows hs l C
  have he : replacementGram A P e hs l C x U*E=
      (replacementGram A P e hs l C x U-replacementGram A P e hs l C x V)*E := by
    rw [sub_mul,hz,sub_zero]
  rw [he]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
    (replacementGram_difference A P e hs l C x hC V U hV hU) (norm_nonneg E))

#print axioms replacementGram_original_zero
#print axioms replacementGram_original_residual
end QuantitativeMaass.RawPrepared
