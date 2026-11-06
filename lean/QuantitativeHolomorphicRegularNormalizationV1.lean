module

public import QuantitativeHolomorphicFiniteNormalizationV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open ContinuousLinearMap

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)

/-- Regular truncation with exactly the same depth and symmetric fold cutoff. -/
def finiteRegularCountReconstruction (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (z : UpperHalfPlane) (d J : ℕ) :
    AsymptoticRegularReconstruction.TerminalSpace A
      (AsymptoticReconstructedCount.parameters A P) z →L[ℂ] AsymptoticRegularFoldedLow.Space :=
  let P' := AsymptoticReconstructedCount.parameters A P
  (AsymptoticRegularInclusion.inclusion P'.epsilon_pos z).comp
    ((AsymptoticRegularReconstruction.finiteFoldFull A hN P' (multiplier e) d
      (Finset.Icc (-(J : ℤ)) J) z).comp
        (AsymptoticRegularReconstruction.TerminalSpace A P' z).subtypeL)

theorem regular_full_subtype (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (z : UpperHalfPlane) :
    (AsymptoticRegularReconstruction.full A hN P (multiplier e) z).comp
      (AsymptoticRegularReconstruction.TerminalSpace A P z).subtypeL =
        AsymptoticRegularReconstruction.extension A hN P (multiplier e) z := by
  apply ContinuousLinearMap.ext
  intro g
  rw [comp_apply, Submodule.subtypeL_apply,
    AsymptoticRegularReconstruction.full_eq_extension]
  congr 1
  apply Subtype.ext
  exact (AsymptoticOrbitRegion.mem_space _ _ _).1 g.property

theorem finiteRegularCountReconstruction_error (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (z : UpperHalfPlane) (d J : ℕ) (hJ : 0 < J) :
    ‖finiteRegularCountReconstruction A hN P e z d J -
      AsymptoticRegularReconstruction.includedExtension A hN
        (AsymptoticReconstructedCount.parameters A P) (multiplier e) z‖ ≤
      countReconstructionError A P d J := by
  have hraw := regular_reconstruction_explicit_error A hN
    (AsymptoticReconstructedCount.parameters A P)
    (AsymptoticReconstructedCount.parameters_bound A P).le
    (multiplier e) (fun q _ => multiplier_norm e q) z d J hJ
  rw [finiteRegularCountReconstruction, AsymptoticRegularReconstruction.includedExtension,
    ← regular_full_subtype A hN _ e z, ← comp_sub, ← sub_comp]
  apply le_trans (opNorm_comp_le _ _)
  apply le_trans (mul_le_mul_of_nonneg_right
    (AsymptoticRegularInclusion.inclusion_norm_le _ z) (norm_nonneg _))
  rw [one_mul]
  apply le_trans (opNorm_comp_le _ _)
  apply le_trans (mul_le_mul_of_nonneg_left
    (AsymptoticRegularReconstruction.terminal_inclusion_norm_le A _ z) (norm_nonneg _))
  simpa only [mul_one, countReconstructionError] using hraw

def scaledFiniteRegularCountReconstruction (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (z : UpperHalfPlane) (d J : ℕ) :=
  (countReconstructionBound A P)⁻¹ • finiteRegularCountReconstruction A hN P e z d J

theorem scaledFiniteRegularCountReconstruction_error (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (z : UpperHalfPlane) (d J : ℕ) (hJ : 0 < J) :
    ‖scaledFiniteRegularCountReconstruction A hN P e z d J -
      scaledRegularCountReconstruction A hN P e z‖ ≤ countReconstructionError A P d J := by
  have hb := countReconstructionBound_one_le A P
  exact scaled_difference_norm_le _ _ (inv_nonneg.2 (zero_le_one.trans hb))
    (inv_le_one_of_one_le₀ hb) (finiteRegularCountReconstruction_error A hN P e z d J hJ)

/-- Shared closed exact-to-finite normalization error at every orbit root. -/
theorem finite_normalizedRegularCountReconstruction_closed_error (hN : 0 < N)
    (P : Parameters A) (e : Sector N) (z : UpperHalfPlane) (n d J : ℕ) (hJ : 0 < J)
    (hsmall : countReconstructionError A P d J ≤ 1) :
    ‖polynomialNormalizedReconstruction
        (scaledFiniteRegularCountReconstruction A hN P e z d J) n -
      normalizedReconstruction (scaledRegularCountReconstruction A hN P e z)‖ ≤
      countReconstructionError A P d J * (1 + 3 * (3 ^ n : ℕ)) * (7 : ℝ) ^ (4 ^ n) +
        (1 - countGramLower A P) ^ (2 ^ n) / Real.sqrt (countGramLower A P) := by
  have herr := scaledFiniteRegularCountReconstruction_error A hN P e z d J hJ
  have hb := scaledRegularCountReconstruction_bounds A hN P e z
  have hδ0 : 0 ≤ countReconstructionError A P d J :=
    (norm_nonneg (scaledFiniteRegularCountReconstruction A hN P e z d J -
      scaledRegularCountReconstruction A hN P e z)).trans herr
  have hv : ‖scaledFiniteRegularCountReconstruction A hN P e z d J‖ ≤ 2 := by
    have ht := norm_le_norm_sub_add (scaledFiniteRegularCountReconstruction A hN P e z d J)
      (scaledRegularCountReconstruction A hN P e z)
    linarith [hb.1]
  apply (finite_polynomial_normalization_error _ _ (countGramLower_pos A P)
    (countGramLower_le_one A P) hb.2 hb.1 hv herr n).trans
  apply add_le_add _ le_rfl
  have hm := polynomialMass_inverseSqrt_le (by norm_num : (0 : ℝ) ≤ 4) n
  have hs := polynomialSensitivity_inverseSqrt_le (by norm_num : (0 : ℝ) ≤ 4) n
  norm_num only [show (3 + 4 : ℝ) = 7 by norm_num] at hm hs
  have hh := mul_le_mul_of_nonneg_left
    (add_le_add hm (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 3))) hδ0
  convert hh using 1
  ring

#print axioms finiteRegularCountReconstruction_error
#print axioms finite_normalizedRegularCountReconstruction_closed_error

end QuantitativeHolomorphic
