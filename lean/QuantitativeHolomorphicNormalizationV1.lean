module

public import QuantitativeHolomorphicGramV1
public import AsymptoticReconstructedCountV1
public import AsymptoticRegularIncludedReconstructionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticDiagonalTrace AsymptoticObservation
open ContinuousLinearMap

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)

/-- The fixed certificate norm bound, independent of weight and sector. -/
def countReconstructionBound (P : Parameters A) : ℝ :=
  1 + 2 * AsymptoticCertificateOperators.terminalConstant A
    (AsymptoticReconstructedCount.parameters A P)

theorem countReconstructionBound_one_le (P : Parameters A) :
    1 ≤ countReconstructionBound A P := by
  have ht : 0 ≤ AsymptoticCertificateOperators.terminalConstant A
      (AsymptoticReconstructedCount.parameters A P) := by
    unfold AsymptoticCertificateOperators.terminalConstant
    positivity
  unfold countReconstructionBound
  linarith

/-- The literal map used in the established Euler count-to-trace theorem. -/
def countReconstruction (hN : 0 < N) (P : Parameters A) (h : ℕ) (e : Sector N) :
    AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε
      →L[ℂ] AsymptoticCylinder.Space :=
  (inclusion (AsymptoticReconstructedCount.parameters A P).epsilon_pos).comp
    (AsymptoticReconstructedCount.reconstruction A hN P h e)

theorem countReconstruction_norm_le (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) :
    ‖countReconstruction A hN P h e‖ ≤ countReconstructionBound A P := by
  apply (opNorm_comp_le _ _).trans
  exact (mul_le_mul (inclusion_norm_le _)
    (AsymptoticReconstructedCount.reconstruction_norm_le A hN P h e)
    (norm_nonneg (AsymptoticReconstructedCount.reconstruction A hN P h e)) zero_le_one).trans_eq (one_mul _)

def scaledCountReconstruction (hN : 0 < N) (P : Parameters A) (h : ℕ) (e : Sector N) :=
  (countReconstructionBound A P)⁻¹ • countReconstruction A hN P h e

def countGramLower (P : Parameters A) : ℝ := (countReconstructionBound A P)⁻¹ ^ 2

theorem countGramLower_pos (P : Parameters A) : 0 < countGramLower A P := by
  exact sq_pos_of_pos (inv_pos.2 (zero_lt_one.trans_le (countReconstructionBound_one_le A P)))

theorem countGramLower_le_one (P : Parameters A) : countGramLower A P ≤ 1 := by
  have hb := countReconstructionBound_one_le A P
  have hi : (countReconstructionBound A P)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb
  simpa only [one_pow, countGramLower] using pow_le_pow_left₀ (inv_nonneg.2 (zero_le_one.trans hb)) hi 2

theorem scaledCountReconstruction_bounds (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) :
    ‖scaledCountReconstruction A hN P h e‖ ≤ 1 ∧
      ∀ v, countGramLower A P * ‖v‖ ^ 2 ≤
        ‖scaledCountReconstruction A hN P h e v‖ ^ 2 :=
  scaled_reconstruction_bounds (countReconstruction A hN P h e)
    (zero_lt_one.trans_le (countReconstructionBound_one_le A P))
    (countReconstruction_norm_le A hN P h e)
    (AsymptoticReconstructedCount.terminal_lower_bound A hN P h e)

/-- Exact isometric reconstruction, with no norm or spectrum input left open. -/
def normalizedCountReconstruction (hN : 0 < N) (P : Parameters A) (h : ℕ) (e : Sector N) :=
  normalizedReconstruction (scaledCountReconstruction A hN P h e)

theorem normalizedCountReconstruction_norm (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (v) :
    ‖normalizedCountReconstruction A hN P h e v‖ = ‖v‖ :=
  normalizedReconstruction_norm _ (countGramLower_pos A P)
    (scaledCountReconstruction_bounds A hN P h e).2 v

/-- The approximation bound is proved for the actual count reconstruction,
uniformly in the holomorphic weight and the ramified sign sector. -/
theorem normalizedCountReconstruction_polynomial_error (hN : 0 < N) (P : Parameters A)
    (h n : ℕ) (e : Sector N) :
    ‖polynomialNormalizedReconstruction (scaledCountReconstruction A hN P h e) n -
      normalizedCountReconstruction A hN P h e‖ ≤
      (1 - countGramLower A P) ^ (2 ^ n) / Real.sqrt (countGramLower A P) :=
  polynomialNormalizedReconstruction_error _ (countGramLower_pos A P)
    (countGramLower_le_one A P) (scaledCountReconstruction_bounds A hN P h e).2
    (scaledCountReconstruction_bounds A hN P h e).1 n

/-- Normalization preserves every vector of the literal Euler cylinder
sector, not only the selected eigenpackages counted by the Euler set. -/
theorem normalizedCountReconstruction_sector (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N)
    (w : holomorphicSpace (2*h) ((AsymptoticReconstructedCount.parameters A P).s+4)
      (by positivity : 0 < 4*Real.pi) (AsymptoticReconstructedCount.parameters A P).epsilon_pos)
    (hw : w ∈ eulerCylinderSector (AsymptoticReconstructedCount.parameters A P) h e) :
    ∃ g, normalizedCountReconstruction A hN P h e g = (w : AsymptoticCylinder.Space) := by
  obtain ⟨g, hg⟩ := AsymptoticReconstructedCount.reconstruct_sector A hN P h e w hw
  let R := scaledCountReconstruction A hN P h e
  let v := countReconstructionBound A P • g
  refine ⟨(R.adjoint.comp R).comp (inverseSqrtCFC (R.adjoint.comp R)) v, ?_⟩
  change normalizedReconstruction R _ = _
  rw [normalizedReconstruction_reconstruct R (countGramLower_pos A P)
    (scaledCountReconstruction_bounds A hN P h e).2]
  have hb : countReconstructionBound A P ≠ 0 :=
    (zero_lt_one.trans_le (countReconstructionBound_one_le A P)).ne'
  simpa only [R, v, scaledCountReconstruction, smul_apply, map_smul_of_tower,
    smul_smul, inv_mul_cancel₀ hb, one_smul, countReconstruction] using hg

/-- The same fixed scaling and Newton polynomials work at every regular
orbit root, with the same coefficient bound as in the physical realization. -/
def scaledRegularCountReconstruction (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (z : UpperHalfPlane) :=
  (countReconstructionBound A P)⁻¹ •
    AsymptoticRegularReconstruction.includedExtension A hN
      (AsymptoticReconstructedCount.parameters A P) (multiplier e) z

theorem scaledRegularCountReconstruction_bounds (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (z : UpperHalfPlane) :
    ‖scaledRegularCountReconstruction A hN P e z‖ ≤ 1 ∧
      ∀ v, countGramLower A P * ‖v‖ ^ 2 ≤
        ‖scaledRegularCountReconstruction A hN P e z v‖ ^ 2 := by
  have hc := AsymptoticRegularReconstruction.parameters_contraction A hN P
    (multiplier e) (fun q _ => multiplier_norm e q) z
  exact scaled_reconstruction_bounds _
    (zero_lt_one.trans_le (countReconstructionBound_one_le A P))
    (AsymptoticRegularReconstruction.includedExtension_norm_le A hN _
      (multiplier e) (fun q _ => multiplier_norm e q) z hc)
    (AsymptoticRegularReconstruction.includedExtension_norm_ge A hN _
      (multiplier e) z (hc.trans (by norm_num)))

theorem normalizedRegularCountReconstruction_norm (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (z : UpperHalfPlane) (v) :
    ‖normalizedReconstruction (scaledRegularCountReconstruction A hN P e z) v‖ = ‖v‖ :=
  normalizedReconstruction_norm _ (countGramLower_pos A P)
    (scaledRegularCountReconstruction_bounds A hN P e z).2 v

theorem normalizedRegularCountReconstruction_polynomial_error (hN : 0 < N)
    (P : Parameters A) (e : Sector N) (z : UpperHalfPlane) (n : ℕ) :
    ‖polynomialNormalizedReconstruction (scaledRegularCountReconstruction A hN P e z) n -
      normalizedReconstruction (scaledRegularCountReconstruction A hN P e z)‖ ≤
      (1 - countGramLower A P) ^ (2 ^ n) / Real.sqrt (countGramLower A P) :=
  polynomialNormalizedReconstruction_error _ (countGramLower_pos A P)
    (countGramLower_le_one A P) (scaledRegularCountReconstruction_bounds A hN P e z).2
    (scaledRegularCountReconstruction_bounds A hN P e z).1 n

#print axioms normalizedRegularCountReconstruction_norm
#print axioms normalizedRegularCountReconstruction_polynomial_error

#print axioms normalizedCountReconstruction_norm
#print axioms normalizedCountReconstruction_polynomial_error
#print axioms normalizedCountReconstruction_sector

end QuantitativeHolomorphic
