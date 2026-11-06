module

public import QuantitativeHolomorphicNormalizationV1
public import QuantitativeHolomorphicNewtonPerturbationV1
public import QuantitativeHolomorphicNewtonCoefficientsV1
public import QuantitativeHolomorphicReconstructionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open ContinuousLinearMap

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)

/-- Both reconstruction truncation parameters are explicit. -/
def countReconstructionError (P : Parameters A) (d J : ℕ) : ℝ :=
  reconstructionFoldTailConstant A (AsymptoticReconstructedCount.parameters A P) d / (J : ℝ) +
    2 * AsymptoticCertificateOperators.terminalConstant A
      (AsymptoticReconstructedCount.parameters A P) * (1 / 2 : ℝ) ^ d

/-- The finite integer-fold / Neumann-depth reconstruction transported to
the same terminal cylinder space as the literal count theorem. -/
def finiteCountReconstruction (hN : 0 < N) (P : Parameters A)
    (h d J : ℕ) (e : Sector N) :
    AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε
      →L[ℂ] AsymptoticCylinder.Space :=
  let P' := AsymptoticReconstructedCount.parameters A P
  (AsymptoticCylinder.inclusion P'.epsilon_pos).comp
    (AsymptoticCylinderLift.lift.toContinuousLinearMap.adjoint.comp
      ((AsymptoticGeometricReconstruction.finiteFoldExtension A hN P' (multiplier e) d
        (Finset.Icc (-(J : ℤ)) J) (h + 1)).comp
          (AsymptoticCylinderReconstruction.terminalLift A P')))

theorem finiteCountReconstruction_error (hN : 0 < N) (P : Parameters A)
    (h d J : ℕ) (hJ : 0 < J) (e : Sector N) :
    ‖finiteCountReconstruction A hN P h d J e - countReconstruction A hN P h e‖ ≤
      countReconstructionError A P d J := by
  have hraw := physical_reconstruction_explicit_error A hN
    (AsymptoticReconstructedCount.parameters A P)
    (AsymptoticReconstructedCount.parameters_bound A P).le
    (multiplier e) (fun q _ => multiplier_norm e q) (h + 1) d J hJ
  let P' := AsymptoticReconstructedCount.parameters A P
  let D := AsymptoticGeometricReconstruction.finiteFoldExtension A hN P' (multiplier e) d
      (Finset.Icc (-(J : ℤ)) J) (h + 1) -
    AsymptoticGeometricReconstruction.extension A hN P' (multiplier e) (h + 1)
  have he : finiteCountReconstruction A hN P h d J e - countReconstruction A hN P h e =
      (AsymptoticCylinder.inclusion P'.epsilon_pos).comp
        (AsymptoticCylinderLift.lift.toContinuousLinearMap.adjoint.comp
          (D.comp (AsymptoticCylinderReconstruction.terminalLift A P'))) := by
    simp only [finiteCountReconstruction, countReconstruction,
      AsymptoticReconstructedCount.reconstruction, AsymptoticCylinderReconstruction.extension,
      P', D, comp_sub, sub_comp]
  rw [he]
  apply le_trans (opNorm_comp_le _ _)
  apply le_trans (mul_le_mul_of_nonneg_right
    (AsymptoticCylinder.inclusion_norm_le P'.epsilon_pos) (norm_nonneg _))
  rw [one_mul]
  apply le_trans (opNorm_comp_le _ _)
  apply le_trans (mul_le_mul_of_nonneg_right
    AsymptoticCylinderReconstruction.lift_adjoint_norm_le (norm_nonneg _))
  rw [one_mul]
  apply le_trans (opNorm_comp_le _ _)
  apply le_trans (mul_le_mul_of_nonneg_left
    (AsymptoticCylinderReconstruction.terminalLift_norm_le A P') (norm_nonneg _))
  simpa only [mul_one, D, P', countReconstructionError] using hraw

def scaledFiniteCountReconstruction (hN : 0 < N) (P : Parameters A)
    (h d J : ℕ) (e : Sector N) :=
  (countReconstructionBound A P)⁻¹ • finiteCountReconstruction A hN P h d J e

theorem scaledFiniteCountReconstruction_error (hN : 0 < N) (P : Parameters A)
    (h d J : ℕ) (hJ : 0 < J) (e : Sector N) :
    ‖scaledFiniteCountReconstruction A hN P h d J e -
      scaledCountReconstruction A hN P h e‖ ≤ countReconstructionError A P d J := by
  have hb := countReconstructionBound_one_le A P
  have hbp : 0 < countReconstructionBound A P := zero_lt_one.trans_le hb
  exact scaled_difference_norm_le _ _ (inv_nonneg.2 hbp.le)
    (inv_le_one_of_one_le₀ hb) (finiteCountReconstruction_error A hN P h d J hJ e)

/-- Actual exact-to-finite normalized reconstruction, with explicit Newton
depth, Neumann depth and symmetric integer-fold cutoff.  No approximation
hypothesis is retained: only the displayed scalar size check is required. -/
theorem finite_normalizedCountReconstruction_error (hN : 0 < N) (P : Parameters A)
    (h n d J : ℕ) (hJ : 0 < J) (e : Sector N)
    (hsmall : countReconstructionError A P d J ≤ 1) :
    ‖polynomialNormalizedReconstruction (scaledFiniteCountReconstruction A hN P h d J e) n -
      normalizedCountReconstruction A hN P h e‖ ≤
      countReconstructionError A P d J *
        (polynomialMass (inverseSqrtPolynomial n) 4 +
          3 * polynomialSensitivity (inverseSqrtPolynomial n) 4) +
        (1 - countGramLower A P) ^ (2 ^ n) / Real.sqrt (countGramLower A P) := by
  have herr := scaledFiniteCountReconstruction_error A hN P h d J hJ e
  have hb := scaledCountReconstruction_bounds A hN P h e
  have hv : ‖scaledFiniteCountReconstruction A hN P h d J e‖ ≤ 2 := by
    have ht := norm_le_norm_sub_add (scaledFiniteCountReconstruction A hN P h d J e)
      (scaledCountReconstruction A hN P h e)
    linarith [hb.1]
  exact finite_polynomial_normalization_error _ _ (countGramLower_pos A P)
    (countGramLower_le_one A P) hb.2 hb.1 hv herr n

/-- Closed quantitative error: the dependence on the Newton depth is
explicit, with no coefficient sums and no qualitative approximation choice. -/
theorem finite_normalizedCountReconstruction_closed_error (hN : 0 < N) (P : Parameters A)
    (h n d J : ℕ) (hJ : 0 < J) (e : Sector N)
    (hsmall : countReconstructionError A P d J ≤ 1) :
    ‖polynomialNormalizedReconstruction (scaledFiniteCountReconstruction A hN P h d J e) n -
      normalizedCountReconstruction A hN P h e‖ ≤
      countReconstructionError A P d J * (1 + 3 * (3 ^ n : ℕ)) * (7 : ℝ) ^ (4 ^ n) +
        (1 - countGramLower A P) ^ (2 ^ n) / Real.sqrt (countGramLower A P) := by
  have hd0 : 0 ≤ countReconstructionError A P d J :=
    (norm_nonneg (finiteCountReconstruction A hN P h d J e -
      countReconstruction A hN P h e)).trans (finiteCountReconstruction_error A hN P h d J hJ e)
  apply (finite_normalizedCountReconstruction_error A hN P h n d J hJ e hsmall).trans
  apply add_le_add _ le_rfl
  have hm := polynomialMass_inverseSqrt_le (by norm_num : (0 : ℝ) ≤ 4) n
  have hs := polynomialSensitivity_inverseSqrt_le (by norm_num : (0 : ℝ) ≤ 4) n
  norm_num only [show (3 + 4 : ℝ) = 7 by norm_num] at hm hs
  have hh := mul_le_mul_of_nonneg_left
    (add_le_add hm (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 3))) hd0
  convert hh using 1
  ring

#print axioms finite_normalizedCountReconstruction_closed_error

#print axioms finiteCountReconstruction_error
#print axioms finite_normalizedCountReconstruction_error

end QuantitativeHolomorphic
