module

public import QuantitativeHolomorphicObservationExpressionV1
public import AsymptoticCylinderTraceV1
public import AsymptoticGramTracePerturbationV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticFourierNorm AsymptoticObservation

/-- A lower spectral bound gives the actual bounded CFC normalizer. -/
theorem inverseSqrtCFC_norm_le {𝔄 : Type*} [CStarAlgebra 𝔄] (T : 𝔄)
    {κ : ℝ} (hκ : 0 < κ) (hlo : ∀ x ∈ spectrum ℝ T, κ ≤ x) :
    ‖inverseSqrtCFC T‖ ≤ (Real.sqrt κ)⁻¹ := by
  apply norm_cfc_le (inv_nonneg.2 (Real.sqrt_nonneg κ))
  intro x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg x))]
  exact inv_anti₀ (Real.sqrt_pos.2 hκ) (Real.sqrt_le_sqrt (hlo x hx))

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)

/-- Exact normalized reconstruction before the capped-weight inclusion. -/
def countWeightedNormalizer (hN : 0 < N) (P : Parameters A) (h : ℕ) (e : Sector N) :=
  ((countReconstructionBound A P)⁻¹ • AsymptoticReconstructedCount.reconstruction A hN P h e).comp
    (inverseSqrtCFC ((scaledCountReconstruction A hN P h e).adjoint.comp
      (scaledCountReconstruction A hN P h e)))

theorem normalizedCountReconstruction_weighted (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) :
    normalizedCountReconstruction A hN P h e =
      (inclusion (AsymptoticReconstructedCount.parameters A P).epsilon_pos).comp
        (countWeightedNormalizer A hN P h e) := by
  simp only [normalizedCountReconstruction, normalizedReconstruction, scaledCountReconstruction,
    countReconstruction, countWeightedNormalizer, comp_smul, smul_comp, comp_assoc]

theorem countWeightedNormalizer_norm_le (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) :
    ‖countWeightedNormalizer A hN P h e‖ ≤ (Real.sqrt (countGramLower A P))⁻¹ := by
  have hbase := scaled_norm_le_one (AsymptoticReconstructedCount.reconstruction A hN P h e)
    (zero_lt_one.trans_le (countReconstructionBound_one_le A P))
    (AsymptoticReconstructedCount.reconstruction_norm_le A hN P h e)
  have hspec := reconstruction_gram_spectrum (scaledCountReconstruction A hN P h e)
    (scaledCountReconstruction_bounds A hN P h e).2
    (scaledCountReconstruction_bounds A hN P h e).1
  have hn := inverseSqrtCFC_norm_le _ (countGramLower_pos A P) (fun x hx => (hspec x hx).1)
  exact (opNorm_comp_le _ _).trans ((mul_le_mul hbase hn (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

/-- Polynomial finite reconstruction before the same capped weight. -/
def finiteCountWeightedNormalizer (hN : 0 < N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (Y : ℝ) (j J n : ℕ) :=
  ((countReconstructionBound A P)⁻¹ • AsymptoticReconstructedCount.finiteCutBaseReconstruction
    A hN P h e Y j (Finset.Icc (-(J : ℤ)) J)).comp
    (Polynomial.aeval ((scaledCutFiniteCountReconstruction A hN P h e Y j J).adjoint.comp
      (scaledCutFiniteCountReconstruction A hN P h e Y j J)) (inverseSqrtPolynomial n))

theorem finiteCountReconstruction_weighted (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (Y : ℝ) (j J n : ℕ) :
    polynomialNormalizedReconstruction (scaledCutFiniteCountReconstruction A hN P h e Y j J) n =
      (inclusion (AsymptoticReconstructedCount.parameters A P).epsilon_pos).comp
        (finiteCountWeightedNormalizer A hN P h e Y j J n) := by
  simp only [polynomialNormalizedReconstruction, finiteCountWeightedNormalizer,
    scaledCutFiniteCountReconstruction, AsymptoticReconstructedCount.finiteCutReconstruction,
    comp_smul, smul_comp, comp_assoc]
  rfl

theorem finiteCountWeightedNormalizer_norm_le (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (Y : ℝ) (j J n : ℕ) :
    ‖finiteCountWeightedNormalizer A hN P h e Y j J n‖ ≤ (4 : ℝ) ^ (4 ^ n) := by
  have hbase := scaled_norm_le_one (AsymptoticReconstructedCount.finiteCutBaseReconstruction
    A hN P h e Y j (Finset.Icc (-(J : ℤ)) J))
    (zero_lt_one.trans_le (countReconstructionBound_one_le A P))
    (AsymptoticReconstructedCount.finiteCutBaseReconstruction_norm_le A hN P h e Y j _)
  have hv := scaledCutFiniteCountReconstruction_norm_le A hN P h e Y j J
  have hg : ‖(scaledCutFiniteCountReconstruction A hN P h e Y j J).adjoint.comp
      (scaledCutFiniteCountReconstruction A hN P h e Y j J)‖ ≤ 1 := by
    rw [norm_adjoint_comp_self]
    simpa only [one_mul] using mul_le_mul hv hv (norm_nonneg (scaledCutFiniteCountReconstruction A hN P h e Y j J)) zero_le_one
  have hq := (polynomial_aeval_norm_le (inverseSqrtPolynomial n) _ hg).trans
    (polynomialMass_inverseSqrt_le (D := 1) zero_le_one n)
  have hq' : ‖Polynomial.aeval ((scaledCutFiniteCountReconstruction A hN P h e Y j J).adjoint.comp
      (scaledCutFiniteCountReconstruction A hN P h e Y j J)) (inverseSqrtPolynomial n)‖ ≤ (4 : ℝ) ^ (4 ^ n) := by
    norm_num only [show (3 + 1 : ℝ) = 4 by norm_num] at hq
    exact hq
  exact (opNorm_comp_le _ _).trans ((mul_le_mul hbase hq' (norm_nonneg (Polynomial.aeval ((scaledCutFiniteCountReconstruction A hN P h e Y j J).adjoint.comp
    (scaledCutFiniteCountReconstruction A hN P h e Y j J)) (inverseSqrtPolynomial n))) zero_le_one).trans_eq (one_mul _))

/-- Concrete, weight-uniform Fourier Gram majorant for exact normalization. -/
theorem normalizedCountReconstruction_fourier_gram (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (l : ℕ) :
    ‖(normalizedCountReconstruction A hN P h e).adjoint
      ((fourierBasis (2*h) ((AsymptoticReconstructedCount.parameters A P).s+4)
        (by positivity : 0 < 4*Real.pi) (AsymptoticReconstructedCount.parameters A P).epsilon_pos l :
        holomorphicSpace (2*h) ((AsymptoticReconstructedCount.parameters A P).s+4)
          (by positivity : 0 < 4*Real.pi) (AsymptoticReconstructedCount.parameters A P).epsilon_pos) : Space)‖ ^ 2 ≤
      ((Real.sqrt (countGramLower A P))⁻¹) ^ 2 *
        modeRatio (2*h) ((AsymptoticReconstructedCount.parameters A P).s+4) (4*Real.pi)
          (AsymptoticReconstructedCount.parameters A P).ε (l+1) := by
  rw [normalizedCountReconstruction_weighted]
  apply (reconstructed_fourier_gram _ _ _ _ _ l).trans
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (countWeightedNormalizer_norm_le A hN P h e) 2)
    (modeRatio_nonneg _ _ _ _ (AsymptoticReconstructedCount.parameters A P).epsilon_pos)

/-- The finite approximation has an explicit Fourier majorant even if its
Gram is singular; the constant depends only on the Newton depth. -/
theorem finiteCountReconstruction_fourier_gram (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (Y : ℝ) (j J n l : ℕ) :
    ‖(polynomialNormalizedReconstruction (scaledCutFiniteCountReconstruction A hN P h e Y j J) n).adjoint
      ((fourierBasis (2*h) ((AsymptoticReconstructedCount.parameters A P).s+4)
        (by positivity : 0 < 4*Real.pi) (AsymptoticReconstructedCount.parameters A P).epsilon_pos l :
        holomorphicSpace (2*h) ((AsymptoticReconstructedCount.parameters A P).s+4)
          (by positivity : 0 < 4*Real.pi) (AsymptoticReconstructedCount.parameters A P).epsilon_pos) : Space)‖ ^ 2 ≤
      ((4 : ℝ) ^ (4 ^ n)) ^ 2 *
        modeRatio (2*h) ((AsymptoticReconstructedCount.parameters A P).s+4) (4*Real.pi)
          (AsymptoticReconstructedCount.parameters A P).ε (l+1) := by
  rw [finiteCountReconstruction_weighted]
  apply (reconstructed_fourier_gram _ _ _ _ _ l).trans
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (finiteCountWeightedNormalizer_norm_le A hN P h e Y j J n) 2)
    (modeRatio_nonneg _ _ _ _ (AsymptoticReconstructedCount.parameters A P).epsilon_pos)

#print axioms finiteCountReconstruction_fourier_gram

#print axioms inverseSqrtCFC_norm_le
#print axioms countWeightedNormalizer_norm_le
#print axioms finiteCountWeightedNormalizer_norm_le
#print axioms normalizedCountReconstruction_fourier_gram

end QuantitativeHolomorphic
