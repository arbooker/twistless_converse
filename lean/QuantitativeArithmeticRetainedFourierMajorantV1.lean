module

public import QuantitativeArithmeticRetainedFiniteNormalizationV1
public import QuantitativeHolomorphicSharpMajorantV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedFourierMajorant
open ContinuousLinearMap AsymptoticSectorSigns AsymptoticCylinder AsymptoticFourierNorm
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedSectorReconstruction
open QuantitativeArithmeticRetainedPreparedReconstruction
open QuantitativeArithmeticRetainedCylinderNormalization
open QuantitativeArithmeticRetainedFiniteNormalization
open QuantitativeHolomorphic

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)
    (hS : ∀p∈S,p.Prime) (hN : 0<N) (P : Parameters A)

/-- The actual mixed reconstruction before the capped-weight inclusion. -/
def weighted (e : Sector N) (m : ℕ) :=
  ((bound A P)⁻¹ • QuantitativeArithmeticRetainedCylinderExtension.extension A hS hN P
    (multiplier e) (ramifiedParameter e) (by omega : 2≤exponent A P+3) m).comp
    (inverseSqrtCFC ((scaled A hS hN P (multiplier e) (ramifiedParameter e)
      (by omega : 2≤exponent A P+3) m).adjoint.comp
      (scaled A hS hN P (multiplier e) (ramifiedParameter e) (by omega : 2≤exponent A P+3) m)))

theorem normalized_weighted (e : Sector N) (m : ℕ) :
    normalized A hS hN P (multiplier e) (ramifiedParameter e) (by omega : 2≤exponent A P+3) m=
      (inclusion P.epsilon_pos).comp (weighted A hS hN P e m) := by
  simp only [normalized,normalizedReconstruction,scaled,reconstruction,weighted,
    comp_smul,smul_comp,comp_assoc]

theorem weighted_norm (e : Sector N) (m : ℕ) :
    ‖weighted A hS hN P e m‖≤(Real.sqrt (gramLower A P))⁻¹ := by
  have hb := scaled_norm_le_one
    (QuantitativeArithmeticRetainedCylinderExtension.extension A hS hN P
      (multiplier e) (ramifiedParameter e) (by omega : 2≤exponent A P+3) m)
    (zero_lt_one.trans_le (bound_one_le A P))
    (QuantitativeArithmeticRetainedCylinderExtension.extension_norm_le A hS hN P
      (multiplier e) (ramifiedParameter e) (fun q _ => multiplier_norm e q)
      (fun p _ => ramifiedParameter_norm e p) (by omega) m (physical_contraction A P hS hN e m))
  have hv := scaled_bounds A hS hN P (multiplier e) (ramifiedParameter e)
    (fun q _ => multiplier_norm e q) (fun p _ => ramifiedParameter_norm e p)
    (by omega : 2≤exponent A P+3) m (physical_contraction A P hS hN e m)
  have hs := reconstruction_gram_spectrum _ hv.2 hv.1
  have hn := inverseSqrtCFC_norm_le _ (gramLower_pos A P) (fun x hx => (hs x hx).1)
  exact (opNorm_comp_le _ _).trans
    ((mul_le_mul hb hn (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

/-- The finite reconstruction uses the same capped weight. Its operator
norm grows only geometrically in the Newton depth, irrespective of coefficient mass. -/
def finiteWeighted (δ Y : ℝ) (e : Sector N) (m n : ℕ) :=
  ((bound A P)⁻¹ • (AsymptoticCylinderTerminal.projection Y).comp
    (cylinderFinite A P hS hN δ e m)).comp
    (Polynomial.aeval ((physicalScaled A P hS hN δ Y e m).adjoint.comp
      (physicalScaled A P hS hN δ Y e m)) (inverseSqrtPolynomial n))

theorem finite_weighted (δ Y : ℝ) (e : Sector N) (m n : ℕ) :
    polynomialNormalizedReconstruction (physicalScaled A P hS hN δ Y e m) n=
      (inclusion P.epsilon_pos).comp (finiteWeighted A hS hN P δ Y e m n) := by
  simp only [polynomialNormalizedReconstruction,finiteWeighted,physicalScaled,
    comp_smul,smul_comp,←comp_assoc,
    AsymptoticCylinderTerminal.projection_comp_inclusion]

theorem finiteWeighted_norm (δ Y : ℝ) (e : Sector N) (m n : ℕ) :
    ‖finiteWeighted A hS hN P δ Y e m n‖≤(3/2:ℝ)^n := by
  have hb := scaled_norm_le_one
    ((AsymptoticCylinderTerminal.projection Y).comp (cylinderFinite A P hS hN δ e m))
    (zero_lt_one.trans_le (bound_one_le A P))
    ((contract_left _ _ (AsymptoticCylinderTerminal.projection_norm_le Y)).trans
      (cylinderFinite_norm A P hS hN δ e m))
  have hn := Sharp.inverseSqrtPolynomial_gram_norm_le _ (physicalScaled_norm A P hS hN δ Y e m) n
  exact (opNorm_comp_le _ _).trans
    ((mul_le_mul hb hn (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

theorem normalized_fourier_gram (h : ℕ) (e : Sector N) (l : ℕ) :
    ‖(normalized A hS hN P (multiplier e) (ramifiedParameter e)
        (by omega : 2≤exponent A P+3) (h+1)).adjoint
      ((fourierBasis (2*h) (exponent A P+4) (by positivity : 0<4*Real.pi) P.epsilon_pos l :
        holomorphicSpace (2*h) (exponent A P+4) (by positivity : 0<4*Real.pi) P.epsilon_pos) : Space)‖^2≤
      ((Real.sqrt (gramLower A P))⁻¹)^2 *
        modeRatio (2*h) (exponent A P+4) (4*Real.pi) P.ε (l+1) := by
  rw [normalized_weighted]
  apply (AsymptoticCylinder.reconstructed_fourier_gram _ _ _ _ _ l).trans
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (weighted_norm A hS hN P e (h+1)) 2)
    (modeRatio_nonneg _ _ _ _ P.epsilon_pos)

theorem finite_fourier_gram (δ Y : ℝ) (h : ℕ) (e : Sector N) (n l : ℕ) :
    ‖(polynomialNormalizedReconstruction (physicalScaled A P hS hN δ Y e (h+1)) n).adjoint
      ((fourierBasis (2*h) (exponent A P+4) (by positivity : 0<4*Real.pi) P.epsilon_pos l :
        holomorphicSpace (2*h) (exponent A P+4) (by positivity : 0<4*Real.pi) P.epsilon_pos) : Space)‖^2≤
      ((3/2:ℝ)^n)^2 * modeRatio (2*h) (exponent A P+4) (4*Real.pi) P.ε (l+1) := by
  rw [finite_weighted]
  apply (AsymptoticCylinder.reconstructed_fourier_gram _ _ _ _ _ l).trans
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (finiteWeighted_norm A hS hN P δ Y e (h+1) n) 2)
    (modeRatio_nonneg _ _ _ _ P.epsilon_pos)

#print axioms normalized_weighted
#print axioms weighted_norm
#print axioms finite_weighted
#print axioms finiteWeighted_norm
#print axioms normalized_fourier_gram
#print axioms finite_fourier_gram
end QuantitativeArithmeticRetainedFourierMajorant
