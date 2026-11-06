module

public import QuantitativeHolomorphicGramV1
public import AsymptoticPolynomialPerturbationV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open ContinuousLinearMap

def polynomialMass (p : Polynomial ℝ) (D : ℝ) : ℝ :=
  ∑ j ∈ p.support, |p.coeff j| * D ^ j

def polynomialSensitivity (p : Polynomial ℝ) (D : ℝ) : ℝ :=
  ∑ j ∈ p.support, |p.coeff j| * (j : ℝ) * D ^ j

variable {G H : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem polynomial_aeval_sum (p : Polynomial ℝ) (A : G →L[ℂ] G) :
    Polynomial.aeval A p = ∑ j ∈ p.support, (p.coeff j : ℝ) • A ^ j := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro j _
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem polynomial_aeval_norm_le (p : Polynomial ℝ) (A : G →L[ℂ] G)
    {D : ℝ} (hA : ‖A‖ ≤ D) : ‖Polynomial.aeval A p‖ ≤ polynomialMass p D := by
  rw [polynomial_aeval_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (AsymptoticReconstruction.power_norm_le A hA j) (abs_nonneg _)

theorem polynomial_aeval_difference_norm_le (p : Polynomial ℝ) (A B : G →L[ℂ] G)
    {D : ℝ} (hD : 1 ≤ D) (hA : ‖A‖ ≤ D) (hB : ‖B‖ ≤ D) :
    ‖Polynomial.aeval A p - Polynomial.aeval B p‖ ≤
      polynomialSensitivity p D * ‖A - B‖ := by
  rw [polynomial_aeval_sum, polynomial_aeval_sum, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  unfold polynomialSensitivity
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  rw [← smul_sub, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left
    (AsymptoticReconstruction.power_difference_norm_le_of_bound A B hD hA hB j)
    (abs_nonneg _)).trans_eq (by ring)

variable [CompleteSpace G] [CompleteSpace H]

/-- The Gram perturbation bound follows from the original maps. -/
theorem gram_difference_norm_le (R V : G →L[ℂ] H) :
    ‖V.adjoint.comp V - R.adjoint.comp R‖ ≤ (‖V‖ + ‖R‖) * ‖V - R‖ := by
  have he : V.adjoint.comp V - R.adjoint.comp R =
      V.adjoint.comp (V - R) + (V - R).adjoint.comp R := by
    rw [map_sub, comp_sub, sub_comp]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  apply (add_le_add (opNorm_comp_le _ _) (opNorm_comp_le _ _)).trans_eq
  rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
  ring

/-- A finite approximation may replace the reconstruction *before* the
Newton polynomial.  Its Gram need not be invertible: all errors are explicit. -/
theorem finite_polynomial_normalization_error (R V : G →L[ℂ] H) {κ δ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hR : ∀ v, κ * ‖v‖ ^ 2 ≤ ‖R v‖ ^ 2)
    (hRn : ‖R‖ ≤ 1) (hVn : ‖V‖ ≤ 2) (hδ : ‖V - R‖ ≤ δ) (n : ℕ) :
    ‖polynomialNormalizedReconstruction V n - normalizedReconstruction R‖ ≤
      δ * (polynomialMass (inverseSqrtPolynomial n) 4 +
        3 * polynomialSensitivity (inverseSqrtPolynomial n) 4) +
        (1 - κ) ^ (2 ^ n) / Real.sqrt κ := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hRG : ‖R.adjoint.comp R‖ ≤ (4 : ℝ) := by
    rw [norm_adjoint_comp_self]
    nlinarith [norm_nonneg R]
  have hVG : ‖V.adjoint.comp V‖ ≤ (4 : ℝ) := by
    rw [norm_adjoint_comp_self]
    nlinarith [norm_nonneg V]
  have hg : ‖V.adjoint.comp V - R.adjoint.comp R‖ ≤ 3 * δ :=
    (gram_difference_norm_le R V).trans
      (mul_le_mul (by linarith : ‖V‖ + ‖R‖ ≤ 3) hδ (norm_nonneg _) (by norm_num))
  have hmass : 0 ≤ polynomialMass (inverseSqrtPolynomial n) 4 := by
    unfold polynomialMass; positivity
  have hsens : 0 ≤ polynomialSensitivity (inverseSqrtPolynomial n) 4 := by
    unfold polynomialSensitivity; positivity
  have hp := polynomial_aeval_difference_norm_le (inverseSqrtPolynomial n)
    (V.adjoint.comp V) (R.adjoint.comp R) (by norm_num : (1 : ℝ) ≤ 4) hVG hRG
  have he : polynomialNormalizedReconstruction V n - polynomialNormalizedReconstruction R n =
      (V - R).comp (Polynomial.aeval (V.adjoint.comp V) (inverseSqrtPolynomial n)) +
      R.comp (Polynomial.aeval (V.adjoint.comp V) (inverseSqrtPolynomial n) -
        Polynomial.aeval (R.adjoint.comp R) (inverseSqrtPolynomial n)) := by
    rw [sub_comp, comp_sub]
    unfold polynomialNormalizedReconstruction
    abel
  have hd : ‖polynomialNormalizedReconstruction V n - polynomialNormalizedReconstruction R n‖ ≤
      δ * (polynomialMass (inverseSqrtPolynomial n) 4 +
        3 * polynomialSensitivity (inverseSqrtPolynomial n) 4) := by
    rw [he]
    apply (norm_add_le _ _).trans
    apply (add_le_add (opNorm_comp_le _ _) (opNorm_comp_le _ _)).trans
    calc
      _ ≤ δ * polynomialMass (inverseSqrtPolynomial n) 4 +
          1 * (polynomialSensitivity (inverseSqrtPolynomial n) 4 * (3 * δ)) :=
        add_le_add
          (mul_le_mul hδ (polynomial_aeval_norm_le _ _ hVG) (norm_nonneg _) hδ0)
          (mul_le_mul hRn (hp.trans (mul_le_mul_of_nonneg_left hg hsens))
            (norm_nonneg _) zero_le_one)
      _ = _ := by ring
  exact (norm_sub_le_norm_sub_add_norm_sub _ (polynomialNormalizedReconstruction R n) _).trans
    (add_le_add hd (polynomialNormalizedReconstruction_error R hκ hκ1 hR hRn n))

#print axioms polynomial_aeval_difference_norm_le
#print axioms gram_difference_norm_le
#print axioms finite_polynomial_normalization_error

end QuantitativeHolomorphic
