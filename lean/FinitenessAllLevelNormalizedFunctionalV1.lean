module

public import FinitenessAllLevelCoefficientFunctionalV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelCoefficientFunctional

open FinitenessOriginalInput FinitenessOriginalFourier FinitenessAllLevelDiskAlgebra
  FinitenessCompletedNormalization Metric

variable {R : ℝ}

/-- Undo the Fourier weight normalization in the continuous coefficient
functional. At index zero all disk-algebra inputs have zero coefficient. -/
def normalizedCLM (hR : 0 < R) (k n : ℕ) : space R →L[ℂ] ℂ :=
  (((n : ℝ) ^ alpha k : ℝ) : ℂ)⁻¹ • coefficientCLM hR n

theorem coefficient_representative {N k : ℕ} (hR : 0 < R) (hR1 : R < 1)
    (f : S N k) (n : ℕ) :
    coefficientCLM hR n (representative N k hR hR1 f) = fullCoefficients f.val k n := by
  apply coefficient_eq_of_series hR _ (FinitenessOriginalDiskIndependence.polynomial N k f)
  intro z hz
  rw [extend, dite_eq_left (Metric.ball_subset_closedBall hz)]
  exact FinitenessAllLevelTopology.polynomial_diskSeries_apply
    (FinitenessOriginalDiskIndependence.polynomial N k f) hR.le hR1 ⟨z, ball_subset_closedBall hz⟩

/-- The functionals recover the literal Dirichlet coefficients, including
the zero index, rather than only the Fourier-normalized coefficients. -/
theorem normalized_representative {N k : ℕ} (hR : 0 < R) (hR1 : R < 1)
    (f : S N k) (n : ℕ) :
    normalizedCLM hR k n (representative N k hR hR1 f) = f.val n := by
  simp only [normalizedCLM, smul_apply, coefficient_representative,
    smul_eq_mul]
  by_cases hn : n = 0
  · subst n
    rw [fullCoefficients_zero f.property.zero, mul_zero, f.property.zero]
  · have hpow : (((n : ℝ) ^ alpha k : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) (alpha k)).ne'
    simp only [fullCoefficients, FinitenessGrowthNormalization.normalized]
    field_simp

#print axioms coefficient_representative
#print axioms normalized_representative

end FinitenessAllLevelCoefficientFunctional
