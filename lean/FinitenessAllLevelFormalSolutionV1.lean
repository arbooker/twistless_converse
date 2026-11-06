module

public import FinitenessAllLevelFormalCoefficientsV1
public import FinitenessAllLevelContinuationV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelCoefficientFunctional

open FinitenessAllLevelDiskAlgebra FinitenessOriginalFourier
  FinitenessCompletedNormalization

theorem coefficient_zero {R : ℝ} (hR : 0 < R) (F : space R) :
    coefficientCLM hR 0 F = 0 := by
  rw [coefficientCLM_apply, coefficient_eq_cauchy,
    (has_series hR F).coeff_zero (fun _ => 1), F.property.2]

/-- Restoring the Fourier normalization recovers every disk coefficient,
including the zero coefficient. -/
theorem full_normalized {R : ℝ} (hR : 0 < R) (k : ℕ) (F : space R) :
    fullCoefficients (fun n => normalizedCLM hR k n F) k =
      (fun n => coefficientCLM hR n F) := by
  funext n
  by_cases hn : n = 0
  · subst n
    simp [fullCoefficients, FinitenessGrowthNormalization.normalized,
      normalizedCLM, coefficient_zero hR F]
  · have hpow : (((n : ℝ) ^ alpha k : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos
        (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) (alpha k)).ne'
    simp only [fullCoefficients, FinitenessGrowthNormalization.normalized,
      normalizedCLM, smul_apply, smul_eq_mul]
    field_simp

end FinitenessAllLevelCoefficientFunctional

namespace FinitenessAllLevelFormalContinuation

open Complex FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelGlobalHeight FinitenessAllLevelCoefficientFunctional
  FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
  QuantitativeArithmeticRetainedCertificate

/-- Cauchy identities, an actual height bound, the original Fricke equation
and the coefficient equations recover the literal original solution predicate.
Neither continuation nor coefficient growth is assumed in this statement. -/
theorem solution_of_height_fricke {N Q p m : ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (hp : p.Prime) (hm : 0 < m) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (lam : ℂ) (F : space (radius a))
    (he : FinitenessAllLevelCauchyConstraints.CauchyIdentities (formal A P a χ m lam F))
    {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ z : ℂ, 0 < z.im → z.im ^ d * ‖formal A P a χ m lam F z‖ ≤ M)
    (ε : ℂ) (hε : ε = 1 ∨ ε = -1)
    (hfr : ∀ z : ℂ, 0 < z.im → formal A P a χ m lam F z =
      (ε * I ^ (2 * m)) / (((Real.sqrt N : ℝ) : ℂ) * z) ^ (2 * m) *
        formal A P a χ m lam F (-1 / ((N : ℂ) * z)))
    (heuler : ∀ e : FinitenessAllLevelEulerEquations.Equation N,
      FinitenessAllLevelEulerEquations.equation N (2 * m) p (radius_pos a) e (lam, F) = 0) :
    IsSolution N (2 * m) (fun n => normalizedCLM (radius_pos a) (2 * m) n F) ∧
      normalizedCLM (radius_pos a) (2 * m) p F = lam := by
  obtain ⟨_, hc, hfourier⟩ := coefficients_of_height hN hp A P ha hae χ m lam F he hM hb
  have hk : 0 < 2 * m := by omega
  have hg := normalized_growth_of_polynomial (radius_pos a) hk F hc
  obtain ⟨hf, hlam⟩ := (FinitenessAllLevelEulerEquations.equations_iff_eulerData
    N (2 * m) p (radius_pos a) lam F hg).mp heuler
  refine ⟨{ toEulerData := hf, continuation := ?_ }, hlam⟩
  obtain ⟨τ, _, hgτ⟩ := hg
  apply FinitenessAllLevelContinuation.continuation_of_fricke hN hk hf.zero hgτ ε hε
  intro z hz
  rw [full_normalized, hfourier z hz, hfourier _ ?_]
  · exact hfr z hz
  · simpa only [ofReal_natCast] using FinitenessComplexGeometry.reflected_im_pos
      (L := (N : ℝ)) (by exact_mod_cast hN) hz

#print axioms FinitenessAllLevelCoefficientFunctional.coefficient_zero
#print axioms FinitenessAllLevelCoefficientFunctional.full_normalized
#print axioms solution_of_height_fricke

end FinitenessAllLevelFormalContinuation
