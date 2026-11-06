module

public import FinitenessAllLevelDeterminantRigidityV1
public import FinitenessAllLevelSectorDichotomyV1
public import FinitenessAllLevelAtlasCoefficientsV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelConstraintLocus

open Complex Set FinitenessAllLevelGlobalHeight FinitenessAllLevelPolynomialPresentation
  FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelCoefficientFunctional QuantitativeArithmeticRetainedCertificate

variable {N Q p r : ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (hp : p.Prime) (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2)
    (hr : r.Prime) (hrgood : ¬ r ∣ N) (hrlarge : N < r ^ 2) (hne : p ≠ r)
    (hpQ : p ∣ Q) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a b : ℝ} (hb : 0 < b) (hba : b < a) (hae : a ≤ P.ε)
    {m : ℕ} (hm : 0 < m) (s : Fin (Q + 1) → Bool)

include hp hgood hlarge hr hrgood hrlarge hne hpQ hae hm

/-- The actual sector cannot cover the whole eigenvalue plane: its second
prime coefficient contradicts the determinant-polynomial degree bounds. -/
theorem sector_not_surjective :
    ¬ ∀ z : ℂ, ∃ F, (z, F) ∈ sectorLocus hN A P hb hba m s := by
  have hfinite (z : ℂ) : {F | (z, F) ∈ sectorLocus hN A P hb hba m s}.Finite := by
    apply ((global_sector_fiber_finite hN hp hgood hlarge hpQ A P hb hba hae hm s z).image Prod.snd).subset
    intro F hF
    exact ⟨(z, F), ⟨hF, rfl⟩, rfl⟩
  apply no_surjective_two_prime_family (fun z F => (z, F) ∈ sectorLocus hN A P hb hba m s)
    (global_sector_projection_isProperMap hN hp hgood hlarge hpQ A P hb hba hae hm s)
    hfinite
    (sector_regular_values_codiscrete hN hp hgood hlarge hpQ A P hb hba hae hm s)
    (normalizedCLM (radius_pos a) (2 * m) r) hp hr hne
  intro j
  obtain ⟨C, D, hC, hD, he⟩ := global_sector_two_prime_bounds
    hN hp hgood hlarge hr hrgood hrlarge hpQ A P hb hba hae hm j
  exact ⟨C, D, hC, hD, fun z F hF => he s ⟨(z, F), hF⟩⟩

/-- Every bounded-eigenvalue part of every actual sector is finite. All
analytic geometry and both prime estimates have been discharged. -/
theorem sector_bounded_finite (B : ℝ) :
    {t : ℂ × space (radius a) | t ∈ sectorLocus hN A P hb hba m s ∧ ‖t.1‖ ≤ B}.Finite := by
  rcases sector_surjective_or_bounded_finite hN hp hgood hlarge hpQ A P hb hba hae hm s with hs | hf
  · exact False.elim ((sector_not_surjective hN hp hgood hlarge hr hrgood hrlarge hne
      hpQ A P hb hba hae hm s) hs)
  · exact hf B

#print axioms sector_not_surjective
#print axioms sector_bounded_finite

end FinitenessAllLevelConstraintLocus
