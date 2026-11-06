module

public import FinitenessAllLevelProjectionDichotomyV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelConstraintLocus

open Complex Set FinitenessAllLevelGlobalHeight FinitenessAllLevelPolynomialPresentation
  FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  QuantitativeArithmeticRetainedCertificate

variable {N Q p : ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (hp : p.Prime) (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2)
    (hpQ : p ∣ Q) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a b : ℝ} (hb : 0 < b) (hba : b < a) (hae : a ≤ P.ε)
    {m : ℕ} (hm : 0 < m) (s : Fin (Q + 1) → Bool)

include hp hgood hlarge hpQ hae hm

/-- The actual sector projection is either all of the eigenvalue plane or
discrete. This is proved from explicit polynomial charts and properness. -/
theorem sector_projection_dichotomy :
    {z : ℂ | ∃ F, (z, F) ∈ sectorLocus hN A P hb hba m s} = univ ∨
      IsDiscrete {z : ℂ | ∃ F, (z, F) ∈ sectorLocus hN A P hb hba m s} := by
  have hrange : range (fun t : sectorLocus hN A P hb hba m s => t.val.1) =
      {z : ℂ | ∃ F, (z, F) ∈ sectorLocus hN A P hb hba m s} := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t.val.2, t.property⟩
    · rintro ⟨F, hF⟩
      exact ⟨⟨(z, F), hF⟩, rfl⟩
  apply closed_projection_dichotomy
  · rw [← hrange]
    exact (global_sector_projection_isProperMap hN hp hgood hlarge hpQ A P hb hba hae hm s).isClosed_range
  · intro w
    obtain ⟨d, es, c, hw⟩ := sector_polynomial_presentation hN hp A P hb hba hae m s w
    obtain ⟨c', hw', hc'⟩ := c.connected_restriction hw
    exact c'.punctured_interior_projection hc'
      (fun z => global_sector_fiber_finite hN hp hgood hlarge hpQ A P hb hba hae hm s z) hw'

/-- If the actual projection is discrete, compactness and finite fibers
supply the desired bounded-eigenvalue finiteness, with no uniform growth
constant introduced. -/
theorem sector_bounded_finite_of_discrete_projection
    (hd : IsDiscrete {z : ℂ | ∃ F, (z, F) ∈ sectorLocus hN A P hb hba m s}) (B : ℝ) :
    {t : ℂ × space (radius a) | t ∈ sectorLocus hN A P hb hba m s ∧ ‖t.1‖ ≤ B}.Finite := by
  let K := {t : ℂ × space (radius a) | t ∈ sectorLocus hN A P hb hba m s ∧ ‖t.1‖ ≤ B}
  have hK : IsCompact K :=
    global_sector_bounded_isCompact hN hp hgood hlarge hpQ A P hb hba hae hm s B
  have himage : (Prod.fst '' K).Finite := (hK.image continuous_fst).finite (hd.mono (by
    rintro z ⟨t, ht, rfl⟩
    exact ⟨t.2, ht.1⟩))
  apply Set.Finite.of_finite_fibers Prod.fst himage
  intro z _
  apply (global_sector_fiber_finite hN hp hgood hlarge hpQ A P hb hba hae hm s z).subset
  intro t ht
  exact ⟨ht.1.1, ht.2⟩

/-- The remaining global obstruction is now explicit: either a sector
has a solution at EVERY complex eigenvalue, or all of its bounded parts
are finite. Surjectivity has not been excluded by this theorem. -/
theorem sector_surjective_or_bounded_finite :
    (∀ z : ℂ, ∃ F, (z, F) ∈ sectorLocus hN A P hb hba m s) ∨
      ∀ B : ℝ, {t : ℂ × space (radius a) |
        t ∈ sectorLocus hN A P hb hba m s ∧ ‖t.1‖ ≤ B}.Finite := by
  rcases sector_projection_dichotomy hN hp hgood hlarge hpQ A P hb hba hae hm s with hall | hd
  · left
    intro z
    change z ∈ {z : ℂ | ∃ F, (z, F) ∈ sectorLocus hN A P hb hba m s}
    rw [hall]
    exact mem_univ z
  · exact Or.inr (sector_bounded_finite_of_discrete_projection
      hN hp hgood hlarge hpQ A P hb hba hae hm s hd)

#print axioms sector_projection_dichotomy
#print axioms sector_bounded_finite_of_discrete_projection
#print axioms sector_surjective_or_bounded_finite

end FinitenessAllLevelConstraintLocus
