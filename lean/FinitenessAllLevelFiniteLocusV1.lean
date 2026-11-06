module

public import FinitenessAllLevelCoherentSectorsV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelConstraintLocus

open Complex Set FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelGlobalHeight FinitenessAllLevelFormalContinuation
  FinitenessAllLevelCertificatePencil FinitenessAllLevelOriginalPencil
  FinitenessOriginalInput QuantitativeArithmeticRetainedCertificate

variable {N Q p : ℕ} {hQ : 0 < Q}

theorem sector_signs (Q m : ℕ) (s : Fin (Q + 1) → Bool) (q : ℕ) :
    sector Q m s q = I ^ (2 * m) ∨ sector Q m s q = -I ^ (2 * m) := by
  unfold sector
  split
  · split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · exact Or.inl rfl

theorem sector_norm (Q m : ℕ) (s : Fin (Q + 1) → Bool) (q : ℕ) :
    ‖sector Q m s q‖ = 1 := by
  rcases sector_signs Q m s q with h | h <;> simp [h]

/-- Heights can simultaneously meet the exact-chart and boundary-reconstruction
requirements, independently of the weight and the chosen sector. -/
theorem chart_heights_exist (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L) :
    ∃ a b : ℝ, 0 < b ∧ b < a ∧ a ≤ P.ε ∧ a ≤ b / P.ρ := by
  let a := P.ε / 2
  have ha : 0 < a := half_pos P.epsilon_pos
  have hρ := P.rho_pos
  have hε := P.epsilon_pos
  refine ⟨a, a * ((1 + P.ρ) / 2), by positivity, ?_, by dsimp [a]; linarith, ?_⟩
  · nlinarith [P.rho_lt_one, mul_pos ha (sub_pos.mpr P.rho_lt_one)]
  · apply (le_div_iff₀ P.rho_pos).mpr
    nlinarith [mul_pos ha (sub_pos.mpr P.rho_lt_one)]

/-- The actual constrained compact-pencil locus for a fixed finite sign label. -/
def sectorLocus (hN : 0 < N) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a b : ℝ} (hb : 0 < b) (hab : b < a)
    (m : ℕ) (s : Fin (Q + 1) → Bool) : Set (ℂ × space (radius a)) :=
  {t | pencil hN A hb hab (sector Q m s) m t.1 t.2 = t.2 ∧
    Constraints A P a (sector Q m s) m t.1 t.2}

/-- On every bounded eigenvalue disk, the union of the finitely many exact
sector loci is precisely the image of literal original solutions. This is a
set equality, not an assumption of analytic-space geometry. -/
theorem finite_locus_iff_original (hN : 0 < N) (hp : p.Prime) (hgood : ¬ p ∣ N)
    (hpQ : p ∣ Q) (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    {a b : ℝ} (hb : 0 < b) (hab : b < a) (hae : a ≤ P.ε) (hheight : a ≤ b / P.ρ)
    {m : ℕ} (hm : 0 < m) (t : ℂ × space (radius a)) (ht : ‖t.1‖ ≤ L) :
    (∃ s : Fin (Q + 1) → Bool, t ∈ sectorLocus hN A P hb hab m s) ↔
      ∃ f : S N (2 * m), f.val p = t.1 ∧
        representative N (2 * m) (radius_pos a) (radius_lt_one (hb.trans hab)) f = t.2 := by
  constructor
  · rintro ⟨s, _, hc⟩
    exact constraints_recover hN hp hpQ hm A P (hb.trans hab) hae (sector Q m s) t.1 t.2
      (fun q _ => sector_norm Q m s q) ht (sector_signs Q m s 1) hc
  · rintro ⟨f, hf, hF⟩
    obtain ⟨s, hs⟩ := original_finite_constrained_pencil hN hp hgood hpQ A P hb hab hae hheight m f
    refine ⟨s, ?_⟩
    change pencil hN A hb hab (sector Q m s) m t.1 t.2 = t.2 ∧
      Constraints A P a (sector Q m s) m t.1 t.2
    simpa only [hf, hF] using hs

#print axioms sector_signs
#print axioms sector_norm
#print axioms chart_heights_exist
#print axioms finite_locus_iff_original

end FinitenessAllLevelConstraintLocus
