module

public import FinitenessAllLevelParameterChangeV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelConstraintLocus

open Complex FinitenessAllLevelGlobalHeight FinitenessAllLevelDiskAlgebra
  FinitenessAllLevelBoundaryCoordinates FinitenessAllLevelFormalContinuation
  FinitenessAllLevelCertificatePencil FinitenessAllLevelOriginalPencil
  FinitenessOriginalInput QuantitativeArithmeticRetainedCertificate

variable {N Q p : ℕ} {hQ : 0 < Q}

/-- Exact constraints recover an original solution for EVERY eigenvalue in one
fixed disk model. The auxiliary growth budget is changed without changing the
actual continuation, the constraints, or either geometric height. -/
theorem constraints_recover_global (hN : 0 < N) (hp : p.Prime) (hpQ : p ∣ Q)
    {m : ℕ} (hm : 0 < m) (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε) (χ : ℕ → ℂ) (lam : ℂ)
    (F : space (radius a)) (hχ : ∀ q, q ∣ Q → ‖χ q‖ = 1)
    (hs : χ 1 = I ^ (2 * m) ∨ χ 1 = -(I ^ (2 * m)))
    (hc : Constraints A P a χ m lam F) :
    ∃ f : S N (2 * m), f.val p = lam ∧
      representative N (2 * m) (radius_pos a) (radius_lt_one ha) f = F := by
  obtain ⟨P', hε, hρ⟩ := parameters_change_bound A P (norm_nonneg lam)
  exact constraints_recover hN hp hpQ hm A P' ha (by simpa only [hε] using hae)
    χ lam F hχ le_rfl hs ((constraints_parameters_congr A P P' hρ a χ m lam F).mpr hc)

/-- A fixed finite collection of sector loci is exact over the WHOLE complex
eigenvalue plane; no increasing family of Banach disks or charts is required. -/
theorem global_finite_locus_iff_original (hN : 0 < N) (hp : p.Prime) (hgood : ¬ p ∣ N)
    (hpQ : p ∣ Q) (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    {a b : ℝ} (hb : 0 < b) (hab : b < a) (hae : a ≤ P.ε) (hheight : a ≤ b / P.ρ)
    {m : ℕ} (hm : 0 < m) (t : ℂ × space (radius a)) :
    (∃ s : Fin (Q + 1) → Bool, t ∈ sectorLocus hN A P hb hab m s) ↔
      ∃ f : S N (2 * m), f.val p = t.1 ∧
        representative N (2 * m) (radius_pos a) (radius_lt_one (hb.trans hab)) f = t.2 := by
  constructor
  · rintro ⟨s, _, hc⟩
    exact constraints_recover_global hN hp hpQ hm A P (hb.trans hab) hae
      (sector Q m s) t.1 t.2 (fun q _ => sector_norm Q m s q) (sector_signs Q m s 1) hc
  · rintro ⟨f, hf, hF⟩
    obtain ⟨s, hs⟩ := original_finite_constrained_pencil hN hp hgood hpQ A P hb hab hae hheight m f
    refine ⟨s, ?_⟩
    change pencil hN A hb hab (sector Q m s) m t.1 t.2 = t.2 ∧
      Constraints A P a (sector Q m s) m t.1 t.2
    simpa only [hf, hF] using hs

#print axioms constraints_recover_global
#print axioms global_finite_locus_iff_original

end FinitenessAllLevelConstraintLocus
