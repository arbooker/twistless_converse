module

public import FinitenessAllLevelFiniteSectorFibersV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelGlobalHeight

open QuantitativeArithmeticRetainedCertificate FinitenessAllLevelHeightWeights

/-- Increasing or decreasing the auxiliary eigenvalue bound only changes the
weight exponent. The actual geometric height parameters remain identical. -/
theorem parameters_change_bound {N Q : ℕ} {S : Finset ℕ} {hQ : 0 < Q}
    (A : Certificate N S Q hQ) {L : ℝ} (P : Parameters A L)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ P' : Parameters A B, P'.ε = P.ε ∧ P'.ρ = P.ρ := by
  obtain ⟨s, hs⟩ := FinitenessIntegerWeight.exists_exponent
    ((by norm_num : (0 : ℝ) ≤ 1).trans (one_le_cost A hB)) P.rho_lt_one
  exact ⟨⟨hB, P.ε, P.ρ, s, P.epsilon_pos, P.rho_pos, P.rho_lt_one,
    P.rho_half, hs, P.small⟩, rfl, rfl⟩

#print axioms parameters_change_bound

end FinitenessAllLevelGlobalHeight

namespace FinitenessAllLevelFormalContinuation

open FinitenessAllLevelGlobalHeight FinitenessAllLevelDiskAlgebra
  FinitenessAllLevelBoundaryCoordinates QuantitativeArithmeticRetainedCertificate

variable {N Q p : ℕ} {hQ : 0 < Q}

theorem depth_parameters_congr (A : Certificate N {p} Q hQ) {L B : ℝ}
    (P : Parameters A L) (P' : Parameters A B) (hρ : P'.ρ = P.ρ) (a : ℝ) (z : ℂ) :
    depth A P' a z = depth A P a z := by
  unfold depth
  split
  · congr 1
    rw [hρ]
  · rfl

/-- The globally defined continuation is independent of the growth budget. -/
theorem formal_parameters_congr (A : Certificate N {p} Q hQ) {L B : ℝ}
    (P : Parameters A L) (P' : Parameters A B) (hρ : P'.ρ = P.ρ)
    (a : ℝ) (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ) (F : space (radius a)) :
    formal A P' a χ m lam F = formal A P a χ m lam F := by
  funext z
  unfold formal
  rw [depth_parameters_congr A P P' hρ]

#print axioms depth_parameters_congr
#print axioms formal_parameters_congr

end FinitenessAllLevelFormalContinuation

namespace FinitenessAllLevelConstraintLocus

open FinitenessAllLevelGlobalHeight FinitenessAllLevelDiskAlgebra
  FinitenessAllLevelBoundaryCoordinates FinitenessAllLevelFormalContinuation
  QuantitativeArithmeticRetainedCertificate

variable {N Q p : ℕ} {hQ : 0 < Q}

theorem constraints_parameters_congr (A : Certificate N {p} Q hQ) {L B : ℝ}
    (P : Parameters A L) (P' : Parameters A B) (hρ : P'.ρ = P.ρ)
    (a : ℝ) (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ) (F : space (radius a)) :
    Constraints A P' a χ m lam F ↔ Constraints A P a χ m lam F := by
  have he := formal_parameters_congr A P P' hρ a χ m lam F
  constructor
  · intro h
    exact ⟨by simpa only [he] using h.cauchy, by simpa only [he] using h.fricke,
      by simpa only [he] using h.hecke, h.euler⟩
  · intro h
    exact ⟨by simpa only [he] using h.cauchy, by simpa only [he] using h.fricke,
      by simpa only [he] using h.hecke, h.euler⟩

#print axioms constraints_parameters_congr

end FinitenessAllLevelConstraintLocus
