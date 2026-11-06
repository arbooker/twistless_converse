module

public import FinitenessAllLevelTwoPrimeBoundsV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFormalContinuation

open Complex FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelGlobalHeight FinitenessAllLevelReconstruction
  QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedReconstruction

variable {N Q p : ℕ} {hQ : 0 < Q}

theorem step_sector_congr (A : Certificate N {p} Q hQ) {χ ψ : ℕ → ℂ}
    (he : ∀ q, q ∣ Q → χ q = ψ q) (m : ℕ) (lam : ℂ) (G : ℂ → ℂ) (z : ℂ) :
    step A χ m lam G z = step A ψ m lam G z := by
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  cases i with
  | inl i => simp only [twoDilationRow, frickeRow, he i.val.1 i.property.1]
  | inr i => rfl

theorem iterate_sector_congr (A : Certificate N {p} Q hQ) {χ ψ : ℕ → ℂ}
    (he : ∀ q, q ∣ Q → χ q = ψ q) (a : ℝ) (m : ℕ) (lam : ℂ)
    (F : space (radius a)) (n : ℕ) :
    iterate A a χ m lam F n = iterate A a ψ m lam F n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext z
    simp only [iterate, ih]
    by_cases hz : a ≤ z.im
    · simp only [ite_eq_left hz]
    · simp only [ite_eq_right hz]
      exact step_sector_congr A he m lam _ z

theorem formal_sector_congr (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    {χ ψ : ℕ → ℂ} (he : ∀ q, q ∣ Q → χ q = ψ q) (a : ℝ) (m : ℕ) (lam : ℂ)
    (F : space (radius a)) (z : ℂ) : formal A P a χ m lam F z = formal A P a ψ m lam F z :=
  congrFun (iterate_sector_congr A he a m lam F _) z

/-- Only finitely many signs are read by the actual certificate tree. -/
def sector (Q m : ℕ) (s : Fin (Q + 1) → Bool) (q : ℕ) : ℂ :=
  if h : q < Q + 1 then if s ⟨q, h⟩ then I ^ (2 * m) else -I ^ (2 * m) else I ^ (2 * m)

theorem exists_sector (hQ : 0 < Q) (m : ℕ) (χ : ℕ → ℂ)
    (hχ : ∀ q, χ q = I ^ (2 * m) ∨ χ q = -I ^ (2 * m)) :
    ∃ s : Fin (Q + 1) → Bool, ∀ q, q ∣ Q → sector Q m s q = χ q := by
  classical
  refine ⟨fun q => decide (χ q.val = I ^ (2 * m)), fun q hq => ?_⟩
  have hlt : q < Q + 1 := Nat.lt_succ_of_le (Nat.le_of_dvd hQ hq)
  rcases hχ q with he | he
  · simp [sector, hlt, he]
  · simpa [sector, hlt, he] using (fun h : -I ^ (2 * m) = I ^ (2 * m) => h.symm)

/-- Every original solution is recovered in one of a fixed finite list of
sectors, rather than an unrestricted space of functions on all natural q. -/
theorem original_finite_sector (hN : 0 < N) (hp : p.Prime) (hgood : ¬ p ∣ N)
    (hpQ : p ∣ Q) (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε) (m : ℕ) (f : FinitenessOriginalInput.S N (2 * m)) :
    ∃ s : Fin (Q + 1) → Bool, ∀ z : ℂ, 0 < z.im →
      formal A P a (sector Q m s) m (f.val p)
        (representative N (2 * m) (radius_pos a) (radius_lt_one ha) f) z =
          FinitenessFourierConstruction.fourier (FinitenessOriginalFourier.fullCoefficients f.val (2 * m)) z := by
  obtain ⟨χ, hs, _, he⟩ := original_formal hN hp hgood hpQ A P ha hae m f
  obtain ⟨s, hsec⟩ := exists_sector hQ m χ hs
  exact ⟨s, fun z hz => (formal_sector_congr A P hsec a m (f.val p) _ z).trans (he z hz)⟩

#print axioms formal_sector_congr
#print axioms exists_sector
#print axioms original_finite_sector

end FinitenessAllLevelFormalContinuation
