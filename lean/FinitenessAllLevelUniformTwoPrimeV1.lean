module

public import FinitenessAllLevelFiniteSectorsV1
public import FinitenessAllLevelAuxiliaryV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelTwoPrimeBounds

open Complex FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelGlobalHeight FinitenessAllLevelFormalContinuation
  FinitenessOriginalInput QuantitativeArithmeticRetainedCertificate
  FinitenessAllLevelAuxiliary

/-- The constant is uniform over all original solutions and all root sectors. -/
theorem uniform_ceiling_comparison {N Q r p : ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (hr : r.Prime) (hrgood : ¬ r ∣ N) (hrQ : r ∣ Q)
    (hp : p.Prime) (hpgood : ¬ p ∣ N)
    (A : Certificate N {r} Q hQ) {L : ℝ} (P : Parameters A L)
    {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε) (m t : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : S N (2 * m),
      ‖f.val p‖ ^ t ≤ C * (1 + ‖f.val r‖) ^
        Nat.ceil ((t : ℝ) * (Real.log p / Real.log r)) := by
  classical
  have hs := fun s : Fin (Q + 1) → Bool =>
    ceiling_comparison hN hr hp hpgood A P ha hae (sector Q m s) m t
  choose C hC hb using hs
  refine ⟨∑ s, C s, Finset.sum_nonneg (fun s _ => hC s), fun f => ?_⟩
  obtain ⟨s, he⟩ := original_finite_sector hN hr hrgood hrQ A P ha hae m f
  exact (hb s f he).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun s _ => hC s) (Finset.mem_univ s)) (by positivity))

/-- No certificate or reconstruction premise remains in this bound on the
literal original solution set. Individual growth exponents are unrestricted. -/
theorem original_ceiling_comparison {N r p : ℕ}
    (hN : 0 < N) (hr : r.Prime) (hrgood : ¬ r ∣ N) (hrlarge : N < r ^ 2)
    (hp : p.Prime) (hpgood : ¬ p ∣ N) (m t : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : S N (2 * m),
      ‖f.val p‖ ^ t ≤ C * (1 + ‖f.val r‖) ^
        Nat.ceil ((t : ℝ) * (Real.log p / Real.log r)) := by
  obtain ⟨Q, hQ, _, hrQ, ⟨A⟩⟩ := certificate_at_prime hN hr hrlarge
  obtain ⟨P⟩ := parameters_exist hN hQ A (L := 0) le_rfl
  exact uniform_ceiling_comparison hN hr hrgood hrQ hp hpgood A P
    P.epsilon_pos le_rfl m t

/-- Both sharp families hold at two fixed distinct good primes for every
positive level and every even weight. Constants precede all original solutions. -/
theorem original_two_prime_bounds (N : ℕ) (hN : 0 < N) :
    ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p ≠ r ∧ ¬ p ∣ N ∧ ¬ r ∣ N ∧
      ∀ m t : ℕ, ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ f : S N (2 * m),
        (‖f.val p‖ ^ t ≤ C * (1 + ‖f.val r‖) ^
          Nat.ceil ((t : ℝ) * (Real.log p / Real.log r))) ∧
        (‖f.val r‖ ^ t ≤ D * (1 + ‖f.val p‖) ^
          Nat.ceil ((t : ℝ) * (Real.log r / Real.log p))) := by
  obtain ⟨p, r, hp, hr, hne, hpN, hrN, hpl, hrl⟩ := two_large_good_primes N hN
  refine ⟨p, r, hp, hr, hne, hpN, hrN, fun m t => ?_⟩
  obtain ⟨C, hC, hc⟩ := original_ceiling_comparison hN hr hrN hrl hp hpN m t
  obtain ⟨D, hD, hd⟩ := original_ceiling_comparison hN hp hpN hpl hr hrN m t
  exact ⟨C, D, hC, hD, fun f => ⟨hc f, hd f⟩⟩

#print axioms uniform_ceiling_comparison
#print axioms original_ceiling_comparison
#print axioms original_two_prime_bounds

end FinitenessAllLevelTwoPrimeBounds
