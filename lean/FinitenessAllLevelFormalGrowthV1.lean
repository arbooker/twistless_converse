module

public import FinitenessAllLevelFormalCuspV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFormalContinuation

open Complex FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelGlobalHeight FinitenessAllLevelGoodTrace
  QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedReconstruction
  FinitenessAnalyticReconstruction
  Function.Periodic

/-- Polynomial height growth is deduced from the exact analytic equations.
The input is an arbitrary Banach-disk vector, not an assumed original solution. -/
theorem global_height_of_equations {N Q p : ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (hp : p.Prime) (hpQ : p ∣ Q) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ) (F : space (radius a))
    (hχ : ∀ q, q ∣ Q → ‖χ q‖ = 1) (hlam : ‖lam‖ ≤ L)
    (he : FinitenessAllLevelCauchyConstraints.CauchyIdentities (formal A P a χ m lam F))
    (hFE : ∀ q : ℕ, q ∣ Q → ∀ z : ℂ, 0 < z.im →
      twist (formal A P a χ m lam F) q z =
        χ q / (((Real.sqrt (Nat.lcm N (q ^ 2)) : ℝ) : ℂ) * z) ^ (2 * m) *
          twist (formal A P a χ m lam F) q (-1 / ((Nat.lcm N (q ^ 2) : ℕ) * z)))
    (hHecke : ∀ z : ℂ, 0 < z.im →
      completeTwist (formal A P a χ m lam F) p z =
        firstMultiplier (fun _ => lam) m p * formal A P a χ m lam F ((p : ℂ) * z) -
          (p : ℂ) ^ (2 * m) * formal A P a χ m lam F ((p : ℂ) ^ 2 * z)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, 0 < z.im →
      z.im ^ (m + P.s) * ‖formal A P a χ m lam F z‖ ≤ M := by
  obtain ⟨hG, h0, heq⟩ := formal_cusp_holomorphic hN hp A P ha hae χ m lam F he
  obtain ⟨M, hM, _, hb⟩ := FinitenessAllLevelEnvelope.global_bound hN A P
    (by intro q hq; simpa only [Finset.mem_singleton.mp hq] using hp)
    (by intro q hq; simpa only [Finset.mem_singleton.mp hq] using hpQ)
    (formal A P a χ m lam F) (formal_periodic A P a χ m lam F) χ (fun _ => lam) m hχ
    (fun _ _ => hlam) hFE
    (by intro q hq; simpa only [Finset.mem_singleton.mp hq] using hHecke)
    (fun y hy => FinitenessCuspBounds.tail _ _ hG h0 (fun z _ => (heq z).symm) (m + P.s) hy)
  exact ⟨M, hM, hb⟩

#print axioms global_height_of_equations

end FinitenessAllLevelFormalContinuation
