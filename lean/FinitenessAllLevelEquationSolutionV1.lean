module

public import FinitenessAllLevelFormalSolutionV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFormalContinuation

open Complex FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelGlobalHeight FinitenessAllLevelGoodTrace
  FinitenessAllLevelCoefficientFunctional FinitenessOriginalInput
  QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedReconstruction
  FinitenessAnalyticReconstruction

/-- The exact spatial and arithmetic equations imply the original solution
predicate for an arbitrary disk input. Polynomial growth and entire finite-order
continuation are consequences, not extra assumptions on that input. -/
theorem solution_of_equations {N Q p m : ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (hp : p.Prime) (hpQ : p ∣ Q) (hm : 0 < m)
    (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (lam : ℂ) (F : space (radius a))
    (hχ : ∀ q, q ∣ Q → ‖χ q‖ = 1) (hlam : ‖lam‖ ≤ L)
    (hsign : χ 1 = I ^ (2 * m) ∨ χ 1 = -(I ^ (2 * m)))
    (he : FinitenessAllLevelCauchyConstraints.CauchyIdentities (formal A P a χ m lam F))
    (hFE : ∀ q : ℕ, q ∣ Q → ∀ z : ℂ, 0 < z.im →
      twist (formal A P a χ m lam F) q z =
        χ q / (((Real.sqrt (Nat.lcm N (q ^ 2)) : ℝ) : ℂ) * z) ^ (2 * m) *
          twist (formal A P a χ m lam F) q (-1 / ((Nat.lcm N (q ^ 2) : ℕ) * z)))
    (hHecke : ∀ z : ℂ, 0 < z.im →
      completeTwist (formal A P a χ m lam F) p z =
        firstMultiplier (fun _ => lam) m p * formal A P a χ m lam F ((p : ℂ) * z) -
          (p : ℂ) ^ (2 * m) * formal A P a χ m lam F ((p : ℂ) ^ 2 * z))
    (heuler : ∀ e : FinitenessAllLevelEulerEquations.Equation N,
      FinitenessAllLevelEulerEquations.equation N (2 * m) p (radius_pos a) e (lam, F) = 0) :
    IsSolution N (2 * m) (fun n => normalizedCLM (radius_pos a) (2 * m) n F) ∧
      normalizedCLM (radius_pos a) (2 * m) p F = lam := by
  obtain ⟨M, hM, hb⟩ := global_height_of_equations hN hp hpQ A P ha hae χ m lam F
    hχ hlam he hFE hHecke
  have hfr (z : ℂ) (hz : 0 < z.im) : formal A P a χ m lam F z =
      χ 1 / (((Real.sqrt N : ℝ) : ℂ) * z) ^ (2 * m) *
        formal A P a χ m lam F (-1 / ((N : ℂ) * z)) := by
    simpa [twist] using hFE 1 (one_dvd Q) z hz
  rcases hsign with hs | hs
  · apply solution_of_height_fricke hN hp hm A P ha hae χ lam F he hM hb
      1 (Or.inl rfl) _ heuler
    simpa only [one_mul, hs] using hfr
  · apply solution_of_height_fricke hN hp hm A P ha hae χ lam F he hM hb
      (-1) (Or.inr rfl) _ heuler
    simpa only [neg_one_mul, hs] using hfr

#print axioms solution_of_equations

end FinitenessAllLevelFormalContinuation
