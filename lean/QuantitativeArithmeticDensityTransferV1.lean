module

public import QuantitativeArithmeticDensityV1
public import QuantitativeHolomorphicDensityTransferV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmetic

open Finset Filter

/-- The density definition supplies precisely the existing Abel-summation
input. This is conditional on ordinary counting density, not a proof of it. -/
theorem good_prime_mass_of_relative_density_one (P : ℕ → Prop) [DecidablePred P]
    (hP : RelativePrimeDensityOne P) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
      (1 - ε) * Real.log (Real.log (n + 1 : ℝ)) - C ≤
        ∑ p ∈ (n + 1).primesBelow.filter P, 1 / ((p : ℝ) - 1) := by
  apply QuantitativeHolomorphic.good_prime_mass_of_count_density P (le_of_lt hε) hε1
  simpa only [badPrimeCount_eq] using hP ε hε

/-- A density-one set supplies every product exponent strictly below the
single-prime contraction parameter, with no progression-density factor. -/
theorem good_prime_product_of_relative_density_one (P : ℕ → Prop) [DecidablePred P]
    (hP : RelativePrimeDensityOne P) {σ b : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hb : 0 ≤ b) (hbσ : b < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
      (∏ p ∈ (n + 1).primesBelow.filter P, (1 - σ / ((p : ℝ) - 1))) ≤
        Real.exp C * (Real.log (n + 1 : ℝ)) ^ (-b) := by
  let ε := (σ - b) / σ
  have hε : 0 < ε := div_pos (sub_pos.mpr hbσ) hσ
  have hε1 : ε ≤ 1 := (div_le_one hσ).mpr (by linarith)
  have hcount : ∀ᶠ n : ℕ in atTop,
      ((n.primesBelow.filter (fun p => ¬ P p)).card : ℝ) ≤
        ε * (n.primesBelow.card : ℝ) := by
    simpa only [badPrimeCount_eq] using hP ε hε
  have heq : σ * (1 - ε) = b := by
    dsimp [ε]
    field_simp [ne_of_gt hσ]
    ring
  simpa only [heq] using
    QuantitativeHolomorphic.good_prime_product_of_count_density P
      (le_of_lt hε) hε1 (le_of_lt hσ) hσ1 hcount

/-- Assemble the finite family of arithmetic conditions and remove all fixed
exceptional primes before applying the contraction-product estimate.
The analytic density of each family member remains an explicit hypothesis. -/
theorem finite_family_product_of_density_one {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (P : ι → ℕ → Prop) [∀ i, DecidablePred (P i)] (S : Finset ℕ)
    (hP : ∀ i ∈ s, RelativePrimeDensityOne (P i))
    {σ b : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hb : 0 ≤ b) (hbσ : b < σ) :
    let good := fun p => (∀ i ∈ s, P i p) ∧ p ∉ S
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
      (∏ p ∈ (n + 1).primesBelow.filter good, (1 - σ / ((p : ℝ) - 1))) ≤
        Real.exp C * (Real.log (n + 1 : ℝ)) ^ (-b) := by
  classical
  exact good_prime_product_of_relative_density_one _
    (relativePrimeDensityOne_remove_finset (relativePrimeDensityOne_finset s P hP) S)
    hσ hσ1 hb hbσ

#print axioms good_prime_mass_of_relative_density_one
#print axioms good_prime_product_of_relative_density_one
#print axioms finite_family_product_of_density_one

end QuantitativeArithmetic
