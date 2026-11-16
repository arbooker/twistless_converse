module

public import SpanningCriterionTheoremV1
public import SpanningCriterionArithmeticV1

@[expose] public section

namespace SpanningCriterion

open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedPrimeChoice

/-- Part (1): the empty retained set is vanishing exactly at admissible levels. -/
theorem vanishing_empty_iff {N : ℕ} (hN : 0 < N) :
    Vanishing N ∅ ↔ ¬16 ∣ N ∧ ∀ p : ℕ, p.Prime → p ≠ 2 → ¬p^2 ∣ N := by
  rw [spanning_iff hN ∅ (by simp)]
  exact condition_empty_iff hN

/-- Part (2), with the radical inequality squared. -/
theorem vanishing_primeFactors_iff {N : ℕ} (hN : 0 < N) :
    Vanishing N N.primeFactors ↔ N ∣ 8 ∨ N < (∏ p ∈ N.primeFactors, p)^2 := by
  rw [spanning_iff hN N.primeFactors (fun _ hp => Nat.prime_of_mem_primeFactors hp)]
  exact condition_primeFactors_iff hN

/-- The natural square inequality agrees with the paper's real square root. -/
theorem square_iff_sqrt {N r : ℕ} (hr : 0 < r) :
    N < r^2 ↔ Real.sqrt (N : ℝ) < (r : ℝ) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  rw [Real.sqrt_lt (Nat.cast_nonneg N) hrR.le]
  exact_mod_cast (Iff.rfl : N < r^2 ↔ N < r^2)

/-- Part (2), with exactly the square-root inequality in the manuscript. -/
theorem vanishing_primeFactors_iff_sqrt {N : ℕ} (hN : 0 < N) :
    Vanishing N N.primeFactors ↔ N ∣ 8 ∨
      Real.sqrt (N : ℝ) < ((∏ p ∈ N.primeFactors, p : ℕ) : ℝ) := by
  rw [vanishing_primeFactors_iff hN, square_iff_sqrt]
  exact Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)

/-- Part (3): one prime above the square root of the level suffices. -/
theorem vanishing_singleton {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hlarge : Real.sqrt (N : ℝ) < (p : ℝ)) : Vanishing N {p} := by
  apply vanishing_of_condition hN {p} (by simpa using hp)
  exact condition_singleton hN hp ((square_iff_sqrt hp.pos).mpr hlarge)

/-- The length condition can equivalently be written as divisibility by
the product of the retained primes, as in the manuscript definition. -/
theorem vanishing_iff_product_length {N : ℕ} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    Vanishing N P ↔ ∃ Q : ℕ, ∃ hQ : 0 < Q, (∏ p ∈ P, p) ∣ Q ∧
      Submodule.span ℚ (Set.range (fun i j => (rows N P hQ i j : ℚ))) = ⊤ := by
  constructor
  · rintro ⟨Q,hQ,hPQ,htop⟩
    exact ⟨Q,hQ,prime_product_dvd hP hPQ,htop⟩
  · rintro ⟨Q,hQ,hprod,htop⟩
    refine ⟨Q,hQ,?_,htop⟩
    intro p hp
    exact (Finset.dvd_prod_of_mem (fun p => p) hp).trans hprod

/-- Full row-span formulation of Theorem `thm:spanning`, including the
paper's product-divisibility condition on the positive length. -/
theorem spanning_rows_iff {N : ℕ} (hN : 0 < N) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    (∃ Q : ℕ, ∃ hQ : 0 < Q, (∏ p ∈ P, p) ∣ Q ∧
      Submodule.span ℚ (Set.range (fun i j => (rows N P hQ i j : ℚ))) = ⊤) ↔
    ∀ s : ℕ, 2 < s → (∀ p ∈ P, p ∣ s) → GridAdmissibleGap.levelPart N s < s^2 := by
  rw [←vanishing_iff_product_length P hP]
  exact spanning_iff hN P hP

#print axioms spanning_rows_iff
#print axioms vanishing_empty_iff
#print axioms vanishing_primeFactors_iff_sqrt
#print axioms vanishing_singleton

end SpanningCriterion
