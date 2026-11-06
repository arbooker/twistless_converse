module

public import QuantitativeEulerEndpointFiniteSieveV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointSieve
open Finset Nat

/-- Primes avoiding the shifted residues survive the two-residue sieve
unless they are themselves at most the auxiliary-prime cutoff. -/
theorem shifted_prime_count_le_sifted (P Q x y : ℕ)
    (active : ℕ → Prop) [DecidablePred active]
    (hy : ∀ p∈P.primeFactors, p≤y) :
    (Nat.count (fun n : ℕ => n.Prime ∧ ∀ p∈P.primeFactors,
      active p → (n : ZMod p)≠Q) x : ℝ)≤
    (Nat.count (fun n : ℕ => ∀ p∈P.primeFactors,
      (n : ZMod p)≠0 ∧ (active p → (n : ZMod p)≠Q)) x : ℝ)+(y+1 : ℕ) := by
  classical
  let A := (range x).filter (fun n : ℕ => n.Prime ∧ ∀ p∈P.primeFactors,
    active p → (n : ZMod p)≠Q)
  let B := (range x).filter (fun n : ℕ => ∀ p∈P.primeFactors,
    (n : ZMod p)≠0 ∧ (active p → (n : ZMod p)≠Q))
  have hsub : A⊆B ∪ range (y+1) := by
    intro n hn
    obtain ⟨hnx,hnprime,hnavoid⟩ := mem_filter.mp hn
    by_cases hny : n≤y
    · exact mem_union_right _ (mem_range.mpr (by omega))
    · apply mem_union_left
      apply mem_filter.mpr
      refine ⟨hnx,fun p hp => ⟨?_,hnavoid p hp⟩⟩
      intro hzero
      have hdiv := (ZMod.natCast_eq_zero_iff n p).mp hzero
      have he := (hnprime.dvd_iff_eq (Nat.prime_of_mem_primeFactors hp).ne_one).mp hdiv
      exact hny (he ▸ hy p hp)
  have hcard := (card_le_card hsub).trans (card_union_le B (range (y+1)))
  rw [card_range] at hcard
  simp only [Nat.count_eq_card_filter_range]
  exact_mod_cast hcard

/-- Fully finite upper bound for the actual shifted-exception prime set.
Only the explicit Euler product remains to be estimated arithmetically. -/
theorem shifted_prime_count_le_product (P : ℕ) (hP : Squarefree P)
    (Q : ℕ) (active : ℕ → Prop) [DecidablePred active]
    (hp3 : ∀ p∈P.primeFactors, 2<p)
    (hQ : ∀ p∈P.primeFactors, active p → (Q : ZMod p)≠0)
    (x z y : ℕ) (hy4 : 4≤y) (hyz : y^24≤z)
    (hy : ∀ p∈P.primeFactors, p≤y) :
    (Nat.count (fun n : ℕ => n.Prime ∧ ∀ p∈P.primeFactors,
      active p → (n : ZMod p)≠Q) x : ℝ)≤
      2*(x : ℝ)*(∏ p∈P.primeFactors, (1-(if active p then (2 : ℝ) else 1)/(p : ℝ)))+
        (z : ℝ)^6+(y+1 : ℕ) := by
  exact (shifted_prime_count_le_sifted P Q x y active hy).trans
    (add_le_add (two_residue_sifted_bound P hP Q active hp3 hQ x z y hy4 hyz hy) le_rfl)

attribute [local instance] Classical.propDecidable

/-- Absence of any divisor in the selected class implies absence of an
auxiliary prime divisor. The initial interval below the shift costs Q. -/
theorem divisor_exception_count_le_shifted (P Q x : ℕ)
    (active : ℕ → Prop) [DecidablePred active] :
    (Nat.count (fun n : ℕ => n.Prime ∧ ¬∃ d : ℕ, d∣n-Q ∧ active d) x : ℝ)≤
    (Nat.count (fun n : ℕ => n.Prime ∧ ∀ p∈P.primeFactors,
      active p → (n : ZMod p)≠Q) x : ℝ)+(Q : ℝ) := by
  classical
  let A := (range x).filter (fun n : ℕ => n.Prime ∧ ¬∃ d : ℕ, d∣n-Q ∧ active d)
  let B := (range x).filter (fun n : ℕ => n.Prime ∧ ∀ p∈P.primeFactors,
    active p → (n : ZMod p)≠Q)
  have hsub : A⊆B ∪ range Q := by
    intro n hn
    obtain ⟨hnx,hnprime,hnnone⟩ := mem_filter.mp hn
    by_cases hQn : Q≤n
    · apply mem_union_left
      apply mem_filter.mpr
      refine ⟨hnx,hnprime,fun p _ hpactive he => ?_⟩
      apply hnnone
      refine ⟨p,?_,hpactive⟩
      apply (ZMod.natCast_eq_zero_iff (n-Q) p).mp
      rw [Nat.cast_sub hQn,he,sub_self]
    · exact mem_union_right _ (mem_range.mpr (by omega))
  have hc := (card_le_card hsub).trans (card_union_le B (range Q))
  rw [card_range] at hc
  simp only [Nat.count_eq_card_filter_range]
  exact_mod_cast hc

/-- Actual shifted-divisor exceptions satisfy the finite two-residue sieve
bound. Taking active d to mean d ≡ a mod M gives the desired arithmetic
exceptional set; quantitative AP product decay is still a separate step. -/
theorem divisor_exception_count_le_product (P : ℕ) (hP : Squarefree P)
    (Q : ℕ) (active : ℕ → Prop) [DecidablePred active]
    (hp3 : ∀ p∈P.primeFactors, 2<p)
    (hQ : ∀ p∈P.primeFactors, active p → (Q : ZMod p)≠0)
    (x z y : ℕ) (hy4 : 4≤y) (hyz : y^24≤z)
    (hy : ∀ p∈P.primeFactors, p≤y) :
    (Nat.count (fun n : ℕ => n.Prime ∧ ¬∃ d : ℕ, d∣n-Q ∧ active d) x : ℝ)≤
      2*(x : ℝ)*(∏ p∈P.primeFactors, (1-(if active p then (2 : ℝ) else 1)/(p : ℝ)))+
        (z : ℝ)^6+(y+1 : ℕ)+(Q : ℝ) := by
  exact (divisor_exception_count_le_shifted P Q x active).trans
    (add_le_add (shifted_prime_count_le_product P hP Q active hp3 hQ x z y hy4 hyz hy) le_rfl)

#print axioms divisor_exception_count_le_product
#print axioms shifted_prime_count_le_sifted
#print axioms shifted_prime_count_le_product
end QuantitativeEulerEndpointSieve
