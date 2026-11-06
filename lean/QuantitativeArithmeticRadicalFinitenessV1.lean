module

public import QuantitativeArithmeticRetainedSignPatternsV1
public import QuantitativeArithmeticRamifiedOriginalBridgeV1

@[expose] public section

namespace QuantitativeArithmeticRadicalFiniteness

open FinitenessOriginalInput

/-- Finiteness and O_N(k) cardinality for the ORIGINAL solution predicate
throughout the radical range. Every additional complete-row law, spanning
certificate, growth estimate and independence input has been discharged.
There is no common growth exponent and no modularity assumption. -/
theorem radical_level (N : ℕ) (hN : 0 < N)
    (hrad : N < (∏ p ∈ N.primeFactors, p)^2) :
    ∃ C : ℕ, 0 < C ∧ ∀ m : ℕ, 0 < m →
      (S N (2*m)).Finite ∧ (S N (2*m)).ncard ≤ C*m := by
  obtain ⟨Q,C,hQ,hNQ,hC,hbound⟩ :=
    QuantitativeArithmeticRetainedHolomorphicSpace.radical_level N hN hrad
  refine ⟨6^(Q+1)*C,Nat.mul_pos (pow_pos (by norm_num) _) hC,?_⟩
  intro m hm
  have hh := QuantitativeArithmeticRetainedSignPatterns.count_of_complete hN hQ hNQ
    (QuantitativeArithmeticRamifiedOriginalBridge.original_sign_cover hm)
    (fun e => hbound (FinitenessSignPatterns.multiplier Q m e.1)
      (QuantitativeArithmeticRetainedSignPatterns.multiplier Q m e.2) m hm
      (fun q _ => FinitenessSignPatterns.unit_norm Q m e.1 q)
      (fun p _ => QuantitativeArithmeticRetainedSignPatterns.norm_bound Q m e.2 p))
  simpa only [Nat.mul_assoc] using hh

/-- Positive-even-weight formulation of the radical-range finiteness
part of Theorem 1.2, including its coarse linear bound. -/
theorem even_weight (N : ℕ) (hN : 0 < N)
    (hrad : N < (∏ p ∈ N.primeFactors, p)^2) :
    ∃ C : ℕ, 0 < C ∧ ∀ k : ℕ, 0 < k → Even k →
      (S N k).Finite ∧ (S N k).ncard ≤ C*k := by
  obtain ⟨C,hC,hbound⟩ := radical_level N hN hrad
  refine ⟨C,hC,?_⟩
  intro k hk heven
  obtain ⟨m,rfl⟩ := heven
  have hm : 0 < m := by omega
  obtain ⟨hf,hb⟩ := hbound m hm
  rw [two_mul] at hf hb
  exact ⟨hf,hb.trans (Nat.mul_le_mul_left C (by omega))⟩

/-- The paper's `rad(N) > sqrt(N)` formulation, with radical written as
the product of the distinct prime divisors of N. -/
theorem even_weight_sqrt (N : ℕ) (hN : 0 < N)
    (hrad : Real.sqrt (N : ℝ) < ((∏ p ∈ N.primeFactors, p : ℕ) : ℝ)) :
    ∃ C : ℕ, 0 < C ∧ ∀ k : ℕ, 0 < k → Even k →
      (S N k).Finite ∧ (S N k).ncard ≤ C*k := by
  apply even_weight N hN
  have hsq := Real.sq_sqrt (Nat.cast_nonneg N)
  have hnonneg := Real.sqrt_nonneg (N : ℝ)
  have hreal : (N : ℝ) < (((∏ p ∈ N.primeFactors, p : ℕ) : ℝ))^2 := by nlinarith
  exact_mod_cast hreal

#print axioms radical_level
#print axioms even_weight
#print axioms even_weight_sqrt

end QuantitativeArithmeticRadicalFiniteness
