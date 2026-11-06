module

public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Nat.Totient
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmetic

open Finset

/-- The literal one-dimensional Selberg denominator, with primes dividing
the fixed progression modulus removed. -/
def shiftedSieveDenominator (R z : ℕ) : ℝ := by
  classical
  exact ∑ n ∈ Icc 1 z,
    if Squarefree n ∧ Nat.Coprime n R then 1 / (Nat.totient n : ℝ) else 0

/-- Harmonic mass of integers coprime to the fixed progression modulus. -/
def coprimeHarmonic (R z : ℕ) : ℝ := by
  classical
  exact ∑ n ∈ Icc 1 z, if Nat.Coprime n R then 1 / (n : ℝ) else 0

/-- Harmonic mass of squarefree integers coprime to the modulus. -/
def squarefreeCoprimeHarmonic (R z : ℕ) : ℝ := by
  classical
  exact ∑ n ∈ Icc 1 z,
    if Squarefree n ∧ Nat.Coprime n R then 1 / (n : ℝ) else 0

end QuantitativeArithmetic
