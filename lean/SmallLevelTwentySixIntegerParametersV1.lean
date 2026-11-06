module
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelTwentySixIntegerParameters
open Complex

theorem sign_ne_zero (s : ℤ) (h : s=1 ∨ s= -1) : (s:ℂ)≠0 := by
  rcases h with rfl|rfl <;> norm_num

theorem signed_two_bound (s : ℤ) (n : ℕ) (hs : s=1 ∨ s= -1) (hn : 1≤n) :
    2≤(s:ℝ)*2^n ∨ (s:ℝ)*2^n≤ -2 := by
  have hp : (2:ℝ)≤2^n := by
    simpa using (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hn)
  rcases hs with rfl|rfl
  · exact Or.inl (by simpa using hp)
  · exact Or.inr (by simpa using neg_le_neg hp)

theorem square_three (n : ℕ) : ((3:ℂ)^n)^2=(9:ℂ)^n := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

theorem square_five (n : ℕ) : ((5:ℂ)^n)^2=(25:ℂ)^n := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

#print axioms signed_two_bound
end SmallLevelTwentySixIntegerParameters
