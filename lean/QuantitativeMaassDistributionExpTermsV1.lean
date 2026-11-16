module

public import QuantitativeMaassTestMultiplierV1
public import Mathlib.Analysis.Normed.Algebra.Exponential

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter TopologicalSpace MeasureTheory Finset
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

def distributionExpTerm (T : PositiveSmoothTest →ₗ[ℝ] H) (B : H →L[ℝ] H)
    (φ : PositiveSmoothTest) (n : ℕ) : H :=
  (n.factorial:ℝ)⁻¹ • (B^n) (T (positiveTestPower n φ))

private theorem pow_apply_commute (B : H →L[ℝ] H) (n : ℕ) (x : H) :
    (B^n) (B x)=B ((B^n) x) := by
  change (B^n*B) x=(B*B^n) x
  rw [← pow_succ,← pow_succ']

private theorem factorial_inv_mul_succ (n : ℕ) :
    ((n+1).factorial:ℝ)⁻¹*(n+1:ℝ)=(n.factorial:ℝ)⁻¹ := by
  rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,mul_inv_rev]
  have hn : (n+1:ℝ)≠0 := by positivity
  rw [mul_assoc,inv_mul_cancel₀ hn,mul_one]

theorem distributionExpTerm_deriv_zero (T : PositiveSmoothTest →ₗ[ℝ] H)
    (B : H →L[ℝ] H) (hT : ∀ φ,T (positiveSmoothTestDeriv φ)=B (T φ))
    (φ : PositiveSmoothTest) :
    distributionExpTerm T B (positiveSmoothTestDeriv φ) 0=B (distributionExpTerm T B φ 0) := by
  simpa only [distributionExpTerm,Nat.factorial_zero,Nat.cast_one,inv_one,one_smul,
    pow_zero,one_apply_eq_self,positiveTestPower_zero] using hT φ

/-- Consecutive coefficients telescope after differentiating the scalar
test. This exact identity contains no convergence or representation premise. -/
theorem distributionExpTerm_deriv_succ (T : PositiveSmoothTest →ₗ[ℝ] H)
    (B : H →L[ℝ] H) (hT : ∀ φ,T (positiveSmoothTestDeriv φ)=B (T φ))
    (φ : PositiveSmoothTest) (n : ℕ) :
    distributionExpTerm T B (positiveSmoothTestDeriv φ) (n+1)=
      B (distributionExpTerm T B φ (n+1))-B (distributionExpTerm T B φ n) := by
  have hm : T (positiveTestPower (n+1) (positiveSmoothTestDeriv φ))=
      B (T (positiveTestPower (n+1) φ))-(n+1:ℝ) • T (positiveTestPower n φ) :=
    positiveDistribution_moment_recurrence T B.toLinearMap hT n φ
  unfold distributionExpTerm
  rw [hm,map_sub,map_smul,smul_sub,smul_smul,factorial_inv_mul_succ]
  rw [pow_apply_commute]
  simp only [map_smul,pow_succ',mul_apply_eq_comp]

/-- The entire finite exponential derivative sum is its last boundary
term. Passing to the limit will use only summability of the coefficients. -/
theorem distributionExpTerm_deriv_sum (T : PositiveSmoothTest →ₗ[ℝ] H)
    (B : H →L[ℝ] H) (hT : ∀ φ,T (positiveSmoothTestDeriv φ)=B (T φ))
    (φ : PositiveSmoothTest) (n : ℕ) :
    (∑ k∈Finset.range (n+1),distributionExpTerm T B (positiveSmoothTestDeriv φ) k)=
      B (distributionExpTerm T B φ n) := by
  induction n with
  | zero => simpa only [Nat.zero_add,Finset.sum_range_one] using distributionExpTerm_deriv_zero T B hT φ
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,distributionExpTerm_deriv_succ T B hT]
    abel

#print axioms distributionExpTerm_deriv_succ
#print axioms distributionExpTerm_deriv_sum

end QuantitativeMaass
