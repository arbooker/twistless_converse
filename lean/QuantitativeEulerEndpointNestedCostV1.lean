module

public import QuantitativeEulerEndpointNestedExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointNestedExpression
open AsymptoticFiniteBranch QuantitativeHolomorphic Polynomial

/-- Exact logarithmic cost of the common nested-expression exponent. -/
def logarithmicCost (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (j : ℕ) : ℝ :=
  Real.log 8+Real.log ((q j).natDegree+1:ℝ)+Real.log (L j+1:ℝ)

theorem budget_log (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (n : ℕ) :
    Real.log (budget L q n:ℝ)=∑ j∈Finset.range n,logarithmicCost L q j := by
  rw [budget_product,Nat.cast_prod,Real.log_prod (fun _ _ => by positivity)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,logarithmicCost]
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by norm_num) (by positivity)]

theorem budget_le_exp (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (n : ℕ) {a : ℝ}
    (ha : (∑ j∈Finset.range n,logarithmicCost L q j)≤a) :
    (budget L q n:ℝ)≤Real.exp a := by
  have hp : (0:ℝ)<budget L q n := by
    have hh : 0<budget L q n := by have h := budget_pos L q n; omega
    exact_mod_cast hh
  rw [←Real.exp_log hp]
  apply Real.exp_le_exp.mpr
  rw [budget_log]
  exact ha

/-- Summed logarithmic degree/depth cost and one common base bound give a
precise double-exponential bound. This is a complexity transfer, not a count theorem. -/
theorem power_budget_le (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (n : ℕ) {B a b : ℝ}
    (hB : 1≤B) (ha : (∑ j∈Finset.range n,logarithmicCost L q j)≤a)
    (hb : Real.log B≤Real.exp b) :
    B^(budget L q n)≤Real.exp (Real.exp (a+b)) := by
  have hBpos : 0<B := by linarith
  have he : B^(budget L q n)=Real.exp ((budget L q n:ℝ)*Real.log B) := by
    rw [Real.exp_nat_mul,Real.exp_log hBpos]
  rw [he]
  apply Real.exp_le_exp.mpr
  rw [Real.exp_add]
  exact mul_le_mul (budget_le_exp L q n ha) hb (Real.log_nonneg hB) (Real.exp_pos a).le

theorem bounds_double_exp (u initial : Expression) (g : ℕ → Expression)
    (L : ℕ → ℕ) (q : ℕ → ℝ[X]) {B a b : ℝ} (hB : 16≤B)
    (hu : expressionBound u≤1) (huM : ExpressionMatrixBound u 1)
    (hi : expressionBound initial≤B) (hiM : ExpressionMatrixBound initial B)
    (hg : ∀ j,expressionBound (g j)≤B) (hgM : ∀ j,ExpressionMatrixBound (g j) B)
    (hq : ∀ j,(∑ i∈(q j).support, |(q j).coeff i|)≤B) (n : ℕ)
    (ha : (∑ j∈Finset.range n,logarithmicCost L q j)≤a) (hb : Real.log B≤Real.exp b) :
    expressionBound (expression u initial g L q n)≤Real.exp (Real.exp (a+b)) ∧
    ExpressionMatrixBound (expression u initial g L q n) (Real.exp (Real.exp (a+b))) := by
  have h := bounds u initial g L q hB hu huM hi hiM hg hgM hq n
  have hp := power_budget_le L q n (show 1≤B by linarith) ha hb
  exact ⟨h.1.trans hp,h.2.mono hp⟩

#print axioms budget_log
#print axioms power_budget_le
#print axioms bounds_double_exp
end QuantitativeEulerEndpointNestedExpression
