module

public import QuantitativeEulerEndpointPhysicalResidualV1
public import QuantitativeEulerEndpointNestedCostV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointResidual
open Polynomial QuantitativeEulerEndpointNestedExpression QuantitativeEulerEndpointExpressionGrowth
open scoped Classical

theorem nat_add_one_le_power {B : ℝ} (hB : 2≤B) (n : ℕ) : (n:ℝ)+1≤B^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    push_cast
    have hh := mul_le_mul_of_nonneg_right ih (by linarith : 0≤B)
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]

theorem residual_factor_le {B : ℝ} (hB : 16≤B) (L : ℕ) (q : ℝ[X])
    (hq : (∑ i∈q.support, |q.coeff i|)≤B) :
    (1+slopeMass q)*(4+2*(L:ℝ))≤B^(q.natDegree+L+2) := by
  have hB0 : 0≤B := by linarith
  have hB2 : 2≤B := by linarith
  have hs := (slopeMass_le q).trans (mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _))
  have hd := nat_add_one_le_power hB2 q.natDegree
  have hL := nat_add_one_le_power hB2 L
  have hfirst : 1+slopeMass q≤B^(q.natDegree+1) := by
    rw [pow_succ]
    have hm := mul_le_mul_of_nonneg_right hd hB0
    nlinarith
  have hsecond : 4+2*(L:ℝ)≤B^(L+1) := by
    rw [pow_succ]
    have hm := mul_le_mul_of_nonneg_right hL hB0
    nlinarith [Nat.cast_nonneg (α:=ℝ) L]
  calc
    _ ≤ B^(q.natDegree+1)*B^(L+1) := mul_le_mul hfirst hsecond (by positivity) (by positivity)
    _ = _ := by rw [←pow_add]; congr 1; omega

/-- The residual amplification fits the SAME exponent already used for
finite-expression complexity, with no extra growth assumption on block depth. -/
theorem errorBudget_le_power (L : ℕ → ℕ) (q : ℕ → ℝ[X]) {B : ℝ} (hB : 16≤B)
    (n : ℕ) (hq : ∀ j<n,(∑ i∈(q j).support, |(q j).coeff i|)≤B) :
    errorBudget L q n≤B^(budget L q n) := by
  induction n with
  | zero => simpa only [errorBudget,budget,pow_one] using (show 1≤B by linarith)
  | succ n ih =>
    have hn := ih (fun j hj => hq j (by omega))
    have hr := budget_pos L q n
    have hex : (q n).natDegree+L n+2+budget L q n≤
        stepExponent (budget L q n) (L n) (q n).natDegree := by
      have hh : (q n).natDegree+L n+2≤2*((q n).natDegree+1)*(L n+1) := by nlinarith
      have hm := Nat.mul_le_mul_left (((q n).natDegree+1)*(L n+1)) hr
      have hp : 1≤((q n).natDegree+1)*(L n+1) := by
        have hh : 0<((q n).natDegree+1)*(L n+1) := by positivity
        omega
      have hm2 := Nat.mul_le_mul_right (budget L q n) hp
      unfold stepExponent
      nlinarith
    calc
      _ ≤ B^((q n).natDegree+L n+2)*B^(budget L q n) :=
        mul_le_mul (residual_factor_le hB (L n) (q n) (hq n (by omega))) hn
          (by linarith [errorBudget_ge_one L q n]) (by positivity)
      _ = B^((q n).natDegree+L n+2+budget L q n) := (pow_add _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) hex

theorem errorBudget_double_exp (L : ℕ → ℕ) (q : ℕ → ℝ[X]) {B a b : ℝ} (hB : 16≤B)
    (n : ℕ) (hq : ∀ j<n,(∑ i∈(q j).support, |(q j).coeff i|)≤B)
    (ha : (∑ j∈Finset.range n,logarithmicCost L q j)≤a) (hb : Real.log B≤Real.exp b) :
    errorBudget L q n≤Real.exp (Real.exp (a+b)) :=
  (errorBudget_le_power L q hB n hq).trans (power_budget_le L q n (by linarith) ha hb)

#print axioms errorBudget_le_power
#print axioms errorBudget_double_exp
end QuantitativeEulerEndpointResidual
