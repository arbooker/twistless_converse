module

public import AsymptoticFiniteBranchPolynomialV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open AsymptoticFiniteBranch

/-- Exact coefficient-mass bookkeeping on the same branch expressions
used by the concrete holomorphic and regular realizations. -/
theorem expressionBound_append (e f : Expression) :
    expressionBound (e ++ f) = expressionBound e + expressionBound f := by
  simp only [expressionBound, List.map_append, List.sum_append]

theorem expressionBound_compose (e f : Expression) :
    expressionBound (composeExpression e f) = expressionBound e * expressionBound f :=
  sum_composeExpression Branch.bound (fun _ _ => rfl) e f

theorem expressionBound_adjoint (e : Expression) :
    expressionBound (adjointExpression e) = expressionBound e := by
  simp only [expressionBound, adjointExpression, List.map_map, Function.comp_def, adjoint]

theorem expressionBound_scale (a : ℂ) (e : Expression) :
    expressionBound (scaleExpression a e) = ‖a‖ * expressionBound e := by
  simp only [expressionBound, scaleExpression, List.map_map, Function.comp_def, scale]
  exact List.sum_map_mul_left e Branch.bound ‖a‖

theorem expressionBound_power (e : Expression) (n : ℕ) :
    expressionBound (powerExpression e n) = expressionBound e ^ n := by
  induction n with
  | zero => simp [powerExpression, expressionBound, identity]
  | succ n ih => rw [powerExpression, expressionBound_compose, ih, pow_succ']

theorem expressionBound_geometric (e : Expression) (n : ℕ) :
    expressionBound (geometricExpression e n) = ∑ j ∈ Finset.range n, expressionBound e ^ j := by
  induction n with
  | zero => simp [geometricExpression, expressionBound]
  | succ n ih => rw [geometricExpression, expressionBound_append, ih, expressionBound_power, Finset.sum_range_succ]

theorem length_composeExpression (e f : Expression) :
    (composeExpression e f).length = e.length * f.length := by
  induction e with
  | nil => simp [composeExpression]
  | cons b e ih =>
    simp only [composeExpression, List.flatMap_cons, List.length_append, List.length_map,
      List.length_cons] at *
    rw [ih]
    ring

theorem length_powerExpression (e : Expression) (n : ℕ) :
    (powerExpression e n).length = e.length ^ n := by
  induction n with
  | zero => simp [powerExpression]
  | succ n ih => rw [powerExpression, length_composeExpression, ih, pow_succ']

theorem length_geometricExpression (e : Expression) (n : ℕ) :
    (geometricExpression e n).length = ∑ j ∈ Finset.range n, e.length ^ j := by
  induction n with
  | zero => simp [geometricExpression]
  | succ n ih => rw [geometricExpression, List.length_append, ih, length_powerExpression, Finset.sum_range_succ]

/-- A single positive filter expanded as a power has exactly the
expected exponential branch count and coefficient mass. -/
theorem single_filter_expression_complexity (e : Expression) (s : ℂ) (d : ℕ) :
    (powerExpression ([identity] ++ scaleExpression (-s) e) d).length = (1 + e.length) ^ d ∧
    expressionBound (powerExpression ([identity] ++ scaleExpression (-s) e) d) =
      (1 + ‖s‖ * expressionBound e) ^ d := by
  constructor
  · rw [length_powerExpression]
    simp [scaleExpression, Nat.add_comm]
  · rw [expressionBound_power, expressionBound_append, expressionBound_scale]
    simp [expressionBound, identity]

#print axioms expressionBound_compose
#print axioms expressionBound_power
#print axioms single_filter_expression_complexity

end QuantitativeHolomorphic
