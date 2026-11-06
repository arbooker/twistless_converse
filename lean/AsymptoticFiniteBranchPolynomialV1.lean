module

public import AsymptoticFiniteBranchExpressionV1
public import AsymptoticInversePolynomialV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFiniteBranch

open UpperHalfPlane ContinuousLinearMap

noncomputable def powerExpression (e : Expression) : ℕ → Expression
  | 0 => [identity]
  | n+1 => composeExpression e (powerExpression e n)

noncomputable def geometricExpression (e : Expression) : ℕ → Expression
  | 0 => []
  | n+1 => geometricExpression e n++powerExpression e n

theorem holomorphicSum_power (e : Expression) (n m : ℕ) :
    holomorphicSum (powerExpression e n) m=(holomorphicSum e m)^n := by
  induction n with
  | zero => simp [powerExpression,holomorphicSum,holomorphic_identity]
  | succ n ih =>
    rw [powerExpression,holomorphicSum_compose,ih,pow_succ',mul_def]

theorem regularSum_power (e : Expression) (n : ℕ) (z : ℍ) :
    regularSum (powerExpression e n) z=(regularSum e z)^n := by
  induction n with
  | zero => simp [powerExpression,regularSum,regular_identity]
  | succ n ih =>
    change regularSum (composeExpression e (powerExpression e n)) z=(regularSum e z)^(n+1)
    exact (regularSum_compose e (powerExpression e n) z).trans
      ((congrArg (fun T => (regularSum e z).comp T) ih).trans (pow_succ' (regularSum e z) n).symm)

theorem holomorphicSum_geometric (e : Expression) (n m : ℕ) :
    holomorphicSum (geometricExpression e n) m=∑ j∈Finset.range n,(holomorphicSum e m)^j := by
  induction n with
  | zero => simp [geometricExpression,holomorphicSum]
  | succ n ih =>
    rw [geometricExpression,holomorphicSum_append,ih,holomorphicSum_power,Finset.sum_range_succ]

theorem regularSum_geometric (e : Expression) (n : ℕ) (z : ℍ) :
    regularSum (geometricExpression e n) z=∑ j∈Finset.range n,(regularSum e z)^j := by
  induction n with
  | zero => simp [geometricExpression,regularSum]
  | succ n ih =>
    change regularSum (geometricExpression e n++powerExpression e n) z=_
    exact (regularSum_append _ _ z).trans
      ((congrArg₂ (·+·) ih (regularSum_power e n z)).trans (Finset.sum_range_succ _ _).symm)

noncomputable def stepExpression (C : ℝ) (e : Expression) : Expression :=
  [identity]++scaleExpression (-(AsymptoticCoerciveNeumann.scale C:ℂ)) e

noncomputable def inversePolynomialExpression (C : ℝ) (e : Expression) (n : ℕ) : Expression :=
  scaleExpression (AsymptoticCoerciveNeumann.scale C:ℂ) (geometricExpression (stepExpression C e) n)

theorem holomorphicSum_step (C : ℝ) (e : Expression) (m : ℕ) :
    holomorphicSum (stepExpression C e) m=AsymptoticCoerciveNeumann.step C (holomorphicSum e m) := by
  rw [stepExpression,holomorphicSum_append,holomorphicSum_scale]
  simp only [holomorphicSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    holomorphic_identity,add_zero,AsymptoticCoerciveNeumann.step,sub_eq_add_neg]
  exact congrArg (fun T : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space => 1+T)
    (neg_smul (AsymptoticCoerciveNeumann.scale C:ℂ) (holomorphicSum e m))

theorem regularSum_step (C : ℝ) (e : Expression) (z : ℍ) :
    regularSum (stepExpression C e) z=AsymptoticCoerciveNeumann.step C (regularSum e z) := by
  rw [stepExpression,regularSum_append,regularSum_scale]
  simp only [regularSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    regular_identity,add_zero,AsymptoticCoerciveNeumann.step,sub_eq_add_neg]
  exact congrArg (fun T : RegularSpace →L[ℂ] RegularSpace => 1+T)
    (neg_smul (AsymptoticCoerciveNeumann.scale C:ℂ) (regularSum e z))

/-- The previously constructed inverse polynomial has an exact finite
branch expansion with the same scalar coefficients in both realizations. -/
theorem holomorphicSum_inversePolynomial (C : ℝ) (e : Expression) (n m : ℕ) :
    holomorphicSum (inversePolynomialExpression C e n) m=
      AsymptoticCoerciveNeumann.polynomial C (holomorphicSum e m) n := by
  rw [inversePolynomialExpression,holomorphicSum_scale,holomorphicSum_geometric,holomorphicSum_step]
  rfl

theorem regularSum_inversePolynomial (C : ℝ) (e : Expression) (n : ℕ) (z : ℍ) :
    regularSum (inversePolynomialExpression C e n) z=
      AsymptoticCoerciveNeumann.polynomial C (regularSum e z) n := by
  rw [inversePolynomialExpression,regularSum_scale,regularSum_geometric,regularSum_step]
  rfl

#print axioms holomorphicSum_power
#print axioms regularSum_power
#print axioms holomorphicSum_geometric
#print axioms regularSum_geometric
#print axioms holomorphicSum_inversePolynomial
#print axioms regularSum_inversePolynomial

end AsymptoticFiniteBranch
