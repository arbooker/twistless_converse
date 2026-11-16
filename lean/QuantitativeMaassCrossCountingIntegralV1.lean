module

public import QuantitativeMaassCrossRegularIntegralV1
public import QuantitativeArithmeticMaassCountingExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane AsymptoticFiniteBranch
open AsymptoticCongruenceStrip AsymptoticRegularTrace AsymptoticNestedQuotients
open scoped lp
namespace QuantitativeMaass.CrossCompactBranch

/-- The regular main integral of the physical compact-transfer expression
is the root matrix coefficient of its actual counting realization, times
the displayed cutoff mass and spherical identity. -/
theorem localExpression_counting_integral (N : ℕ) (S : Set ℍ) (hS : IsCompact S)
    (b : ℍ → ℂ) (hb : Measurable b) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x, ‖b x‖ ≤ B) (E : Expression)
    (A : ℓ²(Classes (gamma N),ℂ) →L[ℂ] ℓ²(Classes (gamma N),ℂ))
    (hA : Counting.Realizes (gamma N) E A) (v : ℂ) :
    let F := localExpression N S S hS hS b b hb hb B B hB hB hbound hbound E
    (∫ x in S, (matrix (regularSum (composeExpression F [corner S hS.measurableSet]) x) 1 1*v).re) =
      (∫ x in S, ‖b x‖^2)*
        ((A (delta (classOf (gamma N) 1))) (classOf (gamma N) 1)*v).re := by
  apply localExpression_regular_integral_constant N S hS b hb B hB hbound E _ v
  intro x _
  exact (hA.root_coefficient x).symm

#print axioms localExpression_counting_integral

end QuantitativeMaass.CrossCompactBranch
