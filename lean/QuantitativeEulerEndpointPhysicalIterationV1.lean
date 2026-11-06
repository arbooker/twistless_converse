module

public import QuantitativeEulerEndpointNestedFiniteV1
public import QuantitativeEulerEndpointPhysicalCornerV1
public import QuantitativeEulerEndpointPhysicalGramV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointNestedExpression
open AsymptoticFiniteBranch QuantitativeHolomorphic Polynomial
open QuantitativeEulerEndpointBandExpression QuantitativeEulerEndpointBernstein

/-- Physical positive contraction and support throughout the SAME finite
expression recursion. All Gram and scalar premises are finite-horizon. -/
theorem physical_iteration_order (ε H : ℝ) (initial : Expression) (g : ℕ → Expression)
    (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (n m : ℕ)
    (hi : let P := holomorphicSum (unitExpression ε H) m
      let A := holomorphicSum initial m
      0≤A ∧ A≤P ∧ P*A=A ∧ A*P=A)
    (hg : ∀ j<n,let P := holomorphicSum (unitExpression ε H) m
      let G := holomorphicSum (g j) m
      0≤G ∧ G≤1 ∧ P*G=G ∧ G*P=G)
    (hq : ∀ j<n,ScalarSharpening (q j)) :
    let P := holomorphicSum (unitExpression ε H) m
    let A := holomorphicSum (expression (unitExpression ε H) initial g L q n) m
    0≤A ∧ A≤holomorphicSum initial m ∧ A≤P ∧ P*A=A ∧ A*P=A := by
  induction n with
  | zero => exact ⟨hi.1,le_rfl,hi.2⟩
  | succ n ih =>
    have hprev := ih (fun j hj => hg j (by omega)) (fun j hj => hq j (by omega))
    have hgn := hg n (by omega)
    have hstep := QuantitativeEulerEndpointPhysicalCorner.sharpened_order
      (holomorphicSum (unitExpression ε H) m)
      (QuantitativeEulerEndpointPhysicalGram.unit_isStarProjection ε H m)
      (holomorphicSum (expression (unitExpression ε H) initial g L q n) m) (holomorphicSum (g n) m)
      hprev.2.2.2.1 hprev.2.2.2.2 hgn.2.2.1 hgn.2.2.2 hprev.1
      (hprev.2.2.1.trans (QuantitativeEulerEndpointPhysicalGram.unit_order ε H m).2)
      hgn.1 hgn.2.1 (L n) (hq n (by omega))
    dsimp only
    rw [expression,holomorphic_sharpened]
    exact ⟨hstep.1,hstep.2.1.trans hprev.2.1,hstep.2.1.trans hprev.2.2.1,hstep.2.2⟩

#print axioms physical_iteration_order
end QuantitativeEulerEndpointNestedExpression
