module

public import QuantitativeEulerEndpointNestedCostV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointNestedExpression
open AsymptoticFiniteBranch QuantitativeHolomorphic Polynomial
open QuantitativeEulerEndpointUpdateExpression QuantitativeEulerEndpointExpressionGrowth

/-- Only the blocks strictly before the requested horizon enter this bound. -/
theorem bounds_upto (u initial : Expression) (g : ℕ → Expression) (L : ℕ → ℕ) (q : ℕ → ℝ[X])
    {B : ℝ} (hB : 16≤B) (hu : expressionBound u≤1) (huM : ExpressionMatrixBound u 1)
    (hi : expressionBound initial≤B) (hiM : ExpressionMatrixBound initial B) (n : ℕ)
    (hg : ∀ j<n,expressionBound (g j)≤B) (hgM : ∀ j<n,ExpressionMatrixBound (g j) B)
    (hq : ∀ j<n,(∑ i∈(q j).support, |(q j).coeff i|)≤B) :
    expressionBound (expression u initial g L q n)≤B^(budget L q n) ∧
    ExpressionMatrixBound (expression u initial g L q n) (B^(budget L q n)) := by
  induction n with
  | zero => simpa only [expression,budget,pow_one] using And.intro hi hiM
  | succ n ih =>
    have hh := ih (fun j hj => hg j (by omega))
      (fun j hj => hgM j (by omega)) (fun j hj => hq j (by omega))
    exact sharpened_common_bound hB (budget_pos L q n) hu huM
      hh.1 hh.2 (hg n (by omega)) (hgM n (by omega)) (L n) (q n) (hq n (by omega))

theorem bounds_double_exp_upto (u initial : Expression) (g : ℕ → Expression)
    (L : ℕ → ℕ) (q : ℕ → ℝ[X]) {B a b : ℝ} (hB : 16≤B)
    (hu : expressionBound u≤1) (huM : ExpressionMatrixBound u 1)
    (hi : expressionBound initial≤B) (hiM : ExpressionMatrixBound initial B) (n : ℕ)
    (hg : ∀ j<n,expressionBound (g j)≤B) (hgM : ∀ j<n,ExpressionMatrixBound (g j) B)
    (hq : ∀ j<n,(∑ i∈(q j).support, |(q j).coeff i|)≤B)
    (ha : (∑ j∈Finset.range n,logarithmicCost L q j)≤a) (hb : Real.log B≤Real.exp b) :
    expressionBound (expression u initial g L q n)≤Real.exp (Real.exp (a+b)) ∧
    ExpressionMatrixBound (expression u initial g L q n) (Real.exp (Real.exp (a+b))) := by
  have h := bounds_upto u initial g L q hB hu huM hi hiM n hg hgM hq
  have hp := power_budget_le L q n (show 1≤B by linarith) ha hb
  exact ⟨h.1.trans hp,h.2.mono hp⟩

open UpperHalfPlane MeasureTheory QuantitativeEulerEndpointRegularBase
open QuantitativeEulerEndpointBandExpression
variable {ε : ℝ} (hε : 0<ε) (H : ℝ)
local notation "s₀" => region (QuantitativeEulerEndpointBandCorner.ambient (ε:=ε) H)
local notation "hs₀" => region_measurable (QuantitativeEulerEndpointBandCorner.ambient_compact hε H)
local notation "p" => QuantitativeEulerEndpointBandCorner.projection hε H
local notation "hp" => QuantitativeEulerEndpointBandCorner.projection_isStarProjection hε H
local notation "𝔄" => QuantitativeEulerEndpointSubcorner.Subcorner action_measurable s₀ hs₀ p hp
local notation "ρ" => QuantitativeEulerEndpointSubcorner.representation action_measurable s₀ hs₀ p hp

/-- The original finite recurrence suffices for exact regular realization. -/
theorem regular_iteration_upto (F G : ℕ → 𝔄) (initial : Expression) (g : ℕ → Expression)
    (L : ℕ → ℕ) (q : ℕ → ℝ[X])
    (hi : ∀ x : Base,regularSum initial x=ρ (F 0) x) (n : ℕ)
    (hg : ∀ j<n,∀ x : Base,regularSum (g j) x=ρ (G j) x)
    (hF : ∀ j<n,F (j+1)=aeval (QuantitativeEulerEndpointSoftUpdate.update (F j) (F j*G j*F j) (L j)) (q j))
    (x : Base) :
    regularSum (expression (unitExpression ε H) initial g L q n) x=ρ (F n) x := by
  induction n generalizing x with
  | zero => exact hi x
  | succ n ih =>
    rw [expression,hF n (by omega)]
    exact regular_sharpened_representation hε H (F n) (G n)
      (expression (unitExpression ε H) initial g L q n) (g n)
      (fun x => ih (fun j hj => hg j (by omega)) (fun j hj => hF j (by omega)) x)
      (hg n (by omega)) (L n) (q n) x

#print axioms bounds_upto
#print axioms bounds_double_exp_upto
#print axioms regular_iteration_upto
end QuantitativeEulerEndpointNestedExpression
