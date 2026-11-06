module

public import QuantitativeEulerEndpointExpressionGrowthV1
public import QuantitativeEulerEndpointBandUpdateV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointNestedExpression
open AsymptoticFiniteBranch QuantitativeHolomorphic Polynomial
open QuantitativeEulerEndpointUpdateExpression QuantitativeEulerEndpointExpressionGrowth

def expression (u initial : Expression) (g : ℕ → Expression) (L : ℕ → ℕ) (q : ℕ → ℝ[X]) : ℕ → Expression
  | 0 => initial
  | n+1 => sharpenedExpression u (expression u initial g L q n) (g n) (L n) (q n)

def budget (L : ℕ → ℕ) (q : ℕ → ℝ[X]) : ℕ → ℕ
  | 0 => 1
  | n+1 => stepExponent (budget L q n) (L n) (q n).natDegree

theorem budget_pos (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (n : ℕ) : 1≤budget L q n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [budget,stepExponent]
    have h : 0<8*((q n).natDegree+1)*(L n+1) := by positivity
    exact Nat.mul_le_mul (show 1≤8*((q n).natDegree+1)*(L n+1) by omega) ih

theorem budget_product (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (n : ℕ) :
    budget L q n=∏ i∈Finset.range n, 8*((q i).natDegree+1)*(L i+1) := by
  induction n with
  | zero => simp [budget]
  | succ n ih => rw [budget,stepExponent,ih,Finset.prod_range_succ]; ring

theorem bounds (u initial : Expression) (g : ℕ → Expression) (L : ℕ → ℕ) (q : ℕ → ℝ[X])
    {B : ℝ} (hB : 16≤B) (hu : expressionBound u≤1) (huM : ExpressionMatrixBound u 1)
    (hi : expressionBound initial≤B) (hiM : ExpressionMatrixBound initial B)
    (hg : ∀ j,expressionBound (g j)≤B) (hgM : ∀ j,ExpressionMatrixBound (g j) B)
    (hq : ∀ j,(∑ i∈(q j).support, |(q j).coeff i|)≤B) (n : ℕ) :
    expressionBound (expression u initial g L q n)≤B^(budget L q n) ∧
    ExpressionMatrixBound (expression u initial g L q n) (B^(budget L q n)) := by
  induction n with
  | zero => simpa only [expression,budget,pow_one] using And.intro hi hiM
  | succ n ih =>
    exact sharpened_common_bound hB (budget_pos L q n) hu huM
      ih.1 ih.2 (hg n) (hgM n) (L n) (q n) (hq n)

open UpperHalfPlane MeasureTheory QuantitativeEulerEndpointRegularBase
open QuantitativeEulerEndpointBandExpression
variable {ε : ℝ} (hε : 0<ε) (H : ℝ)
local notation "s₀" => region (QuantitativeEulerEndpointBandCorner.ambient (ε:=ε) H)
local notation "hs₀" => region_measurable (QuantitativeEulerEndpointBandCorner.ambient_compact hε H)
local notation "p" => QuantitativeEulerEndpointBandCorner.projection hε H
local notation "hp" => QuantitativeEulerEndpointBandCorner.projection_isStarProjection hε H
local notation "𝔄" => QuantitativeEulerEndpointSubcorner.Subcorner action_measurable s₀ hs₀ p hp
local notation "ρ" => QuantitativeEulerEndpointSubcorner.representation action_measurable s₀ hs₀ p hp

/-- The expression recursion realizes the original corner recursion exactly,
including every constant term of every sharpening polynomial. -/
theorem regular_iteration (F G : ℕ → 𝔄) (initial : Expression) (g : ℕ → Expression)
    (L : ℕ → ℕ) (q : ℕ → ℝ[X])
    (hi : ∀ x : Base,regularSum initial x=ρ (F 0) x)
    (hg : ∀ j,∀ x : Base,regularSum (g j) x=ρ (G j) x)
    (hF : ∀ j,F (j+1)=aeval (QuantitativeEulerEndpointSoftUpdate.update (F j) (F j*G j*F j) (L j)) (q j))
    (n : ℕ) (x : Base) :
    regularSum (expression (unitExpression ε H) initial g L q n) x=ρ (F n) x := by
  induction n generalizing x with
  | zero => exact hi x
  | succ n ih =>
    rw [expression,hF]
    exact regular_sharpened_representation hε H (F n) (G n)
      (expression (unitExpression ε H) initial g L q n) (g n) ih (hg n) (L n) (q n) x

#print axioms budget_product
#print axioms bounds
#print axioms regular_iteration
end QuantitativeEulerEndpointNestedExpression
