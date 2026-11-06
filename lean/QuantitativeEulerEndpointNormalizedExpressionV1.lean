module

public import QuantitativeEulerEndpointBandExpressionV1
public import QuantitativeEulerEndpointNormalizedRowsV1
public import AsymptoticFiniteBranchNormalV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointNormalizedExpression
open AsymptoticFiniteBranch QuantitativeHolomorphic UpperHalfPlane
open QuantitativeEulerEndpointBlockNormalization
open scoped Classical

def row (u : Expression) (E : ℕ → Expression) (C : ℕ → ℝ) (n i : ℕ) : Expression :=
  scaleExpression ((factor C n:ℝ):ℂ) (composeExpression (E i) u)

def gram (u : Expression) (E : ℕ → Expression) (C : ℕ → ℝ) (n : ℕ) : Expression :=
  gramExpression (fun i : Fin n => row u E C n i)

theorem regular_row (u : Expression) (E : ℕ → Expression) (C : ℕ → ℝ)
    (n i : ℕ) (x : ℍ) :
    regularSum (row u E C n i) x=((factor C n:ℝ):ℂ) • (regularSum (E i) x*regularSum u x) := by
  rw [row,regularSum_scale,regularSum_compose]
  rfl

theorem holomorphic_row (u : Expression) (E : ℕ → Expression) (C : ℕ → ℝ)
    (n i m : ℕ) :
    holomorphicSum (row u E C n i) m=((factor C n:ℝ):ℂ) • (holomorphicSum (E i) m*holomorphicSum u m) := by
  rw [row,holomorphicSum_scale,holomorphicSum_compose]
  rfl

theorem regular_gram (u : Expression) (E : ℕ → Expression) (C : ℕ → ℝ)
    (n : ℕ) (x : ℍ) :
    regularSum (gram u E C n) x=∑ i : Fin n,
      star (((factor C n:ℝ):ℂ) • (regularSum (E i) x*regularSum u x))*
        (((factor C n:ℝ):ℂ) • (regularSum (E i) x*regularSum u x)) := by
  rw [gram,regularSum_gramExpression]
  apply Finset.sum_congr rfl
  intro i _
  rw [regular_row]
  rfl

theorem holomorphic_gram (u : Expression) (E : ℕ → Expression) (C : ℕ → ℝ)
    (n m : ℕ) :
    holomorphicSum (gram u E C n) m=∑ i : Fin n,
      star (((factor C n:ℝ):ℂ) • (holomorphicSum (E i) m*holomorphicSum u m))*
        (((factor C n:ℝ):ℂ) • (holomorphicSum (E i) m*holomorphicSum u m)) := by
  rw [gram,holomorphicSum_gramExpression]
  apply Finset.sum_congr rfl
  intro i _
  rw [holomorphic_row]
  rfl

theorem row_mass {u : Expression} {E : ℕ → Expression} {C : ℕ → ℝ}
    (hu : expressionBound u≤1) (n i : ℕ) (hE : expressionBound (E i)≤C i) :
    expressionBound (row u E C n i)≤factor C n*C i := by
  rw [row,expressionBound_scale,expressionBound_compose,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (factor_pos C n)]
  have hm := mul_le_mul hE hu (expressionBound_nonneg _) ((expressionBound_nonneg _).trans hE)
  exact mul_le_mul_of_nonneg_left (by simpa only [row,mul_one] using hm) (factor_pos C n).le

/-- Normalizing with actual expression-mass bounds also bounds the full
coefficient mass of the Gram by one, independently of the row count. -/
theorem gram_mass {u : Expression} {E : ℕ → Expression} {C : ℕ → ℝ}
    (hu : expressionBound u≤1) (n : ℕ) (hE : ∀ i : Fin n,expressionBound (E i)≤C i) :
    expressionBound (gram u E C n)≤1 := by
  rw [gram,gramExpression,expressionBound_sumExpressions]
  apply le_trans _ (normalized_square_sum C n)
  apply Finset.sum_le_sum
  intro i _
  rw [expressionBound_compose,expressionBound_adjoint,←pow_two]
  exact pow_le_pow_left₀ (expressionBound_nonneg _) (row_mass hu n i (hE i)) 2

theorem row_matrix {u : Expression} {E : ℕ → Expression} {C : ℕ → ℝ}
    {B : ℝ} (hu : ExpressionMatrixBound u 1) (n i : ℕ) (hE : ExpressionMatrixBound (E i) B) :
    ExpressionMatrixBound (row u E C n i) (2*B) := by
  have h := (hE.compose hu (by norm_num)).scale ((factor C n:ℝ):ℂ)
  simpa only [row,mul_one] using h

theorem gram_matrix {u : Expression} {E : ℕ → Expression} {C : ℕ → ℝ}
    {B : ℝ} (hB : 0≤B) (hu : ExpressionMatrixBound u 1) (n : ℕ)
    (hE : ∀ i : Fin n,ExpressionMatrixBound (E i) B) :
    ExpressionMatrixBound (gram u E C n) (8*B^2) := by
  apply expressionMatrixBound_sum
  intro i _
  have h := row_matrix (C:=C) hu n i (hE i)
  have hh := h.adjoint.compose h (by positivity)
  convert hh using 1
  ring

#print axioms regular_gram
#print axioms holomorphic_gram
#print axioms gram_mass
#print axioms gram_matrix
end QuantitativeEulerEndpointNormalizedExpression
