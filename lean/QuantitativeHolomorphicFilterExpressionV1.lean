module

public import QuantitativeHolomorphicFilterStabilityV1
public import QuantitativeHolomorphicExpressionV1
public import AsymptoticFiniteBranchSumsV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open ContinuousLinearMap AsymptoticFiniteBranch

variable {ι : Type*}

/-- Literal finite sum of observation Gram branches. -/
def observationGramExpression (qs : Finset ι) (rows : ι → Expression) (v : Expression) : Expression :=
  sumExpressions qs (fun i => composeExpression
    (adjointExpression (composeExpression (rows i) v)) (composeExpression (rows i) v))

/-- The ambient single global filter, with the terminal coordinate complement
removed by its two reconstruction factors. -/
def observationFilterExpression (qs : Finset ι) (rows : ι → Expression) (v : Expression)
    (b : ι → ℝ) (d : ℕ) : Expression :=
  composeExpression v (composeExpression
    (powerExpression ([identity] ++ scaleExpression (-(((finiteRowBound qs b)⁻¹ : ℝ) : ℂ))
      (observationGramExpression qs rows v)) d) (adjointExpression v))

theorem holomorphicSum_observationGramExpression (qs : Finset ι) (rows : ι → Expression)
    (v : Expression) (m : ℕ) :
    holomorphicSum (observationGramExpression qs rows v) m =
      finiteRowGram qs (fun i => holomorphicSum (rows i) m) (holomorphicSum v m) := by
  simp only [observationGramExpression, holomorphicSum_sumExpressions,
    holomorphicSum_compose, holomorphicSum_adjoint, finiteRowGram]

theorem regularSum_observationGramExpression (qs : Finset ι) (rows : ι → Expression)
    (v : Expression) (z : UpperHalfPlane) :
    regularSum (observationGramExpression qs rows v) z =
      finiteRowGram qs (fun i => regularSum (rows i) z) (regularSum v z) := by
  simp only [observationGramExpression, regularSum_sumExpressions,
    regularSum_compose, regularSum_adjoint, finiteRowGram]

private theorem real_filter_step {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (a : ℝ) (T : E →L[ℂ] E) :
    1 + (-(a : ℂ)) • T = 1 - a • T := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) a T]
  simp only [neg_smul, sub_eq_add_neg]
  rfl

theorem holomorphicSum_observationFilterExpression (qs : Finset ι) (rows : ι → Expression)
    (v : Expression) (b : ι → ℝ) (d m : ℕ) :
    holomorphicSum (observationFilterExpression qs rows v b d) m =
      (holomorphicSum v m).comp
        ((finiteRowFilter qs (fun i => holomorphicSum (rows i) m) b (holomorphicSum v m) d).comp
          (holomorphicSum v m).adjoint) := by
  simp only [observationFilterExpression, holomorphicSum_compose, holomorphicSum_power,
    holomorphicSum_append, holomorphicSum_scale, holomorphicSum_observationGramExpression,
    holomorphicSum_adjoint, finiteRowFilter]
  have hid : holomorphicSum [identity] m = 1 := by simp [holomorphicSum, holomorphic_identity]
  rw [hid, real_filter_step]

theorem regularSum_observationFilterExpression (qs : Finset ι) (rows : ι → Expression)
    (v : Expression) (b : ι → ℝ) (d : ℕ) (z : UpperHalfPlane) :
    regularSum (observationFilterExpression qs rows v b d) z =
      (regularSum v z).comp
        ((finiteRowFilter qs (fun i => regularSum (rows i) z) b (regularSum v z) d).comp
          (regularSum v z).adjoint) := by
  simp only [observationFilterExpression, regularSum_compose, regularSum_power,
    regularSum_append, regularSum_scale, regularSum_observationGramExpression,
    regularSum_adjoint, finiteRowFilter]
  have hid : regularSum [identity] z = 1 := by simp [regularSum, regular_identity]
  rw [hid]
  exact congrArg (fun T : RegularSpace →L[ℂ] RegularSpace =>
    (regularSum v z).comp ((T ^ d).comp (regularSum v z).adjoint))
    (real_filter_step (finiteRowBound qs b)⁻¹
      (finiteRowGram qs (fun i => regularSum (rows i) z) (regularSum v z)))

theorem expressionBound_sumExpressions (qs : Finset ι) (f : ι → Expression) :
    expressionBound (sumExpressions qs f) = ∑ i ∈ qs, expressionBound (f i) := by
  have h (l : List ι) : expressionBound (l.flatMap f) =
      (l.map (fun i => expressionBound (f i))).sum := by
    induction l with
    | nil => rfl
    | cons i l ih =>
      simp only [List.flatMap_cons, expressionBound_append, List.map_cons, List.sum_cons, ih]
  exact (h qs.toList).trans (Finset.sum_map_toList _ _)

theorem length_sumExpressions (qs : Finset ι) (f : ι → Expression) :
    (sumExpressions qs f).length = ∑ i ∈ qs, (f i).length := by
  simp only [sumExpressions, List.length_flatMap]
  exact Finset.sum_map_toList _ _

theorem observationGramExpression_complexity (qs : Finset ι) (rows : ι → Expression) (v : Expression) :
    expressionBound (observationGramExpression qs rows v) =
      ∑ i ∈ qs, (expressionBound (rows i) * expressionBound v) ^ 2 ∧
    (observationGramExpression qs rows v).length =
      ∑ i ∈ qs, ((rows i).length * v.length) ^ 2 := by
  constructor
  · simp only [observationGramExpression, expressionBound_sumExpressions,
      expressionBound_compose, expressionBound_adjoint, pow_two]
  · simp only [observationGramExpression, length_sumExpressions, length_composeExpression,
      adjointExpression, List.length_map, pow_two]

theorem observationFilterExpression_complexity (qs : Finset ι) (rows : ι → Expression)
    (v : Expression) (b : ι → ℝ) (d : ℕ) :
    expressionBound (observationFilterExpression qs rows v b d) =
      expressionBound v ^ 2 * (1 + (finiteRowBound qs b)⁻¹ *
        ∑ i ∈ qs, (expressionBound (rows i) * expressionBound v) ^ 2) ^ d ∧
    (observationFilterExpression qs rows v b d).length =
      v.length ^ 2 * (1 + ∑ i ∈ qs, ((rows i).length * v.length) ^ 2) ^ d := by
  have hc := single_filter_expression_complexity (observationGramExpression qs rows v)
    (((finiteRowBound qs b)⁻¹ : ℝ) : ℂ) d
  have hg := observationGramExpression_complexity qs rows v
  constructor
  · rw [observationFilterExpression, expressionBound_compose, expressionBound_compose,
      expressionBound_adjoint, hc.2, hg.1]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (finiteRowBound_pos qs b))]
    ring
  · rw [observationFilterExpression, length_composeExpression, length_composeExpression,
      hc.1, hg.2]
    simp only [adjointExpression, List.length_map]
    ring

#print axioms holomorphicSum_observationFilterExpression
#print axioms regularSum_observationFilterExpression
#print axioms observationFilterExpression_complexity

end QuantitativeHolomorphic
