module

public import QuantitativeEulerEndpointNormalizedExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointWeightedExpression
open AsymptoticFiniteBranch QuantitativeHolomorphic UpperHalfPlane
open scoped Classical

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def restrictedGram (u : Expression) (E : κ → Expression) : Expression :=
  gramExpression (fun j => composeExpression (E j) u)

def weightedGram (u : Expression) (E : ι → κ → Expression) (w : ι → ℝ) (c : ℝ) : Expression :=
  scaleExpression (c:ℂ) (sumExpressions Finset.univ
    (fun i => scaleExpression (w i:ℂ) (restrictedGram u (E i))))

theorem regular_restrictedGram (u : Expression) (E : κ → Expression) (x : ℍ) :
    regularSum (restrictedGram u E) x=∑ j,
      star (regularSum (E j) x*regularSum u x)*(regularSum (E j) x*regularSum u x) := by
  rw [restrictedGram,regularSum_gramExpression]
  apply Finset.sum_congr rfl
  intro j _
  rw [regularSum_compose]
  rfl

theorem holomorphic_restrictedGram (u : Expression) (E : κ → Expression) (m : ℕ) :
    holomorphicSum (restrictedGram u E) m=∑ j,
      star (holomorphicSum (E j) m*holomorphicSum u m)*(holomorphicSum (E j) m*holomorphicSum u m) := by
  rw [restrictedGram,holomorphicSum_gramExpression]
  apply Finset.sum_congr rfl
  intro j _
  rw [holomorphicSum_compose]
  rfl

theorem regular_weightedGram (u : Expression) (E : ι → κ → Expression) (w : ι → ℝ) (c : ℝ) (x : ℍ) :
    regularSum (weightedGram u E w c) x=c • ∑ i,w i • (∑ j,
      star (regularSum (E i j) x*regularSum u x)*(regularSum (E i j) x*regularSum u x)) := by
  have hr (r : ℝ) (T : RegularSpace →L[ℂ] RegularSpace) : (r:ℂ) • T=r • T :=
    (RCLike.real_smul_eq_coe_smul (K:=ℂ) r T).symm
  simp only [weightedGram,regularSum_scale,regularSum_sumExpressions,hr,regular_restrictedGram]

theorem holomorphic_weightedGram (u : Expression) (E : ι → κ → Expression) (w : ι → ℝ) (c : ℝ) (m : ℕ) :
    holomorphicSum (weightedGram u E w c) m=c • ∑ i,w i • (∑ j,
      star (holomorphicSum (E i j) m*holomorphicSum u m)*(holomorphicSum (E i j) m*holomorphicSum u m)) := by
  have hr (r : ℝ) (T : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space) : (r:ℂ) • T=r • T :=
    (RCLike.real_smul_eq_coe_smul (K:=ℂ) r T).symm
  simp only [weightedGram,holomorphicSum_scale,holomorphicSum_sumExpressions,hr,holomorphic_restrictedGram]

theorem weighted_mass (u : Expression) (E : ι → κ → Expression) (w : ι → ℝ) (c : ℝ) :
    expressionBound (weightedGram u E w c)=|c| *
      (∑ i, |w i| *(∑ j, (expressionBound (E i j)*expressionBound u)^2)) := by
  simp only [weightedGram,restrictedGram,gramExpression,expressionBound_scale,
    Complex.norm_real,Real.norm_eq_abs,expressionBound_sumExpressions,
    expressionBound_compose,expressionBound_adjoint,←pow_two]

theorem weighted_mass_le {u : Expression} {E : ι → κ → Expression} {w : ι → ℝ} {c : ℝ}
    (hc : 0≤c) (hw : ∀ i,0≤w i) (hu : expressionBound u≤1)
    (C : ι → κ → ℝ) (hE : ∀ i j,expressionBound (E i j)≤C i j) :
    expressionBound (weightedGram u E w c)≤c*(∑ i,w i*(∑ j,(C i j)^2)) := by
  rw [weighted_mass,abs_of_nonneg hc]
  apply mul_le_mul_of_nonneg_left _ hc
  apply Finset.sum_le_sum
  intro i _
  rw [abs_of_nonneg (hw i)]
  apply mul_le_mul_of_nonneg_left _ (hw i)
  apply Finset.sum_le_sum
  intro j _
  have hm := mul_le_mul (hE i j) hu (expressionBound_nonneg u) ((expressionBound_nonneg _).trans (hE i j))
  have he : expressionBound (E i j)*expressionBound u≤C i j := by simpa only [mul_one] using hm
  exact pow_le_pow_left₀ (mul_nonneg (expressionBound_nonneg _) (expressionBound_nonneg _)) he 2

theorem weighted_matrix {u : Expression} {E : ι → κ → Expression} {B : ℝ}
    (hB : 0≤B) (hu : ExpressionMatrixBound u 1) (hE : ∀ i j,ExpressionMatrixBound (E i j) B)
    (w : ι → ℝ) (c : ℝ) : ExpressionMatrixBound (weightedGram u E w c) (8*B^2) := by
  apply ExpressionMatrixBound.scale
  apply expressionMatrixBound_sum
  intro i _
  apply ExpressionMatrixBound.scale
  apply expressionMatrixBound_sum
  intro j _
  have h := (hE i j).compose hu (by norm_num)
  have hh := h.adjoint.compose h (by positivity)
  convert hh using 1
  ring

#print axioms regular_weightedGram
#print axioms holomorphic_weightedGram
#print axioms weighted_mass_le
#print axioms weighted_matrix
end QuantitativeEulerEndpointWeightedExpression
