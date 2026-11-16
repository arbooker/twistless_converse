module

public import QuantitativeMaassCrossExpressionCostV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Set UpperHalfPlane AsymptoticFiniteBranch QuantitativeHolomorphic
namespace QuantitativeMaass.CrossCompactBranch

/-- One fixed exponent controls both costs of every compact localized
expression. It is chosen before the level, cutoffs, radii and expression. -/
theorem localExpression_uniform_exponent (o : ℍ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) (K L : Set ℍ)
      (hK : IsCompact K) (hL : IsCompact L)
      (b₁ b₂ : ℍ → ℂ) (hb₁ : Measurable b₁) (hb₂ : Measurable b₂)
      (hbound₁ : ∀ x, ‖b₁ x‖ ≤ 1) (hbound₂ : ∀ x, ‖b₂ x‖ ≤ 1)
      (E : Expression) (R S X : ℝ),
      0 ≤ R → 0 ≤ S → 0 ≤ X →
      K ⊆ Metric.closedBall o R → L ⊆ Metric.closedBall o S →
      expressionBound E ≤ Real.exp X → ExpressionMatrixBound E (Real.exp X) →
      let F := localExpression N K L hK hL b₁ b₂ hb₁ hb₂
        1 1 zero_le_one zero_le_one hbound₁ hbound₂ E
      expressionBound F ≤ Real.exp (C*(R+S+X+1)) ∧
      ExpressionMatrixBound F (Real.exp (C*(R+S+X+1))) := by
  obtain ⟨A,hA,hcost⟩ := localExpression_exponential_cost o
  let c := (‖(o:ℂ)‖+1)^2/o.im
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  let C := A+10+8*c+2*dist o I
  have hd : 0 ≤ dist o I := dist_nonneg
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  have hC9 : 9 ≤ C := by dsimp only [C]; linarith
  have hCA : A+8*c ≤ C := by dsimp only [C]; linarith
  have hCc : c+dist o I+1 ≤ C := by dsimp only [C]; linarith
  refine ⟨C,hC,?_⟩
  intro N K L hK hL b₁ b₂ hb₁ hb₂ hb₁' hb₂' E R S X hR hS hX hKR hLS he hE F
  have hh := hcost N K L hK hL b₁ b₂ hb₁ hb₂ hb₁' hb₂' E R S X
    hR hS hX hKR hLS he hE
  have hlinear : 9*(R+S+X) ≤ C*(R+S+X) :=
    mul_le_mul_of_nonneg_right hC9 (by positivity)
  constructor
  · apply hh.1.trans
    calc
      _ ≤ Real.exp A*Real.exp (4*R+4*S+9*X+8*c) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        linarith [Real.add_one_le_exp A]
      _ = Real.exp (A+(4*R+4*S+9*X+8*c)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  · apply hh.2.mono
    calc
      _ ≤ Real.exp 1*Real.exp ((R+S)/2+2*X+c+dist o I) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        linarith [Real.add_one_le_exp (1:ℝ)]
      _ = Real.exp (1+((R+S)/2+2*X+c+dist o I)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

#print axioms localExpression_uniform_exponent

end QuantitativeMaass.CrossCompactBranch
