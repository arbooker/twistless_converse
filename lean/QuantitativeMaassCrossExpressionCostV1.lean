module

public import QuantitativeMaassCrossCompactComplexityV1
public import QuantitativeMaassIntegralMatrixMotionV1
public import QuantitativeMaassBranchIdentityCoefficientV1
public import QuantitativeMaassGeometricGrowthV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set UpperHalfPlane AsymptoticFiniteBranch QuantitativeHolomorphic
namespace QuantitativeMaass.CrossCompactBranch

/-- An exponential bound on an actual integer representative gives a
linear displacement bound. No representative is replaced by an uncontrolled
projectively equivalent matrix. -/
theorem expression_exponential_motion (E : Expression) (X : ℝ) (hX : 0 ≤ X)
    (hE : ExpressionMatrixBound E (Real.exp X)) (o : ℍ) :
    ∀ q ∈ E, dist (q.label • o) o ≤ 2*(X+(‖(o:ℂ)‖+1)^2/o.im) := by
  intro q hq
  obtain ⟨M,hM,hMB⟩ := hE q hq
  obtain ⟨hpos,_⟩ := integerAction_positive_real hM
  have hact : positiveIntegralGL M hpos • o = q.label • o := by
    apply UpperHalfPlane.ext
    rw [positiveIntegralGL_fractional,hM.2]
  have hd := positiveIntegralGL_dist_log_bound M hpos (Real.exp X)
    (Real.exp_pos _).le hMB o
  rw [hact] at hd
  let c := (‖(o:ℂ)‖+1)^2/o.im
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have he : 1 ≤ Real.exp X := Real.one_le_exp_iff.mpr hX
  have hlog : Real.log (1+Real.exp X*c) ≤ X+c := by
    calc
      _ ≤ Real.log (Real.exp X*(1+c)) :=
        Real.log_le_log (by positivity) (by nlinarith)
      _ = X+Real.log (1+c) := by
        rw [Real.log_mul (Real.exp_ne_zero _) (by positivity),Real.log_exp]
      _ ≤ X+c := by linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < 1+c)]
  apply hd.trans
  change 2*Real.log (1+Real.exp X*(‖(o:ℂ)‖+1)^2/o.im) ≤ _
  rw [show Real.exp X*(‖(o:ℂ)‖+1)^2/o.im = Real.exp X*c by dsimp only [c]; ring]
  exact mul_le_mul_of_nonneg_left hlog (by norm_num)

/-- The actual localized expression, including its congruence overlaps,
has exponential coefficient and matrix costs in the original exponent and
the two spatial radii. The multiplicative constant precedes all these data. -/
theorem localExpression_exponential_cost (o : ℍ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (K L : Set ℍ)
      (hK : IsCompact K) (hL : IsCompact L)
      (b₁ b₂ : ℍ → ℂ) (hb₁ : Measurable b₁) (hb₂ : Measurable b₂)
      (hbound₁ : ∀ x, ‖b₁ x‖ ≤ 1) (hbound₂ : ∀ x, ‖b₂ x‖ ≤ 1)
      (E : Expression) (R S X : ℝ),
      0 ≤ R → 0 ≤ S → 0 ≤ X →
      K ⊆ Metric.closedBall o R → L ⊆ Metric.closedBall o S →
      expressionBound E ≤ Real.exp X → ExpressionMatrixBound E (Real.exp X) →
      let F := localExpression N K L hK hL b₁ b₂ hb₁ hb₂
        1 1 zero_le_one zero_le_one hbound₁ hbound₂ E
      expressionBound F ≤ A*Real.exp (4*R+4*S+9*X+8*((‖(o:ℂ)‖+1)^2/o.im)) ∧
      ExpressionMatrixBound F
        (2*Real.exp ((R+S)/2+2*X+(‖(o:ℂ)‖+1)^2/o.im+dist o I)) := by
  obtain ⟨A,hA,hAb⟩ := energyMultiplicity_exp o
  refine ⟨A,hA,?_⟩
  intro N K L hK hL b₁ b₂ hb₁ hb₂ hb₁' hb₂' E R S X hR hS hX hKR hLS he hE F
  let c := (‖(o:ℂ)‖+1)^2/o.im
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hm := expression_exponential_motion E X hX hE o
  constructor
  · have hh := localExpression_coefficient_bound N K L hK hL b₁ b₂ hb₁ hb₂
      1 1 zero_le_one zero_le_one hb₁' hb₂' E o R S (2*(X+c)) hKR hLS hm
    simp only [one_mul,mul_one] at hh
    apply hh.trans
    calc
      _ ≤ (A*Real.exp (4*(R+2*(X+c)+S)))*Real.exp X :=
        mul_le_mul (hAb _ (by positivity)) he (expressionBound_nonneg E) (by positivity)
      _ = _ := by
        rw [mul_assoc,←Real.exp_add]
        congr 2
        dsimp only [c]
        ring
  · have hh := localExpression_matrix_bound N K L hK hL b₁ b₂ hb₁ hb₂
      1 1 zero_le_one zero_le_one hb₁' hb₂' E o R S (2*(X+c)) (Real.exp X) hKR hLS hm hE
    convert hh using 1
    rw [mul_assoc,←Real.exp_add]
    congr 2
    dsimp only [c]
    ring

#print axioms expression_exponential_motion
#print axioms localExpression_exponential_cost

end QuantitativeMaass.CrossCompactBranch
