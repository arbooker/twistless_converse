module

public import QuantitativeMaassCrossExpressionPairingV1
public import QuantitativeMaassCrossCompactBranchV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticFiniteBranch
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

/-- On genuine source seeds, the cross-quotient sandwich equals the
explicit finite local branch expression. Every intermediate congruence
translate and both compact cutoff coefficients are retained. -/
theorem crossQuotientLocalization_finite_expression_pairing (N M : ℕ)
    (K L : Set ℍ) (hK : IsCompact K) (hL : IsCompact L)
    (b₁ b₂ : SmoothUpperSeed) (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hbound₁ : ∀ z ∈ K, ‖upperFunction b₁.toFun z‖ ≤ B₁)
    (hbound₂ : ∀ z ∈ L, ‖upperFunction b₂.toFun z‖ ≤ B₂)
    (hb₁ : tsupport (upperFunction b₁.toFun) ⊆ K)
    (hb₂ : tsupport (upperFunction b₂.toFun) ⊆ L)
    (u v : SmoothUpperSeed) (E : Expression)
    (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) (hA : QuotientRealizes N E A) :
    let E' := CrossCompactBranch.localExpression N K L hK hL
      (upperFunction b₁.toFun) (upperFunction b₂.toFun)
      (upperFunction_continuous b₁.smooth).measurable
      (upperFunction_continuous b₂.smooth).measurable B₁ B₂ hB₁ hB₂
      (CrossCompactBranch.cutoff_global_bound _ K hb₁ B₁ hB₁ hbound₁)
      (CrossCompactBranch.cutoff_global_bound _ L hb₂ B₂ hB₂ hbound₂) E
    inner ℂ
      (crossQuotientLocalization N M K hK b₁ hbound₁ (poincareSeedVector M u))
      (A (crossQuotientLocalization N M L hL b₂ hbound₂ (poincareSeedVector M v))) =
      ∫ z in K, star (poincareSum (G := gamma M) (upperFunction u.toFun) z) *
        expressionFunction E' (poincareSum (G := gamma M) (upperFunction v.toFun)) z := by
  intro E'
  rw [crossQuotientLocalization_expression_pairing N M K L hK hL b₁ b₂
    hbound₁ hbound₂ hb₁ hb₂ u v E A hA]
  have hcomm : (fun w => poincareSum (G := gamma M) (upperFunction v.toFun) w *
      upperFunction b₂.toFun w) =
      fun w => upperFunction b₂.toFun w * poincareSum (G := gamma M) (upperFunction v.toFun) w := by
    funext w
    ring
  rw [hcomm]
  apply setIntegral_congr_fun hK.measurableSet
  intro z _
  have he := CrossCompactBranch.expression_expansion N K L hK hL
    (upperFunction b₁.toFun) (upperFunction b₂.toFun)
    (upperFunction_continuous b₁.smooth).measurable
    (upperFunction_continuous b₂.smooth).measurable hb₁ hb₂ B₁ B₂ hB₁ hB₂
    (CrossCompactBranch.cutoff_global_bound _ K hb₁ B₁ hB₁ hbound₁)
    (CrossCompactBranch.cutoff_global_bound _ L hb₂ B₂ hB₂ hbound₂) E
    (poincareSum (G := gamma M) (upperFunction v.toFun)) z
  change _ = star (poincareSum (G := gamma M) (upperFunction u.toFun) z) *
    expressionFunction E' (poincareSum (G := gamma M) (upperFunction v.toFun)) z
  dsimp only
  rw [← he, star_mul]
  ring

#print axioms crossQuotientLocalization_finite_expression_pairing

end QuantitativeMaass
