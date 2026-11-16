module

public import QuantitativeMaassCrossExpressionPairingV1
public import QuantitativeMaassReflectionOperatorV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticFiniteBranch
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

/-- The reflected quotient pairing evaluates the actual finite expression
at the reflected point. Reflection is retained explicitly. -/
theorem poincareSeedVector_reflected_expression_pairing (N : ℕ) (K : Set ℍ)
    (hK : IsCompact K) (u v : SmoothUpperSeed)
    (hu : tsupport (upperFunction u.toFun) ⊆ K)
    (E : Expression) (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (hA : QuotientRealizes N E A) :
    inner ℂ (poincareSeedVector N u) (reflectionIsometry N (A (poincareSeedVector N v))) =
      ∫ z in K, star (upperFunction u.toFun z) *
        expressionFunction E (poincareSum (G := gamma N) (upperFunction v.toFun)) (J•z) := by
  obtain ⟨g,hg,eg⟩ := hA ⟨_,poincareSeed_representative N v⟩
  change AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) g =
    A (poincareSeedVector N v) at hg
  rw [←hg,reflectionIsometry_apply,
    ←quotientRestriction_test_integral N K hK hK.measurableSet u hu]
  apply integral_congr_ae
  filter_upwards [quotientRestriction_representative_ae N K hK hK.measurableSet
    (reflectionRepresentative N g)] with z hz
  rw [hz]
  change star (upperFunction u.toFun z)*g.val (J•z) = _
  rw [eg]

/-- Exact reflected compact-transfer pairing, with both cutoffs in their
original positions and the intermediate congruence sum unaltered. -/
theorem crossQuotientLocalization_reflected_expression_pairing (N M : ℕ)
    (K L : Set ℍ) (hK : IsCompact K) (hL : IsCompact L)
    (b₁ b₂ : SmoothUpperSeed) {B₁ B₂ : ℝ}
    (hB₁ : ∀ z ∈ K, ‖upperFunction b₁.toFun z‖ ≤ B₁)
    (hB₂ : ∀ z ∈ L, ‖upperFunction b₂.toFun z‖ ≤ B₂)
    (hb₁ : tsupport (upperFunction b₁.toFun) ⊆ K)
    (hb₂ : tsupport (upperFunction b₂.toFun) ⊆ L)
    (u v : SmoothUpperSeed) (E : Expression)
    (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) (hA : QuotientRealizes N E A) :
    inner ℂ
      (crossQuotientLocalization N M K hK b₁ hB₁ (poincareSeedVector M u))
      (reflectionIsometry N
        (A (crossQuotientLocalization N M L hL b₂ hB₂ (poincareSeedVector M v)))) =
      ∫ z in K,
        star (poincareSum (G := gamma M) (upperFunction u.toFun) z * upperFunction b₁.toFun z) *
        expressionFunction E (poincareSum (G := gamma N)
          (fun w => poincareSum (G := gamma M) (upperFunction v.toFun) w * upperFunction b₂.toFun w)) (J•z) := by
  let U := b₁.localized (congruencePoincareCartesian M u.toFun)
    (congruencePoincareCartesian_smooth M u.smooth u.compact)
  let V := b₂.localized (congruencePoincareCartesian M v.toFun)
    (congruencePoincareCartesian_smooth M v.smooth v.compact)
  have hU : tsupport (upperFunction U.toFun) ⊆ K := tsupport_mul_subset_right.trans hb₁
  have hUf : upperFunction U.toFun = fun z =>
      poincareSum (G := gamma M) (upperFunction u.toFun) z * upperFunction b₁.toFun z := by
    funext z
    change upperFunction (congruencePoincareCartesian M u.toFun) z * upperFunction b₁.toFun z = _
    rw [congruencePoincareCartesian_represents]
  have hVf : upperFunction V.toFun = fun z =>
      poincareSum (G := gamma M) (upperFunction v.toFun) z * upperFunction b₂.toFun z := by
    funext z
    change upperFunction (congruencePoincareCartesian M v.toFun) z * upperFunction b₂.toFun z = _
    rw [congruencePoincareCartesian_represents]
  rw [crossQuotientLocalization_on_seed N M K hK b₁ hB₁ hb₁,
    crossQuotientLocalization_on_seed N M L hL b₂ hB₂ hb₂]
  have hh := poincareSeedVector_reflected_expression_pairing N K hK U V hU E A hA
  rw [hUf,hVf] at hh
  exact hh

#print axioms poincareSeedVector_reflected_expression_pairing
#print axioms crossQuotientLocalization_reflected_expression_pairing

end QuantitativeMaass
