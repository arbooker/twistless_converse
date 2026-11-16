module

public import QuantitativeMaassCrossQuotientLocalizationV1
public import QuantitativeMaassQuotientExpressionBaseV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticFiniteBranch
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

/-- The exact local integral for a finite quotient expression between
two Poincare seeds. The expression acts on the full Poincare representative. -/
theorem poincareSeedVector_expression_pairing (N : ℕ) (K : Set ℍ)
    (hK : IsCompact K) (u v : SmoothUpperSeed)
    (hu : tsupport (upperFunction u.toFun) ⊆ K)
    (E : Expression) (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (hA : QuotientRealizes N E A) :
    inner ℂ (poincareSeedVector N u) (A (poincareSeedVector N v)) =
      ∫ z in K, star (upperFunction u.toFun z) *
        expressionFunction E (poincareSum (G := gamma N) (upperFunction v.toFun)) z := by
  obtain ⟨g, hg, eg⟩ := hA ⟨_, poincareSeed_representative N v⟩
  change AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) g =
    A (poincareSeedVector N v) at hg
  rw [← hg, ← quotientRestriction_test_integral N K hK hK.measurableSet u hu]
  apply integral_congr_ae
  filter_upwards [quotientRestriction_representative_ae N K hK hK.measurableSet g] with z hz
  rw [hz, eg]

/-- The literal cross-quotient sandwich retains both compact cutoffs and
the intermediate congruence Poincare sum. This is the dense-seed identity
needed before a finite-overlap branch expansion; no wave or cutoff is commuted. -/
theorem crossQuotientLocalization_expression_pairing (N M : ℕ)
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
      (A (crossQuotientLocalization N M L hL b₂ hB₂ (poincareSeedVector M v))) =
      ∫ z in K,
        star (poincareSum (G := gamma M) (upperFunction u.toFun) z * upperFunction b₁.toFun z) *
        expressionFunction E (poincareSum (G := gamma N)
          (fun w => poincareSum (G := gamma M) (upperFunction v.toFun) w * upperFunction b₂.toFun w)) z := by
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
  have hh := poincareSeedVector_expression_pairing N K hK U V hU E A hA
  rw [hUf, hVf] at hh
  exact hh

#print axioms poincareSeedVector_expression_pairing
#print axioms crossQuotientLocalization_expression_pairing

end QuantitativeMaass
