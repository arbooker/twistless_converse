module

public import QuantitativeMaassCrossLocalizedExpressionV1
public import QuantitativeMaassPhysicalExpressionV1
public import QuantitativeMaassCylinderPhysicalV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane AsymptoticFiniteBranch
open AsymptoticClassicalPetersson AsymptoticMassTransport AsymptoticCongruenceStrip
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

/-- For cutoff functions supported in the fundamental strip, the explicit local
expression has the same physical pairing after cylinder zero extension.
Both strip indicators are justified by the corresponding cutoff supports. -/
theorem cross_localExpression_physical_pairing (N : ℕ)
    (K L : Set ℍ) (hK : IsCompact K) (hL : IsCompact L)
    (b₁ b₂ : ℍ → ℂ) (hb₁ : Measurable b₁) (hb₂ : Measurable b₂)
    (hKS : Function.support b₁ ⊆ strip) (hLS : Function.support b₂ ⊆ strip)
    (hs₁ : tsupport b₁ ⊆ K) (hs₂ : tsupport b₂ ⊆ L)
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hbound₁ : ∀ x, ‖b₁ x‖ ≤ B₁) (hbound₂ : ∀ x, ‖b₂ x‖ ≤ B₂)
    (E : Expression) (f g : Lp ℂ 2 (quotientMeasure 0)) (φ ψ : ℍ → ℂ)
    (hf : (f : ℍ → ℂ) =ᵐ[quotientMeasure 0] φ)
    (hg : (g : ℍ → ℂ) =ᵐ[quotientMeasure 0] ψ) :
    let E' := CrossCompactBranch.localExpression N K L hK hL b₁ b₂ hb₁ hb₂
      B₁ B₂ hB₁ hB₂ hbound₁ hbound₂ E
    inner ℂ (cylinderZeroExtension f) (holomorphicSum E' 0 (cylinderZeroExtension g)) =
      ∫ z in K, star (φ z)*expressionFunction E' ψ z := by
  intro E'
  rw [physical_expression_pairing E' _ _ (strip.indicator φ) (strip.indicator ψ)
    (cylinderZeroExtension_coeFn_of_ae f φ hf)
    (cylinderZeroExtension_coeFn_of_ae g ψ hg)]
  have hfun : (fun y => b₂ y*strip.indicator ψ y) = fun y => b₂ y*ψ y := by
    funext y
    by_cases hy : y ∈ strip
    · rw [indicator_of_mem hy]
    · have hb : b₂ y=0 :=
        Classical.byContradiction (fun h => hy (hLS h))
      rw [hb,zero_mul,zero_mul]
  rw [← integral_indicator hK.measurableSet]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    have he := CrossCompactBranch.expression_expansion N K L hK hL
      b₁ b₂ hb₁ hb₂ hs₁ hs₂ B₁ B₂ hB₁ hB₂ hbound₁ hbound₂ E
      (strip.indicator ψ) z
    have he' := CrossCompactBranch.expression_expansion N K L hK hL
      b₁ b₂ hb₁ hb₂ hs₁ hs₂ B₁ B₂ hB₁ hB₂ hbound₁ hbound₂ E ψ z
    change star (strip.indicator φ z)*expressionFunction E' (strip.indicator ψ) z = _
    by_cases hz : z ∈ K
    · rw [indicator_of_mem hz]
      by_cases hzstrip : z ∈ strip
      · rw [indicator_of_mem hzstrip]
        rw [hfun] at he
        rw [← he,he']
      · have hb : b₁ z=0 := Classical.byContradiction (fun h => hzstrip (hKS h))
        rw [indicator_of_notMem hzstrip,star_zero,zero_mul]
        rw [hb,star_zero,zero_mul] at he'
        rw [← he',mul_zero]
    · rw [indicator_of_notMem hz]
      have hb : b₁ z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hs₁ h))
      rw [hb,star_zero,zero_mul] at he
      rw [← he,mul_zero])

/-- Exact physical realization of the compact-transfer sandwich on
genuine cylinder Poincare seeds. The intermediate congruence sum is the
finite local expression, with no wave action or spectral approximation. -/
theorem crossQuotientLocalization_physical_seed_pairing (N : ℕ)
    (K L : Set ℍ) (hK : IsCompact K) (hL : IsCompact L)
    (b₁ b₂ : SmoothUpperSeed)
    (hKS : Function.support (upperFunction b₁.toFun) ⊆ strip)
    (hLS : Function.support (upperFunction b₂.toFun) ⊆ strip)
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
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
      (crossQuotientLocalization N 0 K hK b₁ hbound₁ (poincareSeedVector 0 u))
      (A (crossQuotientLocalization N 0 L hL b₂ hbound₂ (poincareSeedVector 0 v))) =
      inner ℂ (cylinderZeroExtension (poincareSeedVector 0 u).val)
        (holomorphicSum E' 0 (cylinderZeroExtension (poincareSeedVector 0 v).val)) := by
  intro E'
  rw [crossQuotientLocalization_finite_expression_pairing N 0 K L hK hL
    b₁ b₂ B₁ B₂ hB₁ hB₂ hbound₁ hbound₂ hb₁ hb₂ u v E A hA]
  symm
  exact cross_localExpression_physical_pairing N K L hK hL
    (upperFunction b₁.toFun) (upperFunction b₂.toFun)
    (upperFunction_continuous b₁.smooth).measurable
    (upperFunction_continuous b₂.smooth).measurable hKS hLS hb₁ hb₂ B₁ B₂ hB₁ hB₂
    (CrossCompactBranch.cutoff_global_bound _ K hb₁ B₁ hB₁ hbound₁)
    (CrossCompactBranch.cutoff_global_bound _ L hb₂ B₂ hB₂ hbound₂) E
    (poincareSeedVector 0 u).val (poincareSeedVector 0 v).val _ _
    (poincareSeedVector_coeFn 0 u) (poincareSeedVector_coeFn 0 v)

/-- Density upgrades the literal seed identity to the completed
operator sandwich. No invariance of an individual rational branch is used. -/
theorem crossQuotientLocalization_physical_sandwich (N : ℕ)
    (K L : Set ℍ) (hK : IsCompact K) (hL : IsCompact L)
    (b₁ b₂ : SmoothUpperSeed)
    (hKS : Function.support (upperFunction b₁.toFun) ⊆ strip)
    (hLS : Function.support (upperFunction b₂.toFun) ⊆ strip)
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hbound₁ : ∀ z ∈ K, ‖upperFunction b₁.toFun z‖ ≤ B₁)
    (hbound₂ : ∀ z ∈ L, ‖upperFunction b₂.toFun z‖ ≤ B₂)
    (hb₁ : tsupport (upperFunction b₁.toFun) ⊆ K)
    (hb₂ : tsupport (upperFunction b₂.toFun) ⊆ L)
    (E : Expression) (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (hA : QuotientRealizes N E A) :
    let E' := CrossCompactBranch.localExpression N K L hK hL
      (upperFunction b₁.toFun) (upperFunction b₂.toFun)
      (upperFunction_continuous b₁.smooth).measurable
      (upperFunction_continuous b₂.smooth).measurable B₁ B₂ hB₁ hB₂
      (CrossCompactBranch.cutoff_global_bound _ K hb₁ B₁ hB₁ hbound₁)
      (CrossCompactBranch.cutoff_global_bound _ L hb₂ B₂ hB₂ hbound₂) E
    let T₁ := crossQuotientLocalization N 0 K hK b₁ hbound₁
    let T₂ := crossQuotientLocalization N 0 L hL b₂ hbound₂
    let J := cylinderZeroExtension.toContinuousLinearMap.comp (AutomorphicSpace 0).subtypeL
    T₁.adjoint.comp (A.comp T₂) = J.adjoint.comp ((holomorphicSum E' 0).comp J) := by
  intro E' T₁ T₂ J
  have he : (fun x : AutomorphicSpace 0 => T₁.adjoint (A (T₂ x))) =
      fun x => J.adjoint (holomorphicSum E' 0 (J x)) := by
    apply (poincareSeedVector_dense 0).equalizer (by fun_prop) (by fun_prop)
    funext v
    apply (poincareSeedVector_dense 0).eq_of_inner_right (𝕜 := ℂ)
    intro u
    dsimp only [Function.comp_apply]
    rw [T₁.adjoint_inner_right,J.adjoint_inner_right]
    exact crossQuotientLocalization_physical_seed_pairing N K L hK hL
      b₁ b₂ hKS hLS B₁ B₂ hB₁ hB₂ hbound₁ hbound₂ hb₁ hb₂ u v E A hA
  apply ContinuousLinearMap.ext
  intro x
  exact congrFun he x

#print axioms cross_localExpression_physical_pairing
#print axioms crossQuotientLocalization_physical_seed_pairing
#print axioms crossQuotientLocalization_physical_sandwich

end QuantitativeMaass
