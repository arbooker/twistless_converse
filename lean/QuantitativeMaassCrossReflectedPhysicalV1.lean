module

public import QuantitativeMaassCrossReflectedPairingV1
public import QuantitativeMaassCrossReflectedExpressionV1
public import QuantitativeMaassPhysicalReflectionV1
public import QuantitativeMaassCrossPhysicalPairingV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane AsymptoticFiniteBranch ContinuousLinearMap
open AsymptoticClassicalPetersson AsymptoticMassTransport AsymptoticCongruenceStrip
open scoped Topology InnerProductSpace
namespace QuantitativeMaass

def reflectedLocalExpression (N : ℕ) (K L : Set ℍ) (hK : IsCompact K) (hL : IsCompact L)
    (b₁ b₂ : ℍ→ℂ) (hb₁ : Measurable b₁) (hb₂ : Measurable b₂)
    (B₁ B₂ : ℝ) (hB₁ : 0≤B₁) (hB₂ : 0≤B₂)
    (hbound₁ : ∀ x,‖b₁ x‖≤B₁) (hbound₂ : ∀ x,‖b₂ x‖≤B₂)
    (E : Expression) : Expression :=
  CrossCompactBranch.localExpression N ((fun z : ℍ => J•z) '' K) L
    (hK.image (continuous_const_smul J)) hL
    (fun z => b₁ (J•z)) b₂ (hb₁.comp (continuous_const_smul J).measurable) hb₂
    B₁ B₂ hB₁ hB₂ (fun z => hbound₁ (J•z)) hbound₂ E

theorem cross_reflected_localExpression_physical_pairing (N : ℕ)
    (K L : Set ℍ) (hK : IsCompact K) (hL : IsCompact L)
    (b₁ b₂ : ℍ→ℂ) (hb₁ : Measurable b₁) (hb₂ : Measurable b₂)
    (hKS : Function.support b₁ ⊆ strip) (hLS : Function.support b₂ ⊆ strip)
    (hs₁ : tsupport b₁ ⊆ K) (hs₂ : tsupport b₂ ⊆ L)
    (B₁ B₂ : ℝ) (hB₁ : 0≤B₁) (hB₂ : 0≤B₂)
    (hbound₁ : ∀ x,‖b₁ x‖≤B₁) (hbound₂ : ∀ x,‖b₂ x‖≤B₂)
    (E : Expression) (f g : Lp ℂ 2 (quotientMeasure 0)) (φ ψ : ℍ→ℂ)
    (hf : (f : ℍ→ℂ) =ᵐ[quotientMeasure 0] φ)
    (hg : (g : ℍ→ℂ) =ᵐ[quotientMeasure 0] ψ) :
    let E' := reflectedLocalExpression N K L hK hL b₁ b₂ hb₁ hb₂
      B₁ B₂ hB₁ hB₂ hbound₁ hbound₂ E
    inner ℂ (cylinderZeroExtension f)
      (physicalReflection (holomorphicSum E' 0 (cylinderZeroExtension g))) =
      ∫ z in K, star (φ z)*expressionFunction E' ψ (J•z) := by
  intro E'
  rw [physical_reflected_expression_pairing E' _ _ (strip.indicator φ) (strip.indicator ψ)
    (cylinderZeroExtension_coeFn_of_ae f φ hf) (cylinderZeroExtension_coeFn_of_ae g ψ hg)]
  have hfun : (fun y => b₂ y*strip.indicator ψ y) = fun y => b₂ y*ψ y := by
    funext y
    by_cases hy : y∈strip
    · rw [indicator_of_mem hy]
    · have hb : b₂ y=0 := Classical.byContradiction (fun h => hy (hLS h))
      rw [hb,zero_mul,zero_mul]
  rw [←integral_indicator hK.measurableSet]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    have he := CrossCompactBranch.reflected_expression_expansion N K L hK hL
      b₁ b₂ hb₁ hb₂ hs₁ hs₂ B₁ B₂ hB₁ hB₂ hbound₁ hbound₂ E (strip.indicator ψ) z
    have he' := CrossCompactBranch.reflected_expression_expansion N K L hK hL
      b₁ b₂ hb₁ hb₂ hs₁ hs₂ B₁ B₂ hB₁ hB₂ hbound₁ hbound₂ E ψ z
    change _ = expressionFunction E' (strip.indicator ψ) (J•z) at he
    change _ = expressionFunction E' ψ (J•z) at he'
    change star (strip.indicator φ z)*expressionFunction E' (strip.indicator ψ) (J•z) = _
    by_cases hz : z∈K
    · rw [indicator_of_mem hz]
      by_cases hzstrip : z∈strip
      · rw [indicator_of_mem hzstrip]
        rw [hfun] at he
        rw [←he,he']
      · have hb : b₁ z=0 := Classical.byContradiction (fun h => hzstrip (hKS h))
        rw [indicator_of_notMem hzstrip,star_zero,zero_mul]
        rw [hb,star_zero,zero_mul] at he'
        rw [←he',mul_zero]
    · rw [indicator_of_notMem hz]
      have hb : b₁ z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hs₁ h))
      rw [hb,star_zero,zero_mul] at he
      rw [←he,mul_zero])

/-- Exact completed reflected sandwich. The geometric reflection is
separate from the finite rational expression and no cutoff is commuted. -/
theorem crossQuotientLocalization_reflected_physical_sandwich (N : ℕ)
    (K L : Set ℍ) (hK : IsCompact K) (hL : IsCompact L)
    (b₁ b₂ : SmoothUpperSeed)
    (hKS : Function.support (upperFunction b₁.toFun) ⊆ strip)
    (hLS : Function.support (upperFunction b₂.toFun) ⊆ strip)
    (B₁ B₂ : ℝ) (hB₁ : 0≤B₁) (hB₂ : 0≤B₂)
    (hbound₁ : ∀ z∈K,‖upperFunction b₁.toFun z‖≤B₁)
    (hbound₂ : ∀ z∈L,‖upperFunction b₂.toFun z‖≤B₂)
    (hb₁ : tsupport (upperFunction b₁.toFun) ⊆ K)
    (hb₂ : tsupport (upperFunction b₂.toFun) ⊆ L)
    (E : Expression) (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (hA : QuotientRealizes N E A) :
    let E' := reflectedLocalExpression N K L hK hL
      (upperFunction b₁.toFun) (upperFunction b₂.toFun)
      (upperFunction_continuous b₁.smooth).measurable (upperFunction_continuous b₂.smooth).measurable
      B₁ B₂ hB₁ hB₂
      (CrossCompactBranch.cutoff_global_bound _ K hb₁ B₁ hB₁ hbound₁)
      (CrossCompactBranch.cutoff_global_bound _ L hb₂ B₂ hB₂ hbound₂) E
    let T₁ := crossQuotientLocalization N 0 K hK b₁ hbound₁
    let T₂ := crossQuotientLocalization N 0 L hL b₂ hbound₂
    let Z := cylinderZeroExtension.toContinuousLinearMap.comp (AutomorphicSpace 0).subtypeL
    T₁.adjoint.comp ((reflectionIsometry N).toContinuousLinearMap.comp (A.comp T₂)) =
      Z.adjoint.comp (physicalReflection.toContinuousLinearMap.comp ((holomorphicSum E' 0).comp Z)) := by
  intro E' T₁ T₂ Z
  have he : (fun x : AutomorphicSpace 0 => T₁.adjoint (reflectionIsometry N (A (T₂ x)))) =
      fun x => Z.adjoint (physicalReflection (holomorphicSum E' 0 (Z x))) := by
    apply (poincareSeedVector_dense 0).equalizer (by fun_prop) (by fun_prop)
    funext v
    apply (poincareSeedVector_dense 0).eq_of_inner_right (𝕜 := ℂ)
    intro u
    dsimp only [Function.comp_apply]
    rw [T₁.adjoint_inner_right,Z.adjoint_inner_right]
    rw [crossQuotientLocalization_reflected_expression_pairing N 0 K L hK hL b₁ b₂
      hbound₁ hbound₂ hb₁ hb₂ u v E A hA]
    have hphysical := cross_reflected_localExpression_physical_pairing N K L hK hL
      (upperFunction b₁.toFun) (upperFunction b₂.toFun)
      (upperFunction_continuous b₁.smooth).measurable (upperFunction_continuous b₂.smooth).measurable
      hKS hLS hb₁ hb₂ B₁ B₂ hB₁ hB₂
      (CrossCompactBranch.cutoff_global_bound _ K hb₁ B₁ hB₁ hbound₁)
      (CrossCompactBranch.cutoff_global_bound _ L hb₂ B₂ hB₂ hbound₂) E
      (poincareSeedVector 0 u).val (poincareSeedVector 0 v).val _ _
      (poincareSeedVector_coeFn 0 u) (poincareSeedVector_coeFn 0 v)
    change inner ℂ (Z (poincareSeedVector 0 u))
      (physicalReflection (holomorphicSum E' 0 (Z (poincareSeedVector 0 v)))) = _ at hphysical
    rw [hphysical]
    have hcomm : (fun w => poincareSum (G := gamma 0) (upperFunction v.toFun) w *
        upperFunction b₂.toFun w) =
        fun w => upperFunction b₂.toFun w*poincareSum (G := gamma 0) (upperFunction v.toFun) w := by
      funext w
      ring
    rw [hcomm]
    apply setIntegral_congr_fun hK.measurableSet
    intro z _
    have hh := CrossCompactBranch.reflected_expression_expansion N K L hK hL
      (upperFunction b₁.toFun) (upperFunction b₂.toFun)
      (upperFunction_continuous b₁.smooth).measurable (upperFunction_continuous b₂.smooth).measurable
      hb₁ hb₂ B₁ B₂ hB₁ hB₂
      (CrossCompactBranch.cutoff_global_bound _ K hb₁ B₁ hB₁ hbound₁)
      (CrossCompactBranch.cutoff_global_bound _ L hb₂ B₂ hB₂ hbound₂) E
      (poincareSum (G := gamma 0) (upperFunction v.toFun)) z
    change _ = expressionFunction E' (poincareSum (G := gamma 0) (upperFunction v.toFun)) (J•z) at hh
    change _ = star (poincareSum (G := gamma 0) (upperFunction u.toFun) z)*
      expressionFunction E' (poincareSum (G := gamma 0) (upperFunction v.toFun)) (J•z)
    dsimp only
    rw [←hh,star_mul]
    ring
  apply ContinuousLinearMap.ext
  intro x
  exact congrFun he x

#print axioms cross_reflected_localExpression_physical_pairing
#print axioms crossQuotientLocalization_reflected_physical_sandwich

end QuantitativeMaass
