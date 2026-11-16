module

public import QuantitativeMaassCrossCompactBranchV1
public import QuantitativeMaassReflectionOperatorV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane AsymptoticFiniteBranch
open AsymptoticCongruenceStrip
open scoped Topology
namespace QuantitativeMaass.CrossCompactBranch

theorem reflected_cutoff_support (b : ℍ→ℂ) (K : Set ℍ)
    (hb : tsupport b ⊆ K) :
    tsupport (fun z => b (J•z)) ⊆ (fun z : ℍ => J•z) '' K := by
  intro z hz
  have hh := tsupport_comp_subset_preimage b (continuous_const_smul J) hz
  exact ⟨J•z,hb hh,reflection_involutive z⟩

/-- A reflected compact sandwich uses the same finite overlap construction
on the reflected output support. Its rational labels remain orientation
preserving; reflection is the final explicit argument of the expression. -/
theorem reflected_expression_expansion (N : ℕ) (K L : Set ℍ)
    (hK : IsCompact K) (hL : IsCompact L)
    (b₁ b₂ : ℍ→ℂ) (hb₁ : Measurable b₁) (hb₂ : Measurable b₂)
    (hs₁ : tsupport b₁ ⊆ K) (hs₂ : tsupport b₂ ⊆ L)
    (B₁ B₂ : ℝ) (hB₁ : 0≤B₁) (hB₂ : 0≤B₂)
    (hbound₁ : ∀ x,‖b₁ x‖≤B₁) (hbound₂ : ∀ x,‖b₂ x‖≤B₂)
    (E : Expression) (f : ℍ→ℂ) (x : ℍ) :
    star (b₁ x)*expressionFunction E
      (poincareSum (G := gamma N) (fun y => b₂ y*f y)) (J•x) =
      expressionFunction
        (localExpression N ((fun z : ℍ => J•z) '' K) L
          (hK.image (continuous_const_smul J)) hL
          (fun z => b₁ (J•z)) b₂ (hb₁.comp (continuous_const_smul J).measurable) hb₂
          B₁ B₂ hB₁ hB₂ (fun z => hbound₁ (J•z)) hbound₂ E) f (J•x) := by
  have hh := expression_expansion N ((fun z : ℍ => J•z) '' K) L
    (hK.image (continuous_const_smul J)) hL
    (fun z => b₁ (J•z)) b₂ (hb₁.comp (continuous_const_smul J).measurable) hb₂
    (reflected_cutoff_support b₁ K hs₁) hs₂ B₁ B₂ hB₁ hB₂
    (fun z => hbound₁ (J•z)) hbound₂ E f (J•x)
  simpa only [reflection_involutive] using hh

#print axioms reflected_cutoff_support
#print axioms reflected_expression_expansion

end QuantitativeMaass.CrossCompactBranch
