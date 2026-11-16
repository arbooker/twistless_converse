module

public import QuantitativeMaassCylinderZeroModeV1
public import QuantitativeMaassFiberMultiplierV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip AsymptoticMassTransport

namespace QuantitativeMaass

theorem cylinderFold_coeFn_ae (f : Lp ℂ 2 (quotientMeasure 0)) :
    (fun z => f (cylinderFold z))=ᵐ[quotientMeasure 0] (f : ℍ → ℂ) := by
  have hs : ∀ᵐ z ∂quotientMeasure 0,z∈strip := by
    rw [translation_quotient_measure]
    exact ae_restrict_mem strip_measurable
  filter_upwards [hs] with z hz
  rw [cylinderFold_self hz]

/-- An actual measurable periodic representative for every cylinder L2 class. -/
def cylinderRepresentative (f : Lp ℂ 2 (quotientMeasure 0)) :
    AutomorphicL2.representatives (gamma 0) (quotientMeasure 0) := by
  refine ⟨fun z => f (cylinderFold z),
    (Lp.stronglyMeasurable f).measurable.comp cylinderFold_measurable,?_,
    (Lp.memLp f).ae_eq (cylinderFold_coeFn_ae f).symm⟩
  intro γ z
  exact congrArg f (cylinderFold_invariant γ z)

theorem cylinderRepresentative_class (f : Lp ℂ 2 (quotientMeasure 0)) :
    AutomorphicL2.denseEmbedding (gamma 0) (quotientMeasure 0) (cylinderRepresentative f)=
      cylinderAutomorphic f := by
  apply Subtype.ext
  apply Lp.ext
  exact (cylinderRepresentative f).property.2.2.coeFn_toLp.trans (cylinderFold_coeFn_ae f)

theorem cylinder_height_invariant (γ : gamma 0) (z : ℍ) : (γ.val•z).im=z.im := by
  obtain ⟨n,hn⟩ := gamma_zero_translation γ
  rw [hn,AsymptoticCompactTranslation.label_im]

def cylinderHeightMultiplier (c : ℝ → ℂ) (hc : Measurable c) (C : ℝ) (hC : ∀ y,‖c y‖≤C) :
    Lp ℂ 2 (quotientMeasure 0) →L[ℂ] Lp ℂ 2 (quotientMeasure 0) :=
  AsymptoticL2Multiplier.operator (fun z : ℍ => c z.im)
    (hc.comp continuous_im.measurable).aestronglyMeasurable (Eventually.of_forall (fun z => hC z.im))

def cylinderMultipliedRepresentative (c : ℝ → ℂ) (hc : Measurable c)
    (C : ℝ) (hC : ∀ y,‖c y‖≤C)
    (f : AutomorphicL2.representatives (gamma 0) (quotientMeasure 0)) :
    AutomorphicL2.representatives (gamma 0) (quotientMeasure 0) := by
  refine ⟨fun z : ℍ => c z.im*f.val z,(hc.comp continuous_im.measurable).mul f.property.1,?_,?_⟩
  · intro γ z
    dsimp only
    rw [cylinder_height_invariant,f.property.2.1]
  · apply f.property.2.2.of_le_mul (c:=C)
      ((hc.comp continuous_im.measurable).aestronglyMeasurable.mul f.property.2.2.aestronglyMeasurable)
    filter_upwards with z
    change ‖c z.im*f.val z‖≤C*‖f.val z‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC z.im) (norm_nonneg _)

theorem cylinderMultipliedRepresentative_class (c : ℝ → ℂ) (hc : Measurable c)
    (C : ℝ) (hC : ∀ y,‖c y‖≤C) (f : Lp ℂ 2 (quotientMeasure 0)) :
    AutomorphicL2.denseEmbedding (gamma 0) (quotientMeasure 0)
      (cylinderMultipliedRepresentative c hc C hC (cylinderRepresentative f))=
      cylinderAutomorphic (cylinderHeightMultiplier c hc C hC f) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [(cylinderMultipliedRepresentative c hc C hC (cylinderRepresentative f)).property.2.2.coeFn_toLp,
    cylinderFold_coeFn_ae f,AsymptoticL2Multiplier.operator_coeFn (fun z : ℍ => c z.im)
      (hc.comp continuous_im.measurable).aestronglyMeasurable
      (Eventually.of_forall (fun z : ℍ => hC z.im)) f] with z h1 h2 h3
  change _=cylinderHeightMultiplier c hc C hC f z
  change (AutomorphicL2.denseEmbedding (gamma 0) (quotientMeasure 0)
    (cylinderMultipliedRepresentative c hc C hC (cylinderRepresentative f))).val z=
      (cylinderMultipliedRepresentative c hc C hC (cylinderRepresentative f)).val z at h1
  change cylinderHeightMultiplier c hc C hC f z=c z.im*f z at h3
  rw [h1,h3]
  change c z.im*f (cylinderFold z)=c z.im*f z
  rw [h2]

#print axioms cylinderFold_coeFn_ae
#print axioms cylinderRepresentative_class
#print axioms cylinder_height_invariant
#print axioms cylinderMultipliedRepresentative_class

end QuantitativeMaass
