module

public import QuantitativeMaassCylinderMeanMultiplierV1
public import AsymptoticCylinderLiftRangeV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson AsymptoticMassTransport

namespace QuantitativeMaass

/-- Zero extension has exactly the physical strip-supported range. -/
theorem cylinderZeroExtension_exists_of_support (u : AsymptoticHyperbolicSlash.Space)
    (hu : ∀ᵐ z ∂volume,z∉strip → u z=0) :
    ∃ f : Lp ℂ 2 (quotientMeasure 0),cylinderZeroExtension f=u := by
  have hm : MemLp (u : ℍ → ℂ) 2 (quotientMeasure 0) := by
    rw [translation_quotient_measure]
    exact (Lp.memLp u).restrict strip
  refine ⟨hm.toLp u,?_⟩
  apply Lp.ext
  filter_upwards [cylinderZeroExtension_coeFn_of_ae (hm.toLp u) u hm.coeFn_toLp,hu] with z hz hzs
  rw [hz]
  classical
  by_cases hs : z∈strip
  · exact Set.indicator_of_mem hs _
  · rw [Set.indicator_of_notMem hs,hzs hs]

theorem cylinderZeroExtension_adjoint_self (f : Lp ℂ 2 (quotientMeasure 0)) :
    cylinderZeroExtension.toContinuousLinearMap.adjoint (cylinderZeroExtension f)=f := by
  simpa only [ContinuousLinearMap.comp_apply,one_apply_eq_self,
    LinearIsometry.coe_toContinuousLinearMap] using!
    congrArg (fun B => B f) cylinderZeroExtension.adjoint_comp_self

theorem productCylinder_lift_in_range (g : AsymptoticCylinder.Space) :
    ∃ f : Lp ℂ 2 (quotientMeasure 0),cylinderZeroExtension f=AsymptoticCylinderLift.lift g := by
  apply cylinderZeroExtension_exists_of_support
  filter_upwards [AsymptoticCylinderLift.lift_coeFn g] with z hz hs
  rw [hz]
  exact Set.indicator_of_notMem hs _

/-- Exact unitary coordinate change from the product cylinder with its
half-density convention to the hyperbolic translation-cylinder realization. -/
def productCylinderToTranslation : AsymptoticCylinder.Space →ₗᵢ[ℂ] Lp ℂ 2 (quotientMeasure 0) where
  toLinearMap := (cylinderZeroExtension.toContinuousLinearMap.adjoint.comp
    AsymptoticCylinderLift.lift.toContinuousLinearMap).toLinearMap
  norm_map' g := by
    obtain ⟨f,hf⟩ := productCylinder_lift_in_range g
    change ‖cylinderZeroExtension.toContinuousLinearMap.adjoint (AsymptoticCylinderLift.lift g)‖=‖g‖
    rw [←hf,cylinderZeroExtension_adjoint_self]
    exact (cylinderZeroExtension_norm f).symm.trans
      ((congrArg norm hf).trans (AsymptoticCylinderLift.lift_norm g))

theorem productCylinderToTranslation_lift (g : AsymptoticCylinder.Space) :
    cylinderZeroExtension (productCylinderToTranslation g)=AsymptoticCylinderLift.lift g := by
  obtain ⟨f,hf⟩ := productCylinder_lift_in_range g
  change cylinderZeroExtension (cylinderZeroExtension.toContinuousLinearMap.adjoint
    (AsymptoticCylinderLift.lift g))=_
  rw [←hf,cylinderZeroExtension_adjoint_self]

theorem productCylinderToTranslation_surjective : Function.Surjective productCylinderToTranslation := by
  intro f
  obtain ⟨g,hg⟩ := AsymptoticCylinderLift.exists_lift_of_support (cylinderZeroExtension f) (by
    filter_upwards [cylinderZeroExtension_coeFn f] with z hz hs
    rw [hz]
    exact Set.indicator_of_notMem hs _)
  refine ⟨g,?_⟩
  apply cylinderZeroExtension.injective
  rw [productCylinderToTranslation_lift,hg]

#print axioms cylinderZeroExtension_exists_of_support
#print axioms cylinderZeroExtension_adjoint_self
#print axioms productCylinderToTranslation_lift
#print axioms productCylinderToTranslation_surjective

end QuantitativeMaass
