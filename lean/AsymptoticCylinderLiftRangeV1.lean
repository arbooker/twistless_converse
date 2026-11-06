module

public import AsymptoticCylinderSectionV1
public import AsymptoticHeightInverseV1
public import AsymptoticCylinderTerminalV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticZeroExtension

open MeasureTheory Set Filter

theorem exists_preimage_of_support {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Set α) (hs : MeasurableSet s) (u : Lp ℂ 2 μ)
    (hu : ∀ᵐ x ∂μ,x∉s → u x=0) : ∃ g,isometry μ s hs g=u := by
  have hm : MemLp u 2 (μ.restrict s) := (Lp.memLp u).mono_measure Measure.restrict_le_self
  let g := hm.toLp u
  refine ⟨g,?_⟩
  have hg := (ae_eq_restrict_iff_indicator_ae_eq hs).mp (MemLp.coeFn_toLp hm)
  apply Lp.ext
  filter_upwards [isometry_coeFn μ s hs g,hg,hu] with x he hg hx
  rw [he]
  change s.indicator g x=s.indicator u x at hg
  rw [hg]
  classical
  by_cases hxs : x∈s
  · exact indicator_of_mem hxs _
  · rw [indicator_of_notMem hxs,hx hxs]

#print axioms exists_preimage_of_support

end AsymptoticZeroExtension

namespace AsymptoticCylinderLift

open MeasureTheory UpperHalfPlane Filter ContinuousLinearMap
open AsymptoticStripCoordinates AsymptoticFlatHyperbolic

/-- The lift covers the entire strip-supported ambient L² space. -/
theorem exists_lift_of_support (u : AsymptoticHyperbolicSlash.Space)
    (hu : ∀ᵐ z ∂volume,z∉AsymptoticMassTransport.strip → u z=0) : ∃ f,lift f=u := by
  have hi : ∀ᵐ z ∂flat,z∉AsymptoticMassTransport.strip → inverseHeight u z=0 := by
    filter_upwards [inverseHeight_coeFn u,flat_ac_hyperbolic.ae_le hu] with z hz hu hs
    rw [hz,hu hs,mul_zero]
  obtain ⟨g,hg⟩ := AsymptoticZeroExtension.exists_preimage_of_support flat
    AsymptoticMassTransport.strip AsymptoticMassTransport.strip_measurable (inverseHeight u) hi
  obtain ⟨f,hf⟩ := pullback_surjective g
  refine ⟨f,?_⟩
  change heightMap (AsymptoticZeroExtension.isometry flat AsymptoticMassTransport.strip
    AsymptoticMassTransport.strip_measurable (pullback f))=u
  rw [hf,hg,heightMap_inverseHeight]

/-- The product of the lift with its adjoint is exactly strip restriction,
which justifies multiplying transported finite observation operators. -/
theorem lift_comp_adjoint : lift.toContinuousLinearMap.comp lift.toContinuousLinearMap.adjoint=
    AsymptoticRegionL2.projection volume AsymptoticMassTransport.strip
      AsymptoticMassTransport.strip_measurable := by
  let P := AsymptoticRegionL2.projection volume AsymptoticMassTransport.strip
    AsymptoticMassTransport.strip_measurable
  have hP : P.adjoint=P := AsymptoticRegionL2.projection_adjoint _ _ _
  have hL : P.comp lift.toContinuousLinearMap=lift.toContinuousLinearMap := by
    ext1 f
    exact (AsymptoticRegionL2.projection_eq_self_iff volume AsymptoticMassTransport.strip
      AsymptoticMassTransport.strip_measurable (lift f)).mpr (lift_zero_off_strip f)
  have ha := congrArg ContinuousLinearMap.adjoint hL
  rw [adjoint_comp,hP] at ha
  apply ContinuousLinearMap.ext
  intro u
  have hu : ∀ᵐ z ∂volume,z∉AsymptoticMassTransport.strip → P u z=0 :=
    (AsymptoticRegionL2.projection_eq_self_iff _ _ _ _).mp
      (AsymptoticRegionL2.projection_idempotent _ _ _ u)
  obtain ⟨f,hf⟩ := exists_lift_of_support (P u) hu
  have he := congrArg (fun T : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticCylinder.Space => T u) ha
  change lift (lift.toContinuousLinearMap.adjoint u)=P u
  calc
    lift (lift.toContinuousLinearMap.adjoint u)=lift (lift.toContinuousLinearMap.adjoint (P u)) :=
      congrArg lift he.symm
    _ = P u := by rw [← hf,AsymptoticCylinderTerminal.adjoint_lift]

#print axioms exists_lift_of_support
#print axioms lift_comp_adjoint

end AsymptoticCylinderLift
