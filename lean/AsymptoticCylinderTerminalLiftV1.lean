module

public import AsymptoticCylinderLiftRangeV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegionL2

open MeasureTheory Set Filter ContinuousLinearMap InnerProductSpace

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α) (hs : MeasurableSet s)

theorem restrict_eq_adjoint : restrict μ s hs=(Space μ s hs).subtypeL.adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  change ⟪projection μ s hs f,(g:Lp ℂ 2 μ)⟫_ℂ=⟪f,(g:Lp ℂ 2 μ)⟫_ℂ
  have hg := (mem_space μ s hs (g:Lp ℂ 2 μ)).mp g.property
  calc
    _ = ⟪f,(projection μ s hs).adjoint (g:Lp ℂ 2 μ)⟫_ℂ := (adjoint_inner_right _ _ _).symm
    _ = _ := by rw [projection_adjoint,hg]

theorem subtype_comp_adjoint :
    (Space μ s hs).subtypeL.comp (Space μ s hs).subtypeL.adjoint=projection μ s hs :=
  congrArg (fun T : Lp ℂ 2 μ →L[ℂ] Space μ s hs => (Space μ s hs).subtypeL.comp T)
    (restrict_eq_adjoint μ s hs).symm

theorem projection_comp_of_subset (t : Set α) (ht : MeasurableSet t) (hst : s⊆t) :
    (projection μ s hs).comp (projection μ t ht)=projection μ s hs := by
  ext1 f
  apply Lp.ext
  filter_upwards [projection_coeFn μ s hs (projection μ t ht f),projection_coeFn μ t ht f,
    projection_coeFn μ s hs f] with x hstf htf hsf
  change projection μ s hs (projection μ t ht f) x=projection μ s hs f x
  rw [hstf,hsf]
  classical
  by_cases hx : x∈s
  · rw [indicator_of_mem hx,indicator_of_mem hx,htf,indicator_of_mem (hst hx)]
  · rw [indicator_of_notMem hx,indicator_of_notMem hx]

#print axioms restrict_eq_adjoint
#print axioms subtype_comp_adjoint
#print axioms projection_comp_of_subset

end AsymptoticRegionL2

namespace AsymptoticCylinderTerminal

open MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticCylinderLift

noncomputable def ambientLift (ε : ℝ) : Space ε →L[ℂ] AsymptoticHyperbolicSlash.Space :=
  lift.toContinuousLinearMap.comp (Space ε).subtypeL

theorem ambientLift_adjoint_self (ε : ℝ) : (ambientLift ε).adjoint.comp (ambientLift ε)=1 :=
  (norm_map_iff_adjoint_comp_self (ambientLift ε)).mp (fun f => lift_norm (f:AsymptoticCylinder.Space))

theorem ambientLift_self_adjoint (ε : ℝ) :
    (ambientLift ε).comp (ambientLift ε).adjoint=hyperProjection ε := by
  rw [ambientLift,adjoint_comp]
  apply ContinuousLinearMap.ext
  intro u
  have hS := congrArg (fun T : AsymptoticCylinder.Space →L[ℂ] AsymptoticCylinder.Space =>
    T (lift.toContinuousLinearMap.adjoint u))
      (AsymptoticRegionL2.subtype_comp_adjoint AsymptoticCylinder.measure (region ε) (region_measurable ε))
  change (Space ε).subtypeL ((Space ε).subtypeL.adjoint (lift.toContinuousLinearMap.adjoint u))=
    projection ε (lift.toContinuousLinearMap.adjoint u) at hS
  change lift ((Space ε).subtypeL ((Space ε).subtypeL.adjoint (lift.toContinuousLinearMap.adjoint u)))=
    hyperProjection ε u
  rw [hS,lift_projection]
  have hL := congrArg (fun T : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space => T u)
    lift_comp_adjoint
  change lift (lift.toContinuousLinearMap.adjoint u)=_ at hL
  rw [hL]
  exact congrArg (fun T : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space => T u)
    (AsymptoticRegionL2.projection_comp_of_subset volume (AsymptoticCertificateOperators.highStrip ε)
      (AsymptoticCertificateOperators.highStrip_measurable ε) AsymptoticMassTransport.strip
      AsymptoticMassTransport.strip_measurable (fun _ hz => hz.1))

#print axioms ambientLift_adjoint_self
#print axioms ambientLift_self_adjoint

end AsymptoticCylinderTerminal
