module

public import AsymptoticFiniteBranchRetainedV1
public import AsymptoticCylinderTerminalLiftV1
public import AsymptoticCylinderUpperTailV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegionL2

open MeasureTheory Set ContinuousLinearMap

variable {α : Type*} [MeasurableSpace α]

theorem projection_diff (μ : Measure α) (s t : Set α)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    projection μ (s\t) (hs.diff ht)=(1-projection μ t ht).comp (projection μ s hs) := by
  ext1 f
  change projection μ (s\t) (hs.diff ht) f=projection μ s hs f-projection μ t ht (projection μ s hs f)
  apply Lp.ext
  filter_upwards [projection_coeFn μ (s\t) (hs.diff ht) f,
    projection_coeFn μ s hs f,projection_coeFn μ t ht (projection μ s hs f),
    Lp.coeFn_sub (projection μ s hs f) (projection μ t ht (projection μ s hs f))]
    with x hd hsx htx hsub
  rw [hd,hsub,Pi.sub_apply,htx]
  classical
  by_cases hx : x∈s <;> by_cases hy : x∈t <;> simp [hx,hy,hsx]

#print axioms projection_diff

end AsymptoticRegionL2

namespace AsymptoticCylinder

open MeasureTheory Set Filter

/-- Open and closed height cutoffs define the same L² projection. -/
theorem upperProjection_eq_terminal (H : ℝ) :
    upperProjection H=AsymptoticCylinderTerminal.projection H := by
  have hn : ∀ᵐ z ∂measure, z.2≠H := by
    apply (Measure.ae_prod_iff_ae_ae ((measurableSet_singleton H).preimage measurable_snd).compl).mpr
    apply Eventually.of_forall
    intro x
    apply ae_iff.mpr
    simp
  ext1 f
  apply Lp.ext
  filter_upwards [AsymptoticRegionL2.projection_coeFn measure (upperRegion H)
      (upperRegion_measurable H) f,AsymptoticCylinderTerminal.projection_coeFn H f,hn]
      with z ho hc hz
  change AsymptoticRegionL2.projection measure (upperRegion H) (upperRegion_measurable H) f z=_
  rw [ho,hc]
  classical
  have he : z∈upperRegion H ↔ z∈AsymptoticCylinderTerminal.region H :=
    lt_iff_le_and_ne.trans (and_iff_left hz.symm)
  by_cases hy : z∈upperRegion H
  · rw [indicator_of_mem hy,indicator_of_mem (he.mp hy)]
  · rw [indicator_of_notMem hy,indicator_of_notMem (fun h => hy (he.mpr h))]

#print axioms upperProjection_eq_terminal

end AsymptoticCylinder

namespace AsymptoticFiniteBranch

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap AsymptoticCylinderLift

/-- The retained strip uses the same closed lower and open upper boundary
as subtracting the upper terminal projection. -/
theorem retainedRegion_eq_diff (Y H : ℝ) :
    retainedRegion Y H=AsymptoticCertificateOperators.highStrip Y\AsymptoticCertificateOperators.highStrip H := by
  ext z
  simp only [retainedRegion,AsymptoticCertificateOperators.highStrip,mem_inter_iff,
    mem_preimage,mem_Ico,mem_sdiff,mem_ofPred_eq,← not_le]
  tauto

noncomputable def retainedProjection (Y H : ℝ) :
    AsymptoticCylinder.Space →L[ℂ] AsymptoticCylinder.Space :=
  (1-AsymptoticCylinder.upperProjection H).comp (AsymptoticCylinder.upperProjection Y)

theorem lift_retainedProjection (Y H : ℝ) (f : AsymptoticCylinder.Space) :
    lift (retainedProjection Y H f)=
      AsymptoticRegionL2.projection volume (retainedRegion Y H) (retainedRegion_measurable Y H) (lift f) := by
  simp only [retainedRegion_eq_diff]
  rw [AsymptoticRegionL2.projection_diff]
  simp only [retainedProjection,AsymptoticCylinder.upperProjection_eq_terminal]
  change lift (AsymptoticCylinderTerminal.projection Y f-
      AsymptoticCylinderTerminal.projection H (AsymptoticCylinderTerminal.projection Y f))=
    AsymptoticCylinderTerminal.hyperProjection Y (lift f)-
      AsymptoticCylinderTerminal.hyperProjection H (AsymptoticCylinderTerminal.hyperProjection Y (lift f))
  rw [map_sub,AsymptoticCylinderTerminal.lift_projection,
    AsymptoticCylinderTerminal.lift_projection,AsymptoticCylinderTerminal.lift_projection]

theorem retainedProjection_eq_region (Y H : ℝ) :
    retainedProjection Y H=AsymptoticRegionL2.projection AsymptoticCylinder.measure
      (AsymptoticCylinderTerminal.region Y\AsymptoticCylinderTerminal.region H)
      ((AsymptoticCylinderTerminal.region_measurable Y).diff (AsymptoticCylinderTerminal.region_measurable H)) := by
  rw [AsymptoticRegionL2.projection_diff _ _ _
    (AsymptoticCylinderTerminal.region_measurable Y) (AsymptoticCylinderTerminal.region_measurable H)]
  simp only [retainedProjection,AsymptoticCylinder.upperProjection_eq_terminal,
    AsymptoticCylinderTerminal.projection]

theorem retainedProjection_adjoint (Y H : ℝ) :
    (retainedProjection Y H).adjoint=retainedProjection Y H := by
  rw [retainedProjection_eq_region,AsymptoticRegionL2.projection_adjoint]

theorem retainedProjection_norm_le (Y H : ℝ) : ‖retainedProjection Y H‖≤1 := by
  rw [retainedProjection_eq_region]
  exact AsymptoticRegionL2.projection_norm_le _ _ _

#print axioms retainedProjection_eq_region
#print axioms retainedProjection_adjoint
#print axioms retainedProjection_norm_le
#print axioms retainedRegion_eq_diff
#print axioms lift_retainedProjection

end AsymptoticFiniteBranch
