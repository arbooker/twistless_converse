module

public import AsymptoticCylinderLiftV1
public import AsymptoticCertificateSupportV1

set_option autoImplicit false
set_option maxHeartbeats 400000
@[expose] public section

namespace AsymptoticCylinderTerminal

open MeasureTheory Set ContinuousLinearMap
open AsymptoticCylinderLift AsymptoticStripCoordinates

def region (ε : ℝ) : Set AsymptoticCylinder.Cylinder := {z | ε≤z.2}

theorem region_measurable (ε : ℝ) : MeasurableSet (region ε) :=
  measurableSet_Ici.preimage measurable_snd

noncomputable def projection (ε : ℝ) : AsymptoticCylinder.Space →L[ℂ] AsymptoticCylinder.Space :=
  AsymptoticRegionL2.projection AsymptoticCylinder.measure (region ε) (region_measurable ε)

noncomputable abbrev Space (ε : ℝ) :=
  AsymptoticRegionL2.Space AsymptoticCylinder.measure (region ε) (region_measurable ε)

noncomputable def hyperProjection (ε : ℝ) :
    AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space :=
  AsymptoticRegionL2.projection volume (AsymptoticCertificateOperators.highStrip ε)
    (AsymptoticCertificateOperators.highStrip_measurable ε)

theorem projection_coeFn (ε : ℝ) (f : AsymptoticCylinder.Space) :
    projection ε f =ᵐ[AsymptoticCylinder.measure] (region ε).indicator f :=
  AsymptoticRegionL2.projection_coeFn _ _ _ _

theorem projection_norm_le (ε : ℝ) : ‖projection ε‖≤1 :=
  AsymptoticRegionL2.projection_norm_le _ _ _

theorem projection_adjoint (ε : ℝ) : (projection ε).adjoint=projection ε :=
  AsymptoticRegionL2.projection_adjoint _ _ _

theorem hyperProjection_adjoint (ε : ℝ) : (hyperProjection ε).adjoint=hyperProjection ε :=
  AsymptoticRegionL2.projection_adjoint _ _ _

/-- The cylinder-to-strip isometry intertwines the actual terminal
restrictions, including their boundary convention. -/
theorem lift_projection (ε : ℝ) (f : AsymptoticCylinder.Space) :
    lift (projection ε f)=hyperProjection ε (lift f) := by
  apply Lp.ext
  filter_upwards [lift_coeFn_of_ae _ _ (projection_coeFn ε f),
    AsymptoticRegionL2.projection_coeFn volume (AsymptoticCertificateOperators.highStrip ε)
      (AsymptoticCertificateOperators.highStrip_measurable ε) (lift f),lift_coeFn f]
    with z hl hp hf
  change hyperProjection ε (lift f) z=(AsymptoticCertificateOperators.highStrip ε).indicator (lift f) z at hp
  rw [hl,hp]
  classical
  by_cases hs : z∈AsymptoticMassTransport.strip
  · by_cases hy : ε≤z.im
    · have hc : cylinder z∈region ε := hy
      have hh : z∈AsymptoticCertificateOperators.highStrip ε := ⟨hs,hy⟩
      rw [Set.indicator_of_mem hs,Set.indicator_of_mem hc,Set.indicator_of_mem hh,hf,
        Set.indicator_of_mem hs]
    · have hc : cylinder z∉region ε := hy
      have hh : z∉AsymptoticCertificateOperators.highStrip ε := fun h => hy h.2
      rw [Set.indicator_of_mem hs,Set.indicator_of_notMem hc,Set.indicator_of_notMem hh,mul_zero]
  · have hh : z∉AsymptoticCertificateOperators.highStrip ε := fun h => hs h.1
    rw [Set.indicator_of_notMem hs,Set.indicator_of_notMem hh]

theorem adjoint_lift (f : AsymptoticCylinder.Space) :
    lift.toContinuousLinearMap.adjoint (lift f)=f := by
  exact congrArg (fun T : AsymptoticCylinder.Space →L[ℂ] AsymptoticCylinder.Space => T f)
    lift.adjoint_comp_self

theorem adjoint_projection (ε : ℝ) (u : AsymptoticHyperbolicSlash.Space) :
    projection ε (lift.toContinuousLinearMap.adjoint u)=
      lift.toContinuousLinearMap.adjoint (hyperProjection ε u) := by
  have he : lift.toContinuousLinearMap.comp (projection ε)=
      (hyperProjection ε).comp lift.toContinuousLinearMap := by
    ext1 f
    exact lift_projection ε f
  have hh := congrArg ContinuousLinearMap.adjoint he
  rw [adjoint_comp,adjoint_comp,projection_adjoint,hyperProjection_adjoint] at hh
  exact congrArg (fun T : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticCylinder.Space => T u) hh

/-- Changing the capped exponent leaves terminal restriction unchanged. -/
theorem projection_inclusion {ε : ℝ} (hε : 0<ε) (f : AsymptoticCylinder.Space) :
    projection ε (AsymptoticCylinder.inclusion hε f)=projection ε f := by
  apply Lp.ext
  filter_upwards [projection_coeFn ε (AsymptoticCylinder.inclusion hε f),
    projection_coeFn ε f,AsymptoticCylinder.inclusion_coeFn hε f] with z hz hf hw
  rw [hz,hf]
  classical
  by_cases hs : z∈region ε
  · rw [Set.indicator_of_mem hs,Set.indicator_of_mem hs,hw]
    have hh : ε≤z.2 := hs
    rw [AsymptoticCylinder.weight,min_eq_right ((one_le_div hε).mpr hh),Complex.ofReal_one,one_mul]
  · rw [Set.indicator_of_notMem hs,Set.indicator_of_notMem hs]

#print axioms lift_projection
#print axioms adjoint_lift
#print axioms adjoint_projection
#print axioms projection_inclusion

end AsymptoticCylinderTerminal
