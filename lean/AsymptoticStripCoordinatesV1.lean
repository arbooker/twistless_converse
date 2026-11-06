module

public import AsymptoticCylinderV1
public import AsymptoticMassTransportV1
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

set_option autoImplicit false
@[expose] public section

namespace AsymptoticStripCoordinates

open MeasureTheory UpperHalfPlane Set

/-- Flat area on the upper half-plane, before the factor y⁻². -/
noncomputable def flat : Measure ℍ := (volume : Measure ℂ).comap UpperHalfPlane.coe

noncomputable def flatStrip : Measure ℍ := flat.restrict AsymptoticMassTransport.strip

def coordinates (z : ℍ) : ℝ×ℝ := (z.re,z.im)

def cylinder (z : ℍ) : AsymptoticCylinder.Cylinder := ((z.re:AddCircle (1:ℝ)),z.im)

theorem coordinates_image : coordinates '' AsymptoticMassTransport.strip=
    Ico (0:ℝ) 1 ×ˢ Ioi (0:ℝ) := by
  ext p
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨hz,z.im_pos⟩
  · intro hp
    exact ⟨⟨⟨p.1,p.2⟩,hp.2⟩,hp.1,rfl⟩

theorem coordinates_preserving : MeasurePreserving coordinates flatStrip
    ((volume.restrict (Ico (0:ℝ) 1)).prod (volume.restrict (Ioi (0:ℝ)))) := by
  have hc : MeasurePreserving UpperHalfPlane.coe flat
      ((volume : Measure ℂ).restrict (Set.range UpperHalfPlane.coe)) :=
    ⟨measurable_coe,measurableEmbedding_coe.map_comap _⟩
  have hs := hc.restrict_image_emb measurableEmbedding_coe AsymptoticMassTransport.strip
  rw [Measure.restrict_restrict' measurableEmbedding_coe.measurableSet_range,
    inter_eq_self_of_subset_left (Set.image_subset_range _ _)] at hs
  have hp := Complex.volume_preserving_equiv_real_prod.restrict_image_emb
    Complex.measurableEquivRealProd.measurableEmbedding (UpperHalfPlane.coe '' AsymptoticMassTransport.strip)
  have h := hp.comp hs
  have himage : Complex.measurableEquivRealProd '' (UpperHalfPlane.coe '' AsymptoticMassTransport.strip)=
      Ico (0:ℝ) 1 ×ˢ Ioi (0:ℝ) := by
    rw [Set.image_image]
    exact coordinates_image
  rw [himage] at h
  change MeasurePreserving coordinates (flat.restrict AsymptoticMassTransport.strip)
    ((volume : Measure (ℝ×ℝ)).restrict (Ico (0:ℝ) 1 ×ˢ Ioi (0:ℝ))) at h
  simpa only [flatStrip,Measure.volume_eq_prod,Measure.prod_restrict] using h

theorem circle_preserving : MeasurePreserving (fun x : ℝ => (x:AddCircle (1:ℝ)))
    (volume.restrict (Ico (0:ℝ) 1)) (AddCircle.haarAddCircle (T:=1)) := by
  have h := UnitAddCircle.measurePreserving_mk 0
  rw [show (0:ℝ)+1=1 by ring,← restrict_Ico_eq_restrict_Ioc] at h
  simpa only [AddCircle.volume_eq_smul_haarAddCircle,ENNReal.ofReal_one,one_smul] using h

/-- The actual translation quotient preserves flat area on the strip. -/
theorem cylinder_preserving : MeasurePreserving cylinder flatStrip AsymptoticCylinder.measure := by
  have h := (circle_preserving.prod (MeasurePreserving.id (volume.restrict (Ioi (0:ℝ))))).comp
    coordinates_preserving
  exact h

theorem cylinder_continuous : Continuous cylinder := by
  unfold cylinder
  fun_prop

#print axioms coordinates_preserving
#print axioms cylinder_preserving

end AsymptoticStripCoordinates
