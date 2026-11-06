module

public import AsymptoticCylinderLiftV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticStripCoordinates

open MeasureTheory UpperHalfPlane Set Filter

/-- A measurable representative of the cylinder in the translation strip.
The value at nonpositive heights is irrelevant for cylinder area. -/
noncomputable def cylinderSection (w : AsymptoticCylinder.Cylinder) : ℍ :=
  ⟨⟨(AddCircle.measurableEquivIco (T:=1) 0 w.1).val,if 0<w.2 then w.2 else 1⟩,by
    split_ifs with h
    · exact h
    · norm_num⟩

theorem section_measurable : Measurable cylinderSection := by
  apply measurableEmbedding_coe.measurable_comp_iff.mp
  change Measurable (fun w : AsymptoticCylinder.Cylinder =>
    (⟨(AddCircle.measurableEquivIco (T:=1) 0 w.1).val,if 0<w.2 then w.2 else 1⟩:ℂ))
  have hx := measurable_subtype_coe.comp ((AddCircle.measurableEquivIco (T:=1) 0).measurable.comp
    (measurable_fst : Measurable (Prod.fst : AsymptoticCylinder.Cylinder → AddCircle (1:ℝ))))
  have hy : Measurable (fun w : AsymptoticCylinder.Cylinder => if 0<w.2 then w.2 else 1) :=
    measurable_snd.ite (measurableSet_lt measurable_const measurable_snd) measurable_const
  exact Complex.measurableEquivRealProd.symm.measurable.comp (hx.prodMk hy)

theorem section_cylinder (z : ℍ) (hz : z∈AsymptoticMassTransport.strip) : cylinderSection (cylinder z)=z := by
  apply UpperHalfPlane.ext
  apply Complex.ext
  · change (AddCircle.equivIco (1:ℝ) 0 (z.re:AddCircle (1:ℝ))).val=z.re
    exact AddCircle.equivIco_coe_of_mem ⟨hz.1,by simpa only [zero_add] using hz.2⟩
  · change (if 0<z.im then z.im else 1)=z.im
    exact ite_eq_left z.im_pos

theorem section_preserving : MeasurePreserving cylinderSection AsymptoticCylinder.measure flatStrip := by
  refine ⟨section_measurable,?_⟩
  rw [← cylinder_preserving.map_eq,Measure.map_map section_measurable cylinder_continuous.measurable]
  have he : cylinderSection ∘ cylinder =ᵐ[flatStrip] id :=
    (ae_restrict_mem AsymptoticMassTransport.strip_measurable).mono (fun z hz => section_cylinder z hz)
  rw [Measure.map_congr he,Measure.map_id]

#print axioms section_measurable
#print axioms section_cylinder
#print axioms section_preserving

end AsymptoticStripCoordinates

namespace AsymptoticCylinderLift

open MeasureTheory Filter AsymptoticStripCoordinates

/-- Every flat L² function on the strip comes from a cylinder L² function. -/
theorem pullback_surjective : Function.Surjective pullback := by
  intro f
  let g := Lp.compMeasurePreserving cylinderSection section_preserving f
  refine ⟨g,?_⟩
  apply Lp.ext
  have hg := cylinder_preserving.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving f section_preserving)
  filter_upwards [Lp.coeFn_compMeasurePreserving g cylinder_preserving,hg,
    ae_restrict_mem AsymptoticMassTransport.strip_measurable] with z hp hs hz
  change Lp.compMeasurePreserving cylinder cylinder_preserving g z=f z
  rw [hp]
  change Lp.compMeasurePreserving cylinderSection section_preserving f (cylinder z)=f z
  rw [hs,Function.comp_apply,section_cylinder z hz]

#print axioms pullback_surjective

end AsymptoticCylinderLift
