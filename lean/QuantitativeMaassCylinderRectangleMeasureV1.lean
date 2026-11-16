module

public import QuantitativeMaassCylinderRepresentativesV1
public import QuantitativeMaassCuspRectangleIntegralV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson AsymptoticMassTransport AsymptoticCongruenceStrip
open scoped Topology

namespace QuantitativeMaass

/-- A compact vertical edge has zero hyperbolic measure. -/
theorem upperRectangle_vertical_null (r a b : ℝ) (ha : 0<a) :
    volume (upperRectangle r r a b)=0 := by
  have hi : (∫ z in upperRectangle r r a b,(1:ℂ))=0 := by
    rw [integral_upperRectangle_iterated r r a b ha (fun _ => (1:ℂ)) continuous_const]
    simp
  have hm : (volume (upperRectangle r r a b)).toReal=0 := by
    simpa only [integral_const,measureReal_restrict_apply_univ,Complex.smul_re,
      Complex.one_re,smul_eq_mul,mul_one,Complex.zero_re,Measure.real,
      Measure.restrict_apply_univ] using congrArg Complex.re hi
  exact ((ENNReal.toReal_eq_zero_iff _).mp hm).resolve_right
    (upperRectangle_compact r r a b ha).measure_ne_top

/-- The closed unit rectangle lies in the half-open cylinder strip almost
everywhere; its right edge has zero genuine hyperbolic measure. -/
theorem upperRectangle_ae_strip (a b : ℝ) (ha : 0<a) :
    ∀ᵐ z ∂volume.restrict (upperRectangle 0 1 a b),z∈strip := by
  rw [ae_restrict_iff' (upperRectangle_measurable 0 1 a b)]
  have hz : ∀ᵐ z : ℍ ∂volume,z∉upperRectangle 1 1 a b := by
    rw [ae_iff]
    simpa only [not_not] using! upperRectangle_vertical_null 1 a b ha
  filter_upwards [hz] with z hz hK
  refine ⟨hK.1.1,?_⟩
  by_contra hn
  have he : z.re=1 := le_antisymm hK.1.2 (le_of_not_gt hn)
  exact hz ⟨⟨he.ge,he.le⟩,hK.2⟩

/-- Local closed rectangles have the same restricted measure in the
translation quotient and in the physical upper half-plane. -/
theorem cylinder_rectangle_measure (a b : ℝ) (ha : 0<a) :
    (quotientMeasure 0).restrict (upperRectangle 0 1 a b)=
      volume.restrict (upperRectangle 0 1 a b) := by
  rw [translation_quotient_measure,Measure.restrict_comm (upperRectangle_measurable 0 1 a b)]
  exact Measure.restrict_eq_self_of_ae_mem (upperRectangle_ae_strip a b ha)

/-- The actual local cusp restriction is the original cylinder L2 class
on the rectangle, with only a null boundary removed. -/
theorem cylinder_rectangle_restriction (a b : ℝ) (ha : 0<a)
    (v : Lp ℂ 2 (quotientMeasure 0)) :
    cuspRestriction 0 1 (upperRectangle 0 1 a b) (upperRectangle_compact 0 1 a b ha)
      (cylinderAutomorphic v)=ᵐ[volume.restrict (upperRectangle 0 1 a b)] v := by
  rw [←cylinderRepresentative_class v]
  have hh := cuspRestriction_representative_ae 0 1 (upperRectangle 0 1 a b)
    (upperRectangle_compact 0 1 a b ha) (cylinderRepresentative v)
  filter_upwards [hh,upperRectangle_ae_strip a b ha] with z hz hs
  simpa only [cuspAction,map_one,one_smul,cylinderRepresentative,cylinderFold_self hs] using! hz

#print axioms upperRectangle_vertical_null
#print axioms upperRectangle_ae_strip
#print axioms cylinder_rectangle_measure
#print axioms cylinder_rectangle_restriction

end QuantitativeMaass
