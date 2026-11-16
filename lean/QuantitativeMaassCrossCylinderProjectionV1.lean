module

public import QuantitativeArithmeticMaassCanonicalCutoffTransferV1

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticClassicalPetersson

namespace QuantitativeMaass

/-- Cylinder projection onto the same closed rectangle does not alter
its actual local restriction. The boundary measure identity is explicit. -/
theorem quotientRestriction_cylinder_project (a b : ℝ) (ha : 0 < a)
    (v : Lp ℂ 2 (quotientMeasure 0)) :
    let S := upperRectangle 0 1 a b
    let hS := upperRectangle_compact 0 1 a b ha
    let P := AsymptoticRegionL2.projection (quotientMeasure 0) S hS.measurableSet
    quotientRestriction 0 S hS hS.measurableSet (cylinderAutomorphic (P v)) =
      quotientRestriction 0 S hS hS.measurableSet (cylinderAutomorphic v) := by
  intro S hS P
  have hle : volume.restrict S ≤ quotientMeasure 0 := by
    rw [← cylinder_rectangle_measure a b ha]
    exact Measure.restrict_le_self
  apply Lp.ext
  filter_upwards [quotientRestriction_cylinder_rectangle a b ha (P v),
    quotientRestriction_cylinder_rectangle a b ha v,
    (AsymptoticRegionL2.projection_coeFn (quotientMeasure 0) S hS.measurableSet v).filter_mono
      (ae_mono hle),ae_restrict_mem hS.measurableSet] with z hp hv he hz
  rw [hp,hv,he,Set.indicator_of_mem hz]

/-- The spatial projection is inserted at the input of the compact
transfer, without moving it past a wave packet or an ambient filter. -/
theorem crossQuotientLocalization_cylinder_project (N : ℕ)
    (a b : ℝ) (ha : 0 < a) (u : SmoothUpperSeed) {B : ℝ}
    (hu : ∀ z ∈ upperRectangle 0 1 a b, ‖upperFunction u.toFun z‖ ≤ B)
    (v : Lp ℂ 2 (quotientMeasure 0)) :
    let S := upperRectangle 0 1 a b
    let hS := upperRectangle_compact 0 1 a b ha
    let P := AsymptoticRegionL2.projection (quotientMeasure 0) S hS.measurableSet
    let T := crossQuotientLocalization N 0 S hS u hu
    T (cylinderAutomorphic (P v)) = T (cylinderAutomorphic v) := by
  intro S hS P T
  have hh := quotientRestriction_cylinder_project a b ha v
  change quotientRestriction 0 S hS hS.measurableSet (cylinderAutomorphic (P v)) =
    quotientRestriction 0 S hS hS.measurableSet (cylinderAutomorphic v) at hh
  dsimp only [T,crossQuotientLocalization,comp_apply]
  rw [hh]

#print axioms quotientRestriction_cylinder_project
#print axioms crossQuotientLocalization_cylinder_project

end QuantitativeMaass
