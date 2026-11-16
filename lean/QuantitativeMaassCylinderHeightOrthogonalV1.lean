module

public import QuantitativeMaassCylinderRectangleMeasureV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology

namespace QuantitativeMaass

/-- Actual nonzero-mode cylinder vectors annihilate every compact local
height test, with the pairing written as a literal hyperbolic integral. -/
theorem cylinderNonzeroModes_height_pairing_zero (a b : ℝ) (ha : 0<a)
    (h : ℝ → ℂ) (hh : Continuous h) (v : Lp ℂ 2 (quotientMeasure 0))
    (hv : v∈cylinderNonzeroModes) :
    (∫ z in upperRectangle 0 1 a b,star (h z.im)*v z)=0 := by
  have hz : cylinderLocalMean a b ha v=0 := by
    simp only [cylinderNonzeroModes,Submodule.mem_iInf,LinearMap.mem_ker] at hv
    exact hv a b ha
  have hp := localHeightAverage_test (upperRectangle 0 1 a b)
    (upperRectangle_compact 0 1 a b ha) h hh
    (cuspRestriction 0 1 (upperRectangle 0 1 a b) (upperRectangle_compact 0 1 a b ha)
      (cylinderAutomorphic v))
  change inner ℂ (heightTestVector _ _ h hh) (cylinderLocalMean a b ha v)=_ at hp
  rw [hz,inner_zero_right] at hp
  rw [hp]
  apply integral_congr_ae
  filter_upwards [cylinder_rectangle_restriction a b ha v] with z hz
  rw [hz]

/-- Any literal height column supported in a compact cylinder rectangle
is orthogonal to the entire closed nonzero-mode space. -/
theorem cylinderNonzeroModes_height_inner_zero (a b : ℝ) (ha : 0<a)
    (h : ℝ → ℂ) (hh : Continuous h) (c v : Lp ℂ 2 (quotientMeasure 0))
    (hc : c=ᵐ[quotientMeasure 0] (upperRectangle 0 1 a b).indicator (fun z => h z.im))
    (hv : v∈cylinderNonzeroModes) : inner ℂ c v=0 := by
  have he : inner ℂ c v=
      ∫ z in upperRectangle 0 1 a b,star (h z.im)*v z ∂quotientMeasure 0 := by
    rw [L2.inner_def,←integral_indicator (upperRectangle_measurable 0 1 a b)]
    apply integral_congr_ae
    filter_upwards [hc] with z hz
    change v z*star (c z)=_
    rw [hz]
    classical
    by_cases hK : z∈upperRectangle 0 1 a b
    · simp only [Set.indicator_of_mem hK,mul_comm]
    · simp only [Set.indicator_of_notMem hK,star_zero,mul_zero]
  rw [he,cylinder_rectangle_measure a b ha]
  exact cylinderNonzeroModes_height_pairing_zero a b ha h hh v hv

#print axioms cylinderNonzeroModes_height_pairing_zero
#print axioms cylinderNonzeroModes_height_inner_zero

end QuantitativeMaass
