module

public import QuantitativeMaassCylinderMeanMultiplierV1
public import QuantitativeMaassConjugatedColumnsV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticClassicalPetersson

namespace QuantitativeMaass

/-- Each bounded inverse height band preserves all local horizontal means. -/
theorem cylinderNonzeroModes_inverse_band (l : ℝ → ℝ) (hl : Measurable l) (n : ℤ)
    (v : Lp ℂ 2 (quotientMeasure 0)) (hv : v∈cylinderNonzeroModes) :
    LogBands.inverse (quotientMeasure 0) (fun z => l z.im)
      (hl.comp continuous_im.measurable) n v∈cylinderNonzeroModes := by
  have hr (y : ℝ) : star (LogBands.inverseCoefficient l n y)=LogBands.inverseCoefficient l n y := by
    classical
    by_cases hy : y∈LogBands.region l n
    · simp only [LogBands.inverseCoefficient,Set.indicator_of_mem hy,Complex.star_def,Complex.conj_ofReal]
    · simp only [LogBands.inverseCoefficient,Set.indicator_of_notMem hy,star_zero]
  exact cylinderNonzeroModes_multiplier (LogBands.inverseCoefficient l n)
    (LogBands.inverseCoefficient_measurable l hl n) (Real.exp (-(n:ℝ)))
    (LogBands.inverseCoefficient_bound l n) hr hv

/-- Finite inverse rows used in the capped column do not reintroduce a
horizontal constant mode. -/
theorem cylinderNonzeroModes_inverse_row (l : ℝ → ℝ) (hl : Measurable l) (J : ℕ) (n : ℤ)
    (v : Lp ℂ 2 (quotientMeasure 0)) (hv : v∈cylinderNonzeroModes) :
    LogBands.rowInverseSum (quotientMeasure 0) (fun z => l z.im)
      (hl.comp continuous_im.measurable) J n v∈cylinderNonzeroModes := by
  classical
  simp only [LogBands.rowInverseSum,sum_apply]
  apply Submodule.sum_mem
  intro m _
  exact cylinderNonzeroModes_inverse_band l hl m v hv

#print axioms cylinderNonzeroModes_inverse_band
#print axioms cylinderNonzeroModes_inverse_row

end QuantitativeMaass
