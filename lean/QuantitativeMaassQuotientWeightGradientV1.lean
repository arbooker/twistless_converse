module

public import QuantitativeMaassQuotientWeightDerivativeMeasureV1
public import AsymptoticL2MultiplierV1
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

set_option autoImplicit false
set_option maxHeartbeats 1400000
@[expose] public noncomputable section

open Filter MeasureTheory UpperHalfPlane AsymptoticClassicalPetersson

namespace QuantitativeMaass

/-- Actual height-scaled coordinate derivative of the orbit weight. -/
def quotientWeightGradientColumn (N : ℕ) (ε : ℝ) (v : ℕ) (i : Bool) (z : ℍ) : ℂ :=
  (z.im:ℂ)*(fderiv ℝ (quotientWeightPlane N ε v) (z.re,z.im)
    (if i then (1,0) else (0,1)):ℝ)

theorem quotientWeightGradientColumn_measurable (N : ℕ) (ε : ℝ) (v : ℕ) (i : Bool) :
    Measurable (quotientWeightGradientColumn N ε v i) := by
  unfold quotientWeightGradientColumn
  exact (Complex.measurable_ofReal.comp continuous_im.measurable).mul
    (Complex.measurable_ofReal.comp
      ((measurable_fderiv_apply_const ℝ (quotientWeightPlane N ε v)
        (if i then (1,0) else (0,1))).comp (continuous_re.measurable.prodMk continuous_im.measurable)))

theorem quotientWeightGradientColumn_bound (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (i : Bool) (z : ℍ) :
    ‖quotientWeightGradientColumn N ε v i z‖≤4*quotientWeightBound ε*(2*v:ℝ) := by
  have hd := (fderiv ℝ (quotientWeightPlane N ε v) (z.re,z.im)).le_opNorm
    (if i then (1,0) else (0,1))
  have hi : ‖(if i then (1,0) else (0,1):ℝ×ℝ)‖=1 := by cases i <;> simp
  rw [hi,mul_one] at hd
  unfold quotientWeightGradientColumn
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos z.im_pos,Complex.norm_real]
  exact (mul_le_mul_of_nonneg_left hd z.im_pos.le).trans
    (quotientWeightPlane_derivative_bound N hε hv (z.re,z.im) z.im_pos)

def quotientWeightGradientMultiplier (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (i : Bool) :
    Lp ℂ 2 (quotientMeasure N) →L[ℂ] Lp ℂ 2 (quotientMeasure N) :=
  AsymptoticL2Multiplier.operator (quotientWeightGradientColumn N ε v i)
    (quotientWeightGradientColumn_measurable N ε v i).aestronglyMeasurable
    (Eventually.of_forall (quotientWeightGradientColumn_bound N hε hv i))

theorem quotientWeightGradientMultiplier_norm (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (i : Bool) :
    ‖quotientWeightGradientMultiplier N hε hv i‖≤4*quotientWeightBound ε*(2*v:ℝ) :=
  AsymptoticL2Multiplier.operator_norm_le _ _
    (mul_nonneg (mul_nonneg (by norm_num) (quotientWeightBound_nonneg ε)) (by positivity)) _

#print axioms quotientWeightGradientColumn_measurable
#print axioms quotientWeightGradientColumn_bound
#print axioms quotientWeightGradientMultiplier_norm

end QuantitativeMaass
