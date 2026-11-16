module
public import QuantitativeArithmeticMaassHeightProfileV1
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Complex.RealDeriv
set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace QuantitativeArithmeticMaassModularHeight

/-- Smooth truncation of the logarithmic slope, with transitions in [2,3]
and [R-1,R]. The quotient at zero is harmless since the numerator vanishes
on an entire neighborhood. -/
def logSlope (R y : ℝ) : ℝ :=
  Real.smoothTransition (y-2)*Real.smoothTransition (R-y)/y

theorem logSlope_zero_low (R : ℝ) {y : ℝ} (hy : y≤2) : logSlope R y=0 := by
  simp [logSlope,Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hy)]

theorem logSlope_zero_high (R : ℝ) {y : ℝ} (hy : R≤y) : logSlope R y=0 := by
  simp [logSlope,Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hy)]

theorem logSlope_smooth (R : ℝ) : ContDiff ℝ ∞ (logSlope R) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y<2
  · apply ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0:ℝ)))
    filter_upwards [gt_mem_nhds hy] with t ht
    exact logSlope_zero_low R ht.le
  · have hne : y≠0 := by linarith
    exact ((Real.smoothTransition.contDiffAt.comp y
      (contDiffAt_id.sub contDiffAt_const)).mul
      (Real.smoothTransition.contDiffAt.comp y
        (contDiffAt_const.sub contDiffAt_id))).div contDiffAt_id hne

theorem logSlope_nonneg (R y : ℝ) : 0≤logSlope R y := by
  by_cases hy : y≤2
  · rw [logSlope_zero_low R hy]
  · exact div_nonneg (mul_nonneg (Real.smoothTransition.nonneg _)
      (Real.smoothTransition.nonneg _)) (by linarith)

theorem logSlope_le_one (R y : ℝ) : logSlope R y≤1 := by
  by_cases hy : y≤2
  · rw [logSlope_zero_low R hy]; norm_num
  · have hm : Real.smoothTransition (y-2)*Real.smoothTransition (R-y)≤1 :=
      (mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _)
        (Real.smoothTransition.nonneg _)).trans (by simpa using Real.smoothTransition.le_one (R-y))
    exact (div_le_one (by linarith : 0<y)).mpr (by linarith)

theorem logSlope_scaled (R : ℝ) {y : ℝ} (hy : 0<y) :
    0≤y*logSlope R y ∧ y*logSlope R y≤1 := by
  have he : y*logSlope R y=
      Real.smoothTransition (y-2)*Real.smoothTransition (R-y) := by
    unfold logSlope
    field_simp
  rw [he]
  exact ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),
    (mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _)
      (Real.smoothTransition.nonneg _)).trans (by simpa using Real.smoothTransition.le_one (R-y))⟩

theorem logSlope_eq_inv (R : ℝ) {y : ℝ} (hy : 3≤y) (hR : y≤R-1) :
    logSlope R y=y⁻¹ := by
  simp [logSlope,Real.smoothTransition.one_of_one_le (show 1≤y-2 by linarith),
    Real.smoothTransition.one_of_one_le (show 1≤R-y by linarith)]

/-- A bounded smooth primitive that is exactly logarithmic away from its
two transition regions. -/
def truncatedLog (R y : ℝ) : ℝ := ∫ t in 0..y, logSlope R t

theorem truncatedLog_hasDerivAt (R y : ℝ) :
    HasDerivAt (truncatedLog R) (logSlope R y) y := by
  have hc := (logSlope_smooth R).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem truncatedLog_smooth (R : ℝ) : ContDiff ℝ ∞ (truncatedLog R) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun y => (truncatedLog_hasDerivAt R y).differentiableAt,?_⟩
  have he : deriv (truncatedLog R)=logSlope R :=
    funext fun y => (truncatedLog_hasDerivAt R y).deriv
  rw [he]
  exact logSlope_smooth R

theorem truncatedLog_zero (R : ℝ) {y : ℝ} (hy : y≤2) : truncatedLog R y=0 := by
  unfold truncatedLog
  calc
    (∫ t in 0..y, logSlope R t) = ∫ _t in (0:ℝ)..y, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact logSlope_zero_low R (ht.2.trans (max_le (by norm_num) hy))
    _ = 0 := by simp

theorem truncatedLog_monotone (R : ℝ) : Monotone (truncatedLog R) :=
  monotone_of_deriv_nonneg (fun y => (truncatedLog_hasDerivAt R y).differentiableAt)
    (fun y => by rw [(truncatedLog_hasDerivAt R y).deriv];exact logSlope_nonneg R y)

theorem truncatedLog_nonneg (R y : ℝ) : 0≤truncatedLog R y := by
  by_cases hy : y≤2
  · rw [truncatedLog_zero R hy]
  · have hm := truncatedLog_monotone R (show (0:ℝ)≤y by linarith)
    simpa [truncatedLog] using hm

theorem truncatedLog_sub (R a b : ℝ) :
    truncatedLog R b-truncatedLog R a=∫ t in a..b, logSlope R t := by
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => truncatedLog_hasDerivAt R t)
    ((logSlope_smooth R).continuous.intervalIntegrable _ _)).symm

theorem truncatedLog_constant (R : ℝ) {y : ℝ} (hy : R≤y) :
    truncatedLog R y=truncatedLog R R := by
  apply sub_eq_zero.mp
  rw [truncatedLog_sub]
  calc
    (∫ t in R..y, logSlope R t) = ∫ _t in R..y, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : R≤t ∧ t≤y := by simpa only [uIcc_of_le hy,mem_Icc] using ht
      exact logSlope_zero_high R ht'.1
    _ = 0 := by simp

theorem truncatedLog_bound (R : ℝ) (hR : 0≤R) (y : ℝ) : truncatedLog R y≤R := by
  have he : truncatedLog R y≤truncatedLog R R := by
    rcases le_total y R with hy | hy
    · exact truncatedLog_monotone R hy
    · exact (truncatedLog_constant R hy).le
  apply he.trans
  have hi := intervalIntegral.integral_mono (μ := volume) hR
    ((logSlope_smooth R).continuous.intervalIntegrable 0 R)
    (continuous_const.intervalIntegrable 0 R) (logSlope_le_one R)
  simpa [truncatedLog] using hi

/-- Exact logarithmic separation, with no loss in wave propagation speed. -/
theorem truncatedLog_sub_eq_log (R : ℝ) {a b : ℝ} (ha : 3≤a)
    (hab : a≤b) (hb : b≤R-1) :
    truncatedLog R b-truncatedLog R a=Real.log (b/a) := by
  rw [truncatedLog_sub]
  calc
    (∫ t in a..b, logSlope R t) = ∫ t in a..b, t⁻¹ := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : a≤t ∧ t≤b := by simpa [uIcc_of_le hab] using ht
      exact logSlope_eq_inv R (ha.trans ht'.1) (ht'.2.trans hb)
    _ = Real.log (b/a) := integral_inv_of_pos (by linarith) (by linarith)

/-- Explicit bounded smooth invariant logarithmic cutoff at every level.
Its hyperbolic gradient bound is exactly one, independent of R and N. -/
def logarithmicCuspCutoff (N : ℕ) (R : ℝ) (hR : 0≤R) :
    QuantitativeMaass.Weighted.Cutoff N :=
  cuspCutoff N (fun y => (truncatedLog R y : ℂ))
    (fun y hy => by simp [truncatedLog_zero R hy])
    (Complex.ofRealCLM.contDiff.comp (truncatedLog_smooth R))
    (fun y => by simp) R hR
    (fun y => by simpa [Real.norm_eq_abs,abs_of_nonneg (truncatedLog_nonneg R y)]
      using truncatedLog_bound R hR y) 1
    (fun y hy => by
      rw [(truncatedLog_hasDerivAt R y).ofReal_comp.deriv]
      simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs,one_pow]
      have hh := logSlope_scaled R hy
      nlinarith [sq_nonneg (y*logSlope R y),sq_nonneg (1-y*logSlope R y)])

#print axioms truncatedLog_smooth
#print axioms truncatedLog_sub_eq_log
#print axioms logarithmicCuspCutoff
end QuantitativeArithmeticMaassModularHeight
