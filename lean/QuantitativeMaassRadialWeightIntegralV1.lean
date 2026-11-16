module

public import QuantitativeMaassHyperbolicWeightsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The first radial weight has integrable square-root behavior at zero. -/
theorem inverse_sqrt_sinh_integral (δ L : ℝ) (hδ : 0<δ) (hL : δ≤L) :
    IntervalIntegrable (fun r => (Real.sqrt (Real.sinh r))⁻¹) volume δ L ∧
      (∫ r in δ..L,(Real.sqrt (Real.sinh r))⁻¹)≤2*Real.sqrt L := by
  have hpos (r : ℝ) (hr : r∈uIcc δ L) : 0<r := by
    rw [uIcc_of_le hL] at hr
    exact hδ.trans_le hr.1
  have hc : ContinuousOn (fun r => (Real.sqrt (Real.sinh r))⁻¹) (uIcc δ L) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro r hr
    exact (Real.sqrt_pos.mpr (Real.sinh_pos_iff.mpr (hpos r hr))).ne'
  have hi := hc.intervalIntegrable (μ:=volume)
  have hj0 := (inverse_sqrt_gap_integral 0 L (hδ.le.trans hL)).1
  simp only [sub_zero] at hj0
  have hj : IntervalIntegrable (fun r => (Real.sqrt r)⁻¹) volume δ L := hj0.mono_set (by rw [uIcc_of_le (hδ.le.trans hL),uIcc_of_le hL];exact Icc_subset_Icc hδ.le le_rfl)
  have hh := intervalIntegral.integral_mono_on hL hi hj (fun r hr => by
    apply inv_anti₀ (Real.sqrt_pos.mpr (hδ.trans_le hr.1))
    exact Real.sqrt_le_sqrt (Real.self_le_sinh_iff.mpr (hδ.le.trans hr.1)))
  have hm := intervalIntegral.integral_mono_interval hδ.le hL le_rfl
    (Eventually.of_forall (fun r => inv_nonneg.mpr (Real.sqrt_nonneg r))) hj0
  have he := (inverse_sqrt_gap_integral 0 L (hδ.le.trans hL)).2
  simp only [sub_zero] at he
  exact ⟨hi,hh.trans (hm.trans_eq he)⟩

/-- Exact primitive of the more singular radial derivative weight. -/
theorem cosh_inverse_sinh_sqrt_integral (δ L : ℝ) (hδ : 0<δ) (hL : δ≤L) :
    IntervalIntegrable (fun r => Real.cosh r/(Real.sinh r*Real.sqrt (Real.sinh r))) volume δ L ∧
      (∫ r in δ..L,Real.cosh r/(Real.sinh r*Real.sqrt (Real.sinh r)))=
        2/Real.sqrt (Real.sinh δ)-2/Real.sqrt (Real.sinh L) := by
  have hpos (r : ℝ) (hr : r∈uIcc δ L) : 0<r := by
    rw [uIcc_of_le hL] at hr
    exact hδ.trans_le hr.1
  have hc : ContinuousOn (fun r => Real.cosh r/(Real.sinh r*Real.sqrt (Real.sinh r))) (uIcc δ L) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro r hr
    exact mul_ne_zero (Real.sinh_pos_iff.mpr (hpos r hr)).ne'
      (Real.sqrt_pos.mpr (Real.sinh_pos_iff.mpr (hpos r hr))).ne'
  have hi := hc.intervalIntegrable (μ:=volume)
  have hd (r : ℝ) (hr : r∈uIcc δ L) :
      HasDerivAt (fun r => -2/Real.sqrt (Real.sinh r))
        (Real.cosh r/(Real.sinh r*Real.sqrt (Real.sinh r))) r := by
    have hs := Real.sinh_pos_iff.mpr (hpos r hr)
    have hsq := Real.sqrt_pos.mpr hs
    have hh := (((Real.hasDerivAt_sinh r).sqrt hs.ne').inv hsq.ne').const_mul (-2)
    change HasDerivAt (fun r => -2/Real.sqrt (Real.sinh r)) _ r at hh
    apply hh.congr_deriv
    have hsq2 := Real.sq_sqrt hs.le
    field_simp
    nlinarith
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  refine ⟨hi,hh.trans ?_⟩
  ring

/-- Its entire cutoff cost is at most two divided by sqrt(delta). -/
theorem cosh_inverse_sinh_sqrt_bound (δ L : ℝ) (hδ : 0<δ) (hL : δ≤L) :
    (∫ r in δ..L,Real.cosh r/(Real.sinh r*Real.sqrt (Real.sinh r)))≤2/Real.sqrt δ := by
  rw [(cosh_inverse_sinh_sqrt_integral δ L hδ hL).2]
  apply (sub_le_self _ (by positivity)).trans
  exact div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr hδ)
    (Real.sqrt_le_sqrt (Real.self_le_sinh_iff.mpr hδ.le))

#print axioms inverse_sqrt_sinh_integral
#print axioms cosh_inverse_sinh_sqrt_integral
#print axioms cosh_inverse_sinh_sqrt_bound

end QuantitativeMaass
