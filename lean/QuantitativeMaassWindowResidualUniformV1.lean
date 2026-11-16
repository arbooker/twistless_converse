module

public import QuantitativeMaassWindowResidualMomentV1
public import QuantitativeMaassWindowShiftedMomentV1
public import QuantitativeMaassWindowTranslationV1

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace QuantitativeMaass

/-- The actual symmetric window has residual spectral moment O_K(t³ ε),
uniformly for smoothing scales at least one and widths at most one. -/
theorem symmetricWindow_residual_moment_uniform (K : SchwartzMap ℝ ℝ)
    (hK : ∀ x, 0 ≤ K x) (hm : (∫ x, K x) = 1)
    (R t ε : ℝ) (hR : 1 ≤ R) (ht : 1 ≤ t) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Integrable (fun r => (r^2-t^2)^2 * |r| *
      (smoothedWindow K R (Icc t (t+ε) ∪ Icc (-(t+ε)) (-t)) r)^2) ∧
    (∫ r, (r^2-t^2)^2 * |r| *
      (smoothedWindow K R (Icc t (t+ε) ∪ Icc (-(t+ε)) (-t)) r)^2) ≤
      (576 * (1 + ∫ x, |x|^5 * K x)) * t^3 * ε := by
  let S := Icc t (t+ε) ∪ Icc (-(t+ε)) (-t)
  have hS : IsCompact S := isCompact_Icc.union isCompact_Icc
  let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS.measure_ne_top
  have hband : ∀ u ∈ S, t ≤ |u| ∧ |u| ≤ t+1 := by
    intro u hu
    rcases hu with hu|hu
    · rw [abs_of_nonneg (by linarith [hu.1] : 0 ≤ u)]
      exact ⟨hu.1, by linarith [hu.2]⟩
    · rw [abs_of_nonpos (by linarith [hu.2] : u ≤ 0)]
      constructor <;> linarith [hu.1, hu.2]
  have h := smoothedWindow_residual_moment K hK hm R (by linarith) S
    hS.measurableSet t ht hband
  refine ⟨h.1, h.2.trans ?_⟩
  have hvol : (volume S).toReal = 2*ε := by
    have hv := symmetric_window_volume t (t+ε) (by linarith) (by linarith)
    change (volume S).toReal = _ at hv
    simpa only [add_sub_cancel_left] using hv
  rw [hvol]
  calc
    _ ≤ (18*t^3*(2*ε)) * (16*(1+∫ x, |x|^5*K x)) :=
      mul_le_mul_of_nonneg_left (scaledWindowKernel_fifth_shifted_uniform K hK hm R hR)
        (by positivity)
    _ = _ := by ring

#print axioms symmetricWindow_residual_moment_uniform

end QuantitativeMaass
