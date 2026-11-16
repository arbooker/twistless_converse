module

public import QuantitativeMaassShiftedWaveScalarV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace QuantitativeMaass.Wave

theorem signedCosine_jointlyContinuous :
    Continuous (fun p : ℝ × ℝ => signedCosine p.1 p.2) := by
  unfold signedCosine
  fun_prop

/-- Joint continuity includes the oscillatory endpoint of inverse energy. -/
theorem shiftedDampedCosine_jointlyContinuous :
    Continuous (fun p : ℝ × ℝ => shiftedDampedCosine p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hs : p.2 = 0
  · have hz : shiftedDampedCosine p.1 p.2 = 0 := by simp [hs, shiftedDampedCosine]
    change Tendsto (fun q : ℝ × ℝ => shiftedDampedCosine q.1 q.2)
      (𝓝 p) (𝓝 (shiftedDampedCosine p.1 p.2))
    rw [hz]
    apply squeeze_zero_norm (fun q : ℝ × ℝ => shiftedDampedCosine_norm_le q.1 q.2)
    have hc : Continuous (fun q : ℝ × ℝ => Real.cosh (|q.1|/2) * ‖q.2‖) := by fun_prop
    simpa only [hs, norm_zero, mul_zero] using hc.continuousAt (x := p) |>.tendsto
  · change ContinuousAt (fun q : ℝ × ℝ => q.2 *
      signedCosine q.1 (max (q.2⁻¹-1) 0-1/4)) p
    have hi : ContinuousAt (fun q : ℝ × ℝ => q.2⁻¹) p := continuousAt_snd.inv₀ hs
    have hm : ContinuousAt (fun q : ℝ × ℝ => max (q.2⁻¹-1) 0-1/4) p :=
      ((hi.sub continuousAt_const).max continuousAt_const).sub continuousAt_const
    have hj := signedCosine_jointlyContinuous.continuousAt.comp
      (continuousAt_fst.prodMk hm)
    exact continuousAt_snd.mul hj

#print axioms shiftedDampedCosine_jointlyContinuous

end QuantitativeMaass.Wave
