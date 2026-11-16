module

public import QuantitativeArithmeticMaassRectangleSmoothingV1

set_option autoImplicit false
set_option maxHeartbeats 400000
@[expose] public noncomputable section

open Set UpperHalfPlane AsymptoticMassTransport

namespace QuantitativeMaass

/-- The nonzero set of the smooth cutoff lies in the half-open strip,
even though its closed support may meet the right boundary. -/
theorem rectangleSmoothSeed_support_strip (a b h : ℝ) (ha : 0 < a) (hh : 0 < h) :
    Function.support (upperFunction (rectangleSmoothSeed 0 1 a b h ha hh).toFun) ⊆ strip := by
  intro z hz
  have hx : innerIntervalCutoff 0 1 h z.re ≠ 0 := by
    intro hn
    exact hz (by simp [rectangleSmoothSeed,upperFunction,rectangleCutoffFunction,hn])
  have hi := innerIntervalCutoff_support 0 1 h hh hx
  refine ⟨hi.1,?_⟩
  by_contra hn
  have hz' := Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith : 1-z.re ≤ 0) hh.le)
  exact hx (by simp [innerIntervalCutoff,hz'])

#print axioms rectangleSmoothSeed_support_strip

end QuantitativeMaass
