module

public import QuantitativeMaassWeightedEulerV1
public import Mathlib.Analysis.Normed.Operator.Prod

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

/-- The real differential with specified horizontal and vertical complex values. -/
def eulerGradient (a b : ℂ) : (ℝ × ℝ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight a +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight b

theorem eulerGradient_norm_le (a b : ℂ) : ‖eulerGradient a b‖≤‖a‖+‖b‖ := by
  unfold eulerGradient
  simpa only [ContinuousLinearMap.norm_smulRight_apply,ContinuousLinearMap.norm_fst,
    ContinuousLinearMap.norm_snd,one_mul] using norm_add_le
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight a)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight b)

/-- Both partial derivatives of each actual weighted summand, assembled as a
joint real Frechet derivative. -/
theorem principalWeightedTerm_hasFDerivAt (b : ℕ → ℂ) (r : ℝ) (j k σ n : ℕ)
    (z : ℝ × ℝ) (hz : 0<z.2) :
    HasFDerivAt (principalWeightedTerm b r j k σ n)
      (eulerGradient
        (((2*Real.pi:ℝ):ℂ)*Complex.I*principalWeightedTerm b r j (k+1) (σ+1) n z)
        (-((2*Real.pi:ℝ):ℂ)*principalWeightedTerm b r (j+1) (k+1) σ n z)) z := by
  have hpos : 0<2*Real.pi*((n+1:ℕ):ℝ)*z.2 := by positivity
  have hm := ((MaassKBessel.moment_hasDerivAt j r hpos).comp z.2
    ((hasDerivAt_id z.2).const_mul (2*Real.pi*((n+1:ℕ):ℝ)))).ofReal_comp
  have hp := eulerParityPhase_hasDerivAt σ (n+1) z.1
  have hh : HasFDerivAt (principalWeightedTerm b r j k σ n) _ z :=
    ((hm.hasFDerivAt.comp z hasFDerivAt_snd).const_mul
    (b (n+1)*((n+1:ℕ):ℂ)^k)).mul (hp.hasFDerivAt.comp z hasFDerivAt_fst)
  convert! hh using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [eulerGradient,principalWeightedTerm,ContinuousLinearMap.smulRight_apply,
    pow_succ,Complex.real_smul]
  ring

#print axioms eulerGradient_norm_le
#print axioms principalWeightedTerm_hasFDerivAt

end QuantitativeMaass
