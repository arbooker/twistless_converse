module

public import QuantitativeMaassAbelOffDiagonalTimeV1

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The actual one-sided Abel profile is linear, including at its physical
endpoint. Derivatives are evaluated strictly above one almost everywhere. -/
theorem abelProfile_linear_physical (F G : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ici 1)) (hG : ContDiffOn ℝ ∞ G (Ici 1))
    (B : ℝ) (hB : 1 ≤ B) (hsF : Function.support F ⊆ Iic B)
    (hsG : Function.support G ⊆ Iic B) (a b : ℂ) (q : ℝ) (hq : 1 ≤ q) :
    abelProfile (fun x => a*F x+b*G x) q = a*abelProfile F q+b*abelProfile G q := by
  have hiF := physical_quadratic_derivative_integrable F hF B hB hsF q hq
  have hiG := physical_quadratic_derivative_integrable G hG B hB hsG q hq
  have hd (x : ℝ) (hx : 1 < x) :
      deriv (fun y => a*F y+b*G y) x = a*deriv F x+b*deriv G x := by
    have hf := ((hF x hx.le).contDiffAt (Ici_mem_nhds hx)).differentiableAt (by simp)
    have hg := ((hG x hx.le).contDiffAt (Ici_mem_nhds hx)).differentiableAt (by simp)
    exact ((hf.hasDerivAt.const_mul a).add (hg.hasDerivAt.const_mul b)).deriv
  have he : (∫ s in Ioi (0 : ℝ), deriv (fun x => a*F x+b*G x) (q+s^2)) =
      ∫ s in Ioi (0 : ℝ), a*deriv F (q+s^2)+b*deriv G (q+s^2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    exact hd _ (by have hs0 : 0 < s := hs; nlinarith [sq_pos_of_pos hs0])
  simp only [abelProfile, abelIntegral]
  rw [he, integral_add (hiF.const_mul a) (hiG.const_mul b),
    integral_const_mul, integral_const_mul]
  ring

#print axioms abelProfile_linear_physical

end QuantitativeMaass
