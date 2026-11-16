module

public import QuantitativeMaassAbelOperatorBoundV1
public import QuantitativeMaassRadialKernelLinearV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem support_sub_Iic (F G : ℝ → ℂ) (B : ℝ)
    (hF : Function.support F⊆Iic B) (hG : Function.support G⊆Iic B) :
    Function.support (fun q => F q-G q)⊆Iic B := by
  intro q hq
  by_contra hn
  have hf : F q=0 := by by_contra h;exact hn (hF h)
  have hg : G q=0 := by by_contra h;exact hn (hG h)
  exact hq (by dsimp only;rw [hf,hg,sub_self])

theorem abelProfile_sub (F G : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G) (q : ℝ) :
    abelProfile (fun v => F v-G v) q=abelProfile F q-abelProfile G q := by
  have hd : deriv (fun v => F v-G v)=(fun v => deriv F v-deriv G v) := by
    funext v
    exact deriv_sub (hF.differentiable (by simp) v) (hG.differentiable (by simp) v)
  simp only [abelProfile,hd,abelIntegral]
  rw [integral_sub
    (quadratic_integrable (deriv F) (contDiff_infty_iff_deriv.mp hF).2.continuous hcF.deriv q).integrableOn
    (quadratic_integrable (deriv G) (contDiff_infty_iff_deriv.mp hG).2.continuous hcG.deriv q).integrableOn]
  ring

/-- Subtraction of test functions is literal subtraction of the constructed
quotient operators; both integral interchanges use proved integrability. -/
theorem abelKernelOperator_sub (N : ℕ) [NeZero N]
    (F G : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (R : ℝ) (hR : 0≤R) (hsF : Function.support F⊆Iic (Real.cosh R))
    (hsG : Function.support G⊆Iic (Real.cosh R)) :
    abelKernelOperator N (fun q => F q-G q) (hF.sub hG) (hcF.sub hcG) R hR
      (support_sub_Iic F G _ hsF hsG)=
        abelKernelOperator N F hF hcF R hR hsF-abelKernelOperator N G hG hcG R hR hsG := by
  apply ContinuousLinearMap.ext
  intro f
  have h := radialKernelOperator_linear N (abelProfile F) (abelProfile G)
    (abelProfile (fun q => F q-G q))
    (abelProfile_smooth F hF hcF) (abelProfile_smooth G hG hcG)
    (abelProfile_smooth _ (hF.sub hG) (hcF.sub hcG)) R hR
    (abelProfile_support F _ hsF) (abelProfile_support G _ hsG)
    (abelProfile_support _ _ (support_sub_Iic F G _ hsF hsG)) 1
    (fun q => by simpa only [one_mul] using abelProfile_sub F G hF hG hcF hcG q) f
  simpa only [one_smul,sub_apply,abelKernelOperator] using h

/-- Uniform first-derivative convergence of compact q-tests controls the
operator-norm difference, rather than merely pointwise kernel convergence. -/
theorem abelKernelOperator_sub_norm (N : ℕ) [NeZero N]
    (F G : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (R : ℝ) (hR : 0≤R) (hsF : Function.support F⊆Iic (Real.cosh R))
    (hsG : Function.support G⊆Iic (Real.cosh R))
    (C : ℝ) (hb : ∀ q,‖deriv F q-deriv G q‖≤C) :
    ‖abelKernelOperator N F hF hcF R hR hsF-abelKernelOperator N G hG hcG R hR hsG‖≤
      2*Real.pi*((Real.sqrt 2/Real.pi)*(C*(Real.cosh R+1))*(Real.cosh R-1)) := by
  rw [← abelKernelOperator_sub N F G hF hG hcF hcG R hR hsF hsG]
  apply abelKernelOperator_derivative_bound
  intro q
  have hd : deriv (fun v => F v-G v) q=deriv F q-deriv G q :=
    deriv_sub (hF.differentiable (by simp) q) (hG.differentiable (by simp) q)
  rw [hd]
  exact hb q

#print axioms abelProfile_sub
#print axioms abelKernelOperator_sub
#print axioms abelKernelOperator_sub_norm

end QuantitativeMaass
