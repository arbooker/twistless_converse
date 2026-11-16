module

public import QuantitativeMaassCoshTestBoundV1
public import QuantitativeMaassAbelOperatorLinearV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem coshTestLift_sub (ψ θ : ℝ → ℂ) :
    coshTestLift (fun t => ψ t-θ t)=(fun q => coshTestLift ψ q-coshTestLift θ q) := by
  funext q
  unfold coshTestLift
  split_ifs <;> simp

theorem support_sub_interval (ψ θ : ℝ → ℂ) (δ R : ℝ)
    (hψ : Function.support ψ⊆Icc δ R) (hθ : Function.support θ⊆Icc δ R) :
    Function.support (fun t => ψ t-θ t)⊆Icc δ R := by
  intro t ht
  by_contra hn
  have hp : ψ t=0 := by by_contra h;exact hn (hψ h)
  have hq : θ t=0 := by by_contra h;exact hn (hθ h)
  exact ht (by dsimp only;rw [hp,hq,sub_self])

/-- Support-radius witnesses do not change the literal integral operator. -/
theorem abelKernelOperator_radius (N : ℕ) [NeZero N]
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (R S : ℝ) (hR : 0≤R) (hS : 0≤S)
    (hsR : Function.support F⊆Iic (Real.cosh R))
    (hsS : Function.support F⊆Iic (Real.cosh S)) :
    abelKernelOperator N F hF hc R hR hsR=abelKernelOperator N F hF hc S hS hsS := rfl

/-- On one fixed positive time interval, the difference of actual Abel
operators is bounded by the uniform first-derivative difference of the tests. -/
theorem positiveTimeAbelOperator_sub_norm (N : ℕ) [NeZero N]
    (ψ θ : PositiveTimeTest) (δ R C : ℝ) (hδ : 0<δ) (hR : 0≤R)
    (hsψ : Function.support ψ.toFun⊆Icc δ R) (hsθ : Function.support θ.toFun⊆Icc δ R)
    (hb : ∀ t,‖deriv ψ.toFun t-deriv θ.toFun t‖≤C) :
    ‖positiveTimeAbelOperator N ψ-positiveTimeAbelOperator N θ‖≤
      2*Real.pi*((Real.sqrt 2/Real.pi)*((C/Real.sinh δ)*(Real.cosh R+1))*(Real.cosh R-1)) := by
  have hsF : Function.support ψ.lift⊆Iic (Real.cosh R) :=
    fun _ h => (coshTestLift_support ψ.toFun δ R hδ hR hsψ h).2
  have hsG : Function.support θ.lift⊆Iic (Real.cosh R) :=
    fun _ h => (coshTestLift_support θ.toFun δ R hδ hR hsθ h).2
  have heψ : positiveTimeAbelOperator N ψ=
      abelKernelOperator N ψ.lift ψ.lift_smooth ψ.lift_compact R hR hsF := rfl
  have heθ : positiveTimeAbelOperator N θ=
      abelKernelOperator N θ.lift θ.lift_smooth θ.lift_compact R hR hsG := rfl
  rw [heψ,heθ]
  apply abelKernelOperator_sub_norm
  intro q
  have hd : deriv (coshTestLift (fun t => ψ.toFun t-θ.toFun t)) q=
      deriv ψ.lift q-deriv θ.lift q := by
    rw [coshTestLift_sub]
    exact deriv_sub (ψ.lift_smooth.differentiable (by simp) q)
      (θ.lift_smooth.differentiable (by simp) q)
  rw [← hd]
  apply coshTestLift_deriv_bound _ (ψ.smooth.sub θ.smooth) δ R C hδ
    (support_sub_interval ψ.toFun θ.toFun δ R hsψ hsθ)
  intro t
  have hd : deriv (fun v => ψ.toFun v-θ.toFun v) t=deriv ψ.toFun t-deriv θ.toFun t :=
    deriv_sub (ψ.smooth.differentiable (by simp) t) (θ.smooth.differentiable (by simp) t)
  rw [hd]
  exact hb t

#print axioms abelKernelOperator_radius
#print axioms positiveTimeAbelOperator_sub_norm

end QuantitativeMaass
