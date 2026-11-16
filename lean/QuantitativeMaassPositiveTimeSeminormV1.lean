module

public import QuantitativeMaassPositiveTimeTranslateV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass

def positiveTimeNormConstant (δ R : ℝ) : ℝ :=
  2*Real.pi*(Real.sqrt 2/Real.pi)*((Real.cosh R+1)/Real.sinh δ)*(Real.cosh R-1)

theorem positiveTimeNormConstant_nonneg (δ R : ℝ) (hδ : 0<δ) :
    0≤positiveTimeNormConstant δ R := by
  unfold positiveTimeNormConstant
  have hc := Real.one_le_cosh R
  have hs : 0<Real.sinh δ := Real.sinh_pos_iff.mpr hδ
  positivity

/-- The same operator admits a first-derivative estimate using any common
positive support interval, independently of the test's stored witnesses. -/
theorem positiveTimeAbelOperator_norm_common (N : ℕ) [NeZero N] (ψ : PositiveTimeTest)
    (δ R C : ℝ) (hδ : 0<δ) (hR : 0≤R)
    (hs : Function.support ψ.toFun⊆Icc δ R) (hb : ∀ t,‖deriv ψ.toFun t‖≤C) :
    ‖positiveTimeAbelOperator N ψ‖≤positiveTimeNormConstant δ R*C := by
  let θ : PositiveTimeTest := {ψ with left:=δ,right:=R,left_pos:=hδ,right_nonneg:=hR,support:=hs}
  rw [positiveTimeAbelOperator_congr N ψ θ rfl]
  have h := positiveTimeAbelOperator_derivative_bound N θ C hb
  change _≤2*Real.pi*((Real.sqrt 2/Real.pi)*((C/Real.sinh δ)*(Real.cosh R+1))*(Real.cosh R-1)) at h
  calc
    _ ≤ _ := h
    _ = _ := by unfold positiveTimeNormConstant; ring

theorem PositiveTimeTest.scaledSub_support (ψ θ : PositiveTimeTest) (c δ R : ℝ)
    (hp : Function.support ψ.toFun⊆Icc δ R) (hq : Function.support θ.toFun⊆Icc δ R) :
    Function.support (ψ.scaledSub θ c).toFun⊆Icc δ R := by
  intro t ht
  by_contra hn
  have hp0 : ψ.toFun t=0 := by by_contra h; exact hn (hp h)
  have hq0 : θ.toFun t=0 := by by_contra h; exact hn (hq h)
  exact ht (by change (c:ℂ)*ψ.toFun t-θ.toFun t=0; rw [hp0,hq0,mul_zero,sub_self])

theorem PositiveTimeTest.scaledSub_deriv (ψ θ : PositiveTimeTest) (c t : ℝ) :
    deriv (ψ.scaledSub θ c).toFun t=(c:ℂ)*deriv ψ.toFun t-deriv θ.toFun t := by
  exact (((ψ.smooth.differentiable (by simp) t).hasDerivAt.const_mul (c:ℂ)).sub
    (θ.smooth.differentiable (by simp) t).hasDerivAt).deriv

#print axioms positiveTimeAbelOperator_norm_common
#print axioms PositiveTimeTest.scaledSub_deriv

end QuantitativeMaass
