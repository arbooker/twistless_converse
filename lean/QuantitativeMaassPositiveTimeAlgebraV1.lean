module

public import QuantitativeMaassPositiveTimeContinuityV1
public import QuantitativeMaassAbelNormalizedKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem PositiveTimeTest.compact (ψ : PositiveTimeTest) : HasCompactSupport ψ.toFun :=
  HasCompactSupport.intro isCompact_Icc (fun t ht => by
    by_contra hn
    exact ht (ψ.support hn))

def PositiveTimeTest.first (ψ : PositiveTimeTest) : PositiveTimeTest where
  toFun := deriv ψ.toFun
  smooth := (contDiff_infty_iff_deriv.mp ψ.smooth).2
  real := deriv_real_profile ψ.toFun ψ.real
  left := ψ.left
  right := ψ.right
  left_pos := ψ.left_pos
  right_nonneg := ψ.right_nonneg
  support := (support_deriv_subset).trans
    ((closure_mono ψ.support).trans_eq isClosed_Icc.closure_eq)

/-- A real linear combination with a proved common compact support. -/
def PositiveTimeTest.scaledSub (ψ θ : PositiveTimeTest) (c : ℝ) : PositiveTimeTest where
  toFun := fun t => (c:ℂ)*ψ.toFun t-θ.toFun t
  smooth := (contDiff_const.mul ψ.smooth).sub θ.smooth
  real := fun t => by simp only [star_sub,star_mul,Complex.star_def,Complex.conj_ofReal,ψ.real,θ.real,mul_comm]
  left := min ψ.left θ.left
  right := max ψ.right θ.right
  left_pos := lt_min ψ.left_pos θ.left_pos
  right_nonneg := ψ.right_nonneg.trans (le_max_left _ _)
  support := by
    intro t ht
    by_contra hn
    have hp : ψ.toFun t=0 := by
      by_contra h
      exact hn ⟨(min_le_left _ _).trans (ψ.support h).1,(ψ.support h).2.trans (le_max_left _ _)⟩
    have hq : θ.toFun t=0 := by
      by_contra h
      exact hn ⟨(min_le_right _ _).trans (θ.support h).1,(θ.support h).2.trans (le_max_right _ _)⟩
    exact ht (by dsimp only; rw [hp,hq,mul_zero,sub_self])

theorem coshTestLift_scaledSub (ψ θ : ℝ → ℂ) (c : ℂ) :
    coshTestLift (fun t => c*ψ t-θ t)=
      fun q => c*coshTestLift ψ q-coshTestLift θ q := by
  funext q
  unfold coshTestLift
  split_ifs <;> simp

/-- The actual geometric construction respects real linear combinations.
Support witnesses are allowed to differ between the three tests. -/
theorem positiveTimeAbelOperator_scaledSub (N : ℕ) [NeZero N]
    (ψ θ : PositiveTimeTest) (c : ℝ) :
    positiveTimeAbelOperator N (ψ.scaledSub θ c)=
      (c:ℂ) • positiveTimeAbelOperator N ψ-positiveTimeAbelOperator N θ := by
  let R := max ψ.right θ.right
  have hR : 0≤R := ψ.right_nonneg.trans (le_max_left _ _)
  have hsψ : Function.support ψ.lift⊆Iic (Real.cosh R) := by
    intro q hq
    exact (ψ.lift_support hq).trans
      (Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg ψ.right_nonneg,abs_of_nonneg hR]; exact le_max_left _ _))
  have hsθ : Function.support θ.lift⊆Iic (Real.cosh R) := by
    intro q hq
    exact (θ.lift_support hq).trans
      (Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg θ.right_nonneg,abs_of_nonneg hR]; exact le_max_right _ _))
  let χ := ψ.scaledSub θ c
  have he : χ.lift=(fun q => (c:ℂ)*ψ.lift q-θ.lift q) := coshTestLift_scaledSub _ _ _
  have hp (q : ℝ) : abelProfile χ.lift q=(c:ℂ)*abelProfile ψ.lift q-abelProfile θ.lift q := by
    rw [he,abelProfile_sub _ _ (contDiff_const.mul ψ.lift_smooth) θ.lift_smooth
      ψ.lift_compact.mul_left θ.lift_compact,abelProfile_const_mul]
  apply ContinuousLinearMap.ext
  intro f
  have h := radialKernelOperator_linear N (abelProfile ψ.lift) (abelProfile θ.lift)
    (abelProfile χ.lift) (abelProfile_smooth _ ψ.lift_smooth ψ.lift_compact)
    (abelProfile_smooth _ θ.lift_smooth θ.lift_compact)
    (abelProfile_smooth _ χ.lift_smooth χ.lift_compact) R hR
    (abelProfile_support _ _ hsψ) (abelProfile_support _ _ hsθ)
    (abelProfile_support _ _ χ.lift_support) (c:ℂ) hp f
  exact h

#print axioms PositiveTimeTest.first
#print axioms positiveTimeAbelOperator_scaledSub

end QuantitativeMaass
