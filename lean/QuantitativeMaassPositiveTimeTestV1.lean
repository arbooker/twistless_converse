module

public import QuantitativeMaassCoshTestDifferentialV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- A real smooth test supported in a compact positive-time interval. -/
structure PositiveTimeTest where
  toFun : ℝ → ℂ
  smooth : ContDiff ℝ ∞ toFun
  real : ∀ t,star (toFun t)=toFun t
  left : ℝ
  right : ℝ
  left_pos : 0<left
  right_nonneg : 0≤right
  support : Function.support toFun⊆Icc left right

def PositiveTimeTest.second (ψ : PositiveTimeTest) : PositiveTimeTest where
  toFun := deriv (deriv ψ.toFun)
  smooth := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp ψ.smooth).2).2
  real := deriv_real_profile (deriv ψ.toFun) (deriv_real_profile ψ.toFun ψ.real)
  left := ψ.left
  right := ψ.right
  left_pos := ψ.left_pos
  right_nonneg := ψ.right_nonneg
  support := second_deriv_support_interval ψ.toFun ψ.left ψ.right ψ.support

def PositiveTimeTest.lift (ψ : PositiveTimeTest) : ℝ → ℂ := coshTestLift ψ.toFun

theorem PositiveTimeTest.lift_smooth (ψ : PositiveTimeTest) : ContDiff ℝ ∞ ψ.lift :=
  coshTestLift_smooth ψ.toFun ψ.smooth ψ.left ψ.right ψ.left_pos ψ.support

theorem PositiveTimeTest.lift_compact (ψ : PositiveTimeTest) : HasCompactSupport ψ.lift :=
  coshTestLift_compact ψ.toFun ψ.left ψ.right ψ.left_pos ψ.right_nonneg ψ.support

theorem PositiveTimeTest.lift_support (ψ : PositiveTimeTest) :
    Function.support ψ.lift⊆Iic (Real.cosh ψ.right) :=
  fun _ h => (coshTestLift_support ψ.toFun ψ.left ψ.right ψ.left_pos ψ.right_nonneg ψ.support h).2

theorem PositiveTimeTest.lift_real (ψ : PositiveTimeTest) (q : ℝ) : star (ψ.lift q)=ψ.lift q :=
  coshTestLift_real ψ.toFun ψ.real q

theorem PositiveTimeTest.lift_second (ψ : PositiveTimeTest) : coshTimeOperator ψ.lift=ψ.second.lift :=
  coshTestLift_operator ψ.toFun ψ.smooth ψ.left ψ.right ψ.left_pos ψ.support

theorem PositiveTimeTest.waveWeight (ψ : PositiveTimeTest) :
    Wave.ShiftedWaveWeight (fun t => ψ.toFun |t|) := by
  have he : coshTimeTest ψ.lift=(fun t => ψ.toFun |t|) :=
    funext (coshTestLift_time ψ.toFun ψ.left ψ.right ψ.left_pos ψ.support)
  rw [← he]
  exact coshTimeTest_waveWeight ψ.lift ψ.lift_smooth ψ.right ψ.right_nonneg ψ.lift_support

/-- The genuine geometric kernel tested against the evenization of a
positive-time test. The spectral-packet equality is not part of this definition. -/
def positiveTimeAbelOperator (N : ℕ) [NeZero N] (ψ : PositiveTimeTest) :
    AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  abelKernelOperator N ψ.lift ψ.lift_smooth ψ.lift_compact ψ.right ψ.right_nonneg ψ.lift_support

/-- Ordinary second time differentiation now gives the actual operator-valued
weak shifted-wave equation, with membership in the full Friedrichs graph. -/
theorem positiveTimeAbelOperator_graph (N : ℕ) [NeZero N] (ψ : PositiveTimeTest)
    (f : AutomorphicSpace N) :
    FriedrichsGraph N (positiveTimeAbelOperator N ψ f)
      ((1/4:ℂ) • positiveTimeAbelOperator N ψ f-positiveTimeAbelOperator N ψ.second f) := by
  have h := abelKernelOperator_graph N ψ.lift ψ.lift_smooth ψ.lift_compact
    ψ.right ψ.right_nonneg ψ.lift_support ψ.lift_real f
  simpa only [positiveTimeAbelOperator,ψ.lift_second,
    show ψ.second.right=ψ.right from rfl] using h

#print axioms PositiveTimeTest.second
#print axioms PositiveTimeTest.lift_second
#print axioms PositiveTimeTest.waveWeight
#print axioms positiveTimeAbelOperator_graph

end QuantitativeMaass
