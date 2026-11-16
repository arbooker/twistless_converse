module

public import QuantitativeMaassPositiveTimeSmoothV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem PositiveTimeTest.translate_second (ψ : PositiveTimeTest) (x : ℝ)
    (hx : 0<ψ.left+x) :
    (ψ.translate x hx).second.toFun=(ψ.second.translate x hx).toFun := by
  have he : deriv (ψ.translate x hx).toFun=(ψ.first.translate x hx).toFun :=
    funext (ψ.translate_deriv x hx)
  funext t
  change deriv (deriv (ψ.translate x hx).toFun) t=deriv (deriv ψ.toFun) (t-x)
  rw [he]
  exact ψ.first.translate_deriv x hx t

theorem translatedPositiveTimeAbelOperator_hasDerivAt_apply (N : ℕ) [NeZero N]
    (ψ : PositiveTimeTest) (f : AutomorphicSpace N) (x : ℝ) (hx : 0<ψ.left+x) :
    HasDerivAt (fun t => translatedPositiveTimeAbelOperator N ψ t f)
      (-translatedPositiveTimeAbelOperator N ψ.first x f) x := by
  let E := (ContinuousLinearMap.apply ℂ (AutomorphicSpace N) f).restrictScalars ℝ
  have he : HasFDerivAt E E (translatedPositiveTimeAbelOperator N ψ x) := E.hasFDerivAt
  have h := he.comp_hasDerivAt x (f := translatedPositiveTimeAbelOperator N ψ)
    (translatedPositiveTimeAbelOperator_hasDerivAt N ψ x hx)
  convert! h using 1

theorem translatedPositiveTimeAbelOperator_velocity_hasDerivAt (N : ℕ) [NeZero N]
    (ψ : PositiveTimeTest) (f : AutomorphicSpace N) (x : ℝ) (hx : 0<ψ.left+x) :
    HasDerivAt (fun t => -translatedPositiveTimeAbelOperator N ψ.first t f)
      (translatedPositiveTimeAbelOperator N ψ.second x f) x := by
  have h := (translatedPositiveTimeAbelOperator_hasDerivAt_apply N ψ.first f x hx).neg
  convert! h using 1
  simp only [neg_neg]
  rfl

/-- Every translated smooth time test gives a genuine local strong solution
of the shifted wave equation in the full Friedrichs domain. -/
theorem translatedPositiveTimeAbelOperator_graph (N : ℕ) [NeZero N]
    (ψ : PositiveTimeTest) (f : AutomorphicSpace N) (x : ℝ) (hx : 0<ψ.left+x) :
    FriedrichsGraph N (translatedPositiveTimeAbelOperator N ψ x f)
      ((1/4:ℂ) • translatedPositiveTimeAbelOperator N ψ x f-
        translatedPositiveTimeAbelOperator N ψ.second x f) := by
  rw [translatedPositiveTimeAbelOperator_eq N ψ x hx,
    translatedPositiveTimeAbelOperator_eq N ψ.second x hx]
  have he := positiveTimeAbelOperator_congr N (ψ.translate x hx).second
    (ψ.second.translate x hx) (ψ.translate_second x hx)
  have h := positiveTimeAbelOperator_graph N (ψ.translate x hx) f
  rw [he] at h
  exact h

#print axioms PositiveTimeTest.translate_second
#print axioms translatedPositiveTimeAbelOperator_hasDerivAt_apply
#print axioms translatedPositiveTimeAbelOperator_velocity_hasDerivAt
#print axioms translatedPositiveTimeAbelOperator_graph

end QuantitativeMaass
