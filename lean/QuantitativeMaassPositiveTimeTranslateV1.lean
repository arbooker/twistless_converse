module

public import QuantitativeMaassPositiveTimeAlgebraV1
public import QuantitativeMaassTranslatedTestSmoothV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Translate a test while its support stays in positive time. -/
def PositiveTimeTest.translate (ψ : PositiveTimeTest) (x : ℝ) (hx : 0<ψ.left+x) :
    PositiveTimeTest where
  toFun := fun t => ψ.toFun (t-x)
  smooth := ψ.smooth.comp (contDiff_id.sub contDiff_const)
  real := fun t => ψ.real (t-x)
  left := ψ.left+x
  right := ψ.right+|x|
  left_pos := hx
  right_nonneg := add_nonneg ψ.right_nonneg (abs_nonneg _)
  support := by
    intro t ht
    have h := ψ.support ht
    constructor
    · linarith [h.1]
    · linarith [h.2,le_abs_self x]

theorem PositiveTimeTest.translate_deriv (ψ : PositiveTimeTest) (x : ℝ)
    (hx : 0<ψ.left+x) (t : ℝ) :
    deriv (ψ.translate x hx).toFun t=deriv ψ.toFun (t-x) := by
  have hi : HasDerivAt (fun u : ℝ => u-x) 1 t := (hasDerivAt_id t).sub_const x
  simpa only [one_smul,PositiveTimeTest.translate,Function.comp_def] using
    ((ψ.smooth.differentiable (by simp) (t-x)).hasDerivAt.scomp t hi).deriv

theorem positiveTimeAbelOperator_congr (N : ℕ) [NeZero N] (ψ θ : PositiveTimeTest)
    (he : ψ.toFun=θ.toFun) : positiveTimeAbelOperator N ψ=positiveTimeAbelOperator N θ := by
  have hl : ψ.lift=θ.lift := congrArg coshTestLift he
  unfold positiveTimeAbelOperator
  simp only [hl]
  rfl

/-- Translation as an everywhere-defined operator curve. Only the open set
where the translated support remains positive is used for differentiation. -/
def translatedPositiveTimeAbelOperator (N : ℕ) [NeZero N] (ψ : PositiveTimeTest)
    (x : ℝ) : AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  if hx : 0<ψ.left+x then positiveTimeAbelOperator N (ψ.translate x hx) else 0

theorem translatedPositiveTimeAbelOperator_eq (N : ℕ) [NeZero N] (ψ : PositiveTimeTest)
    (x : ℝ) (hx : 0<ψ.left+x) :
    translatedPositiveTimeAbelOperator N ψ x=positiveTimeAbelOperator N (ψ.translate x hx) :=
  dite_eq_left hx

theorem translatedPositiveTimeAbelOperator_zero (N : ℕ) [NeZero N] (ψ : PositiveTimeTest) :
    translatedPositiveTimeAbelOperator N ψ 0=positiveTimeAbelOperator N ψ := by
  rw [translatedPositiveTimeAbelOperator_eq N ψ 0 (by simpa using ψ.left_pos)]
  exact positiveTimeAbelOperator_congr N _ _ (by ext t; simp [PositiveTimeTest.translate])

/-- A fixed compact positive interval controls every sufficiently nearby
translation. This is the support estimate needed in the operator-norm bounds. -/
theorem PositiveTimeTest.translate_support_near (ψ : PositiveTimeTest) (x : ℝ)
    (hx : 0<ψ.left+x) (z : ℝ) (hz : |z-x|<(ψ.left+x)/2) :
    0<ψ.left+z ∧ Function.support (fun t => ψ.toFun (t-z))⊆
      Icc ((ψ.left+x)/2) (ψ.right+|x|+(ψ.left+x)/2) := by
  have hz' := abs_lt.mp hz
  constructor
  · linarith [hz'.1]
  · intro t ht
    have h := ψ.support ht
    constructor
    · linarith [h.1,hz'.1]
    · linarith [h.2,hz'.2,le_abs_self x]

#print axioms PositiveTimeTest.translate_deriv
#print axioms positiveTimeAbelOperator_congr
#print axioms translatedPositiveTimeAbelOperator_zero
#print axioms PositiveTimeTest.translate_support_near

end QuantitativeMaass
