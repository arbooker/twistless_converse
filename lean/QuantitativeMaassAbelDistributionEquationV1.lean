module

public import QuantitativeMaassAbelTestDistributionV1
public import QuantitativeMaassRadialKernelCommuteV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter TopologicalSpace
open scoped Topology ContDiff Distributions InnerProductSpace

namespace QuantitativeMaass

/-- Differentiation is a continuous linear operation on the real positive
time test space and keeps every compact support inside the positive half-line. -/
def positiveSmoothTestDeriv : PositiveSmoothTest →L[ℝ] PositiveSmoothTest :=
  TestFunction.lineDerivCLM ℝ (1:ℝ)

theorem positiveSmoothTestDeriv_apply (φ : PositiveSmoothTest) (t : ℝ) :
    positiveSmoothTestDeriv φ t=deriv (φ : ℝ → ℝ) t := by
  change (TestFunction.lineDerivCLM ℝ (1:ℝ) φ : PositiveSmoothTest) t=_
  rw [TestFunction.lineDerivCLM_eq_fderivCLM]
  have he := congrFun (TestFunction.fderivCLM_apply (𝕜:=ℝ) (k:=⊤) φ) t
  simp only [top_add,le_refl,ite_true] at he
  rw [he]
  rfl

theorem positiveSmoothTestToAbel_deriv (φ : PositiveSmoothTest) :
    (positiveSmoothTestToAbel (positiveSmoothTestDeriv φ)).toFun=
      (positiveSmoothTestToAbel φ).first.toFun := by
  funext t
  change ((positiveSmoothTestDeriv φ t:ℝ):ℂ)=deriv (fun s => (φ s:ℂ)) t
  rw [positiveSmoothTestDeriv_apply]
  exact ((φ.contDiff.differentiable (by simp) t).hasDerivAt.ofReal_comp).deriv.symm

theorem positiveSmoothTestToAbel_second (φ : PositiveSmoothTest) :
    (positiveSmoothTestToAbel (positiveSmoothTestDeriv (positiveSmoothTestDeriv φ))).toFun=
      (positiveSmoothTestToAbel φ).second.toFun := by
  rw [positiveSmoothTestToAbel_deriv]
  change deriv (positiveSmoothTestToAbel (positiveSmoothTestDeriv φ)).toFun=
    deriv (deriv (positiveSmoothTestToAbel φ).toFun)
  rw [positiveSmoothTestToAbel_deriv]
  rfl

/-- The distribution satisfies the actual Friedrichs equation, not a
formal scalar surrogate: every tested operator maps every L2 input into
the full unbounded Laplacian graph. -/
theorem abelTestDistribution_graph (N : ℕ) [NeZero N]
    (φ : PositiveSmoothTest) (f : AutomorphicSpace N) :
    FriedrichsGraph N (abelTestDistribution N φ f)
      ((1/4:ℂ) • abelTestDistribution N φ f-
        abelTestDistribution N (positiveSmoothTestDeriv (positiveSmoothTestDeriv φ)) f) := by
  have he := positiveTimeAbelOperator_congr N _ _ (positiveSmoothTestToAbel_second φ)
  simpa only [abelTestDistribution_apply,he] using
    positiveTimeAbelOperator_graph N (positiveSmoothTestToAbel φ) f

/-- The distribution values commute with the actual quotient shifted wave;
this follows from the real geometric radial kernel and full-domain graph. -/
theorem abelTestDistribution_commute_wave (N : ℕ) [NeZero N]
    (φ : PositiveSmoothTest) (t : ℝ) :
    Commute (abelTestDistribution N φ) (Wave.shiftedQuotientWave N t) := by
  let ψ := positiveSmoothTestToAbel φ
  exact radialKernelOperator_commute_wave N (abelProfile ψ.lift)
    (abelProfile_smooth _ ψ.lift_smooth ψ.lift_compact) ψ.right ψ.right_nonneg
    (abelProfile_support _ _ ψ.lift_support) (abelProfile_real _ ψ.lift_real) t

#print axioms positiveSmoothTestDeriv_apply
#print axioms positiveSmoothTestToAbel_second
#print axioms abelTestDistribution_graph
#print axioms abelTestDistribution_commute_wave

end QuantitativeMaass
