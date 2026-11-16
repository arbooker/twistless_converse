module

public import QuantitativeMaassAbelRegularizedCauchyV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

/-- A genuine real positive-time Abel test gives an ordinary real smooth
test on the positive half-line, with exactly the same values. -/
def PositiveTimeTest.toSmooth (ψ : PositiveTimeTest) : PositiveSmoothTest where
  toFun t := (ψ.toFun t).re
  contDiff' := Complex.reCLM.contDiff.comp ψ.smooth
  hasCompactSupport' := ψ.compact.mono' (fun t ht => subset_tsupport _ (fun hz => ht (by simp only [hz,Complex.zero_re])))
  tsupport_subset' := by
    have hs : Function.support (fun t => (ψ.toFun t).re)⊆Icc ψ.left ψ.right := by
      intro t ht
      apply ψ.support
      intro hz
      exact ht (by simp only [hz,Complex.zero_re])
    intro t ht
    exact ψ.left_pos.trans_le (closure_minimal hs isClosed_Icc ht).1

theorem PositiveTimeTest.toSmooth_coe (ψ : PositiveTimeTest) (t : ℝ) :
    ((ψ.toSmooth t:ℝ):ℂ)=ψ.toFun t := by
  apply Complex.ext
  · rfl
  · have h := congrArg Complex.im (ψ.real t)
    simp only [Complex.star_def,Complex.conj_im] at h
    change 0=(ψ.toFun t).im
    linarith

theorem PositiveTimeTest.toSmooth_operator (N : ℕ) [NeZero N] (ψ : PositiveTimeTest) :
    abelTestDistribution N ψ.toSmooth=positiveTimeAbelOperator N ψ :=
  positiveSmoothTestToAbel_congr N ψ.toSmooth ψ (fun t => (ψ.toSmooth_coe t).symm)

/-- The real and complex scalar actions agree in this conversion. -/
theorem PositiveTimeTest.toSmooth_smul {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (ψ : PositiveTimeTest) (t : ℝ) (v : H) : ψ.toSmooth t • v=ψ.toFun t • v := by
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),RCLike.ofReal_eq_complex_ofReal,ψ.toSmooth_coe]

#print axioms PositiveTimeTest.toSmooth_coe
#print axioms PositiveTimeTest.toSmooth_operator

end QuantitativeMaass
