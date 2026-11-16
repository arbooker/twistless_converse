module

public import QuantitativeMaassPositiveTimeSeminormV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff NNReal

namespace QuantitativeMaass

/-- The first-order remainder as an actual compactly supported time test. -/
def PositiveTimeTest.translationRemainder (ψ : PositiveTimeTest) (x z : ℝ)
    (hx : 0<ψ.left+x) (hz : 0<ψ.left+z) : PositiveTimeTest :=
  (ψ.first.translate x hx).scaledSub ((ψ.translate x hx).scaledSub (ψ.translate z hz) 1) (z-x)

/-- The derivative seminorm of the translated-test remainder is quadratic
in the translation increment, with a proved global Lipschitz constant. -/
theorem PositiveTimeTest.translationRemainder_deriv_bound (ψ : PositiveTimeTest)
    (K : ℝ≥0) (hK : LipschitzWith K (deriv (deriv ψ.toFun)))
    (x z : ℝ) (hx : 0<ψ.left+x) (hz : 0<ψ.left+z) (t : ℝ) :
    ‖deriv (ψ.translationRemainder x z hx hz).toFun t‖≤(K:ℝ)*‖z-x‖^2 := by
  have hd := (contDiff_infty_iff_deriv.mp ψ.smooth).2
  have h := norm_taylor_remainder_le (deriv ψ.toFun) (deriv (deriv ψ.toFun)) K
    (fun u => (hd.differentiable (by simp) u).hasDerivAt) hK (t-x) (t-z)
  have he : (t-z)-(t-x)=-(z-x) := by ring
  rw [he,norm_neg] at h
  have hv : deriv (ψ.translationRemainder x z hx hz).toFun t=
      deriv ψ.toFun (t-z)-deriv ψ.toFun (t-x)- (-(z-x)) • deriv (deriv ψ.toFun) (t-x) := by
    unfold PositiveTimeTest.translationRemainder
    rw [PositiveTimeTest.scaledSub_deriv,PositiveTimeTest.scaledSub_deriv,
      PositiveTimeTest.translate_deriv,PositiveTimeTest.translate_deriv,PositiveTimeTest.translate_deriv]
    change (↑(z-x):ℂ)*deriv (deriv ψ.toFun) (t-x)-
      (1*deriv ψ.toFun (t-x)-deriv ψ.toFun (t-z))=_
    simp only [Complex.real_smul,Complex.ofReal_neg]
    ring
  rw [hv]
  exact h

theorem positiveTimeAbelOperator_translationRemainder (N : ℕ) [NeZero N]
    (ψ : PositiveTimeTest) (x z : ℝ) (hx : 0<ψ.left+x) (hz : 0<ψ.left+z) :
    positiveTimeAbelOperator N (ψ.translationRemainder x z hx hz)=
      translatedPositiveTimeAbelOperator N ψ z-translatedPositiveTimeAbelOperator N ψ x-
        (z-x) • (-translatedPositiveTimeAbelOperator N ψ.first x) := by
  unfold PositiveTimeTest.translationRemainder
  rw [positiveTimeAbelOperator_scaledSub,positiveTimeAbelOperator_scaledSub]
  rw [translatedPositiveTimeAbelOperator_eq N ψ z hz,
    translatedPositiveTimeAbelOperator_eq N ψ x hx,
    translatedPositiveTimeAbelOperator_eq N ψ.first x hx]
  simp only [Complex.ofReal_one,one_smul]
  let P := positiveTimeAbelOperator N (ψ.first.translate x hx)
  let Q := positiveTimeAbelOperator N (ψ.translate x hx)
  let S := positiveTimeAbelOperator N (ψ.translate z hz)
  change (↑(z-x):ℂ) • P-(Q-S)=S-Q-(z-x) • (-P)
  have hs : (↑(z-x):ℂ) • P=(z-x) • P :=
    (RCLike.real_smul_eq_coe_smul (K:=ℂ) (z-x) P).symm
  rw [hs,smul_neg (z-x) P]
  abel

/-- Uniform operator-norm Taylor remainder on a neighborhood whose translated
supports stay a positive distance from zero. -/
theorem translatedPositiveTimeAbelOperator_remainder_le (N : ℕ) [NeZero N]
    (ψ : PositiveTimeTest) (K : ℝ≥0) (hK : LipschitzWith K (deriv (deriv ψ.toFun)))
    (x : ℝ) (hx : 0<ψ.left+x) (z : ℝ) (hz : |z-x|<(ψ.left+x)/2) :
    ‖translatedPositiveTimeAbelOperator N ψ z-translatedPositiveTimeAbelOperator N ψ x-
      (z-x) • (-translatedPositiveTimeAbelOperator N ψ.first x)‖≤
      positiveTimeNormConstant ((ψ.left+x)/2) (ψ.right+|x|+(ψ.left+x)/2)*
        ((K:ℝ)*‖z-x‖^2) := by
  obtain ⟨hz0,hsz⟩ := ψ.translate_support_near x hx z hz
  have hxx : |x-x|<(ψ.left+x)/2 := by rw [sub_self,abs_zero]; linarith
  have hsx := (ψ.translate_support_near x hx x hxx).2
  have hsd := (ψ.first.translate_support_near x hx x hxx).2
  rw [← positiveTimeAbelOperator_translationRemainder N ψ x z hx hz0]
  apply positiveTimeAbelOperator_norm_common
  · linarith
  · have hp := ψ.right_nonneg; have ha := abs_nonneg x; linarith
  · exact PositiveTimeTest.scaledSub_support _ _ _ _ _ hsd
      (PositiveTimeTest.scaledSub_support _ _ _ _ _ hsx hsz)
  · exact ψ.translationRemainder_deriv_bound K hK x z hx hz0

#print axioms PositiveTimeTest.translationRemainder_deriv_bound
#print axioms positiveTimeAbelOperator_translationRemainder
#print axioms translatedPositiveTimeAbelOperator_remainder_le

end QuantitativeMaass
