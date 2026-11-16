module

public import QuantitativeMaassCuspKernelBoundV1
public import QuantitativeMaassIntegratedWindowV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open scoped Topology MatrixGroups FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- At fixed propagation radius, the actual moving-window nonidentity kernel
has the sharp square-root spectral factor and an integrable cusp-height cost.
Both constants precede all levels, charts, widths and spectral centres. -/
theorem windowGeometricRemainder_fixedRadius_high_cusp (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ B C : ℝ,0<B ∧ 0<C ∧ ∀ (N : ℕ) (A : SL(2,ℤ)) (ε t : ℝ),
      0≤ε → ε≤1 → 1≤t → ∀ z : ℍ,Real.exp B<z.im →
      ‖windowGeometricRemainder N K hc 1 zero_lt_one (t-ε) (t+ε) (A•z)‖≤
        C*Real.sqrt t*ε^2*(1+z.im)*Real.sqrt z.im := by
  obtain ⟨B,hB,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  obtain ⟨C,hC,hbound⟩ := windowTimeSquare_abel_decay K he hc
  refine ⟨B,(6*Real.exp (2*B)+9)*C,hB,by positivity,?_⟩
  intro N A ε t hε hε1 ht z hz
  let f := windowTimeSchwartz K hc 1 zero_lt_one (t-ε) (t+ε)
  have hfs : Function.support (f : ℝ → ℂ)⊆Icc (-B) B := by
    change Function.support (symmetricWindowTimeTest K 1 (t-ε) (t+ε))⊆_
    simpa only [mul_one] using hs 1 zero_lt_one (t-ε) (t+ε)
  have hgs : Function.support (timeConvolution f f : ℝ → ℂ)⊆Icc (-(2*B)) (2*B) := by
    simpa only [two_mul] using timeConvolution_support f f B B hfs hfs
  have hps : Function.support (windowSquareProfile K hc 1 zero_lt_one ε t)⊆Iic (Real.cosh (2*B)) :=
    abelProfile_support _ _ (evenCoshLift_support_of_time_support _ _ (by positivity) hgs)
  have hp : ∀ d : ℝ,0<d → ‖windowSquareProfile K hc 1 zero_lt_one ε t (Real.cosh d)‖≤
      (C*Real.sqrt t*ε^2)/Real.sqrt (Real.sinh d) := by
    intro d hd
    dsimp only [windowSquareProfile]
    simpa only [one_pow,mul_one] using hbound 1 ε t d le_rfl hε hε1 ht hd
  have hh := radialNonidentity_high_cusp_bound N A
    (windowSquareProfile K hc 1 zero_lt_one ε t) (2*B) (by positivity)
    hps (C*Real.sqrt t*ε^2) (by positivity) hp z (by simpa only [mul_div_cancel_left₀ B (by norm_num : (2:ℝ)≠0)] using hz)
  apply hh.trans
  have hb : 6*z.im*(Real.exp (2*B)-1)+9≤(6*Real.exp (2*B)+9)*(1+z.im) := by
    nlinarith [Real.exp_pos (2*B),z.im_pos]
  have hm := mul_le_mul_of_nonneg_right hb
    (show 0≤(C*Real.sqrt t*ε^2)*Real.sqrt z.im by positivity)
  convert hm using 1 <;> ring

#print axioms windowGeometricRemainder_fixedRadius_high_cusp

end QuantitativeMaass
