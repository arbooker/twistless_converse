module

public import QuantitativeMaassPhysicalLineSmoothV1
public import QuantitativeMaassEvenTimeCalculusV1
public import QuantitativeMaassWindowCenteredKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- The actual one-sided Abel profile is smooth on the entire physical
half-line, including its endpoint. No smooth extension below one is used. -/
theorem abelProfile_smoothOn_physical (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ici 1)) (B : ℝ) (hB : 1≤B)
    (hs : Function.support F⊆Iic B) : ContDiffOn ℝ ∞ (abelProfile F) (Ici 1) := by
  let H := parabolicLineProfile (abelProfile F) 1
  have hH : ContDiff ℝ ∞ H := abelProfile_horizontal_smooth F hF B hB hs 1
  have he : Function.Even H := by
    intro v
    simp only [H,parabolicLineProfile,neg_sq]
  have hc : HasCompactSupport H :=
    parabolicLineProfile_compact (abelProfile F) B (abelProfile_support F B hs) 1 zero_lt_one
  have hh := (evenSquareLift_smoothOn H hH he hc).comp
    (show ContDiffOn ℝ ∞ (fun q : ℝ => 2*(q-1)) (Ici 1) by fun_prop)
    (fun q hq => mul_nonneg (by norm_num) (sub_nonneg.mpr hq))
  apply hh.congr
  intro q hq
  dsimp only [Function.comp_def,evenSquareLift,H,parabolicLineProfile]
  rw [Real.sq_sqrt (mul_nonneg (by norm_num) (sub_nonneg.mpr hq))]
  congr 1
  ring

/-- The literal squared-window Abel profile satisfies the physical smoothness
premise needed by the checked centered-variation theorem. -/
theorem windowTimeSquareProfile_smoothOn (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) :
    ContDiffOn ℝ ∞ (windowTimeSquareProfile K hc R hR a b) (Ici 1) := by
  obtain ⟨B,hB,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  let f := windowTimeSchwartz K hc R hR a b
  have hfc : HasCompactSupport (f : ℝ → ℂ) := symmetricWindowTimeTest_compact K hc R a b hR
  have hfe : Function.Even f := symmetricWindowTimeTest_even K he R a b
  have hgc := timeConvolution_compact f f hfc hfc
  have hge := timeConvolution_even f f hfe hfe
  have hgs := timeConvolution_support f f (B*R) (B*R) (hs R hR a b) (hs R hR a b)
  have hBR : 0≤B*R+B*R := by positivity
  exact abelProfile_smoothOn_physical _
    (evenCoshLift_smoothOn _ ((timeConvolution f f).smooth ⊤) hge hgc)
    (Real.cosh (B*R+B*R)) (Real.one_le_cosh _)
    (evenCoshLift_support_of_time_support _ _ hBR hgs)

#print axioms abelProfile_smoothOn_physical
#print axioms windowTimeSquareProfile_smoothOn

end QuantitativeMaass
