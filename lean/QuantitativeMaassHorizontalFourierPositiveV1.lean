module

public import QuantitativeMaassParabolicFourierV1
public import QuantitativeMaassParabolicVariationScaleV1
public import QuantitativeMaassPhysicalAbelSmoothV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff FourierTransform SchwartzMap

namespace QuantitativeMaass

theorem real_fourier_height_scale (g : ℝ→ℂ) (y : ℝ) (hy : 0<y) (ξ : ℝ) :
    𝓕 (fun x => g (x/y)) ξ=(y:ℂ)*𝓕 g (ξ*y) := by
  simp only [Real.fourier_real_eq_integral_exp_smul,smul_eq_mul]
  let h := fun x : ℝ => Complex.exp (((-2*Real.pi*x*(ξ*y):ℝ):ℂ)*Complex.I)*g x
  have hfun (x : ℝ) :
      Complex.exp (((-2*Real.pi*x*ξ:ℝ):ℂ)*Complex.I)*g (x/y)=h (x/y) := by
    have harg : -2*Real.pi*x*ξ= -2*Real.pi*(x/y)*(ξ*y) := by
      field_simp
    dsimp only [h]
    rw [harg]
  simp_rw [hfun]
  simpa only [abs_of_pos hy,Complex.real_smul] using Measure.integral_comp_div h y

/-- Nonnegative horizontal Fourier transform at every integer sample and
at every height, obtained from the actual cylinder column energy. -/
theorem timeSquareLine_fourier_integer_nonneg (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ→ℂ)) (he : Function.Even f)
    (hr : ∀ t,star (f t)=f t) (R : ℝ) (hR : 0≤R)
    (hs : Function.support f⊆Icc (-R) R) (y : ℝ) (hy : 0<y) (n : ℤ) :
    0≤(𝓕 (parabolicLineProfile (abelProfile (evenCoshLift (timeConvolution f f))) y) n).re := by
  let F := evenCoshLift (timeConvolution f f)
  have hF : ContDiffOn ℝ ∞ F (Ici 1) :=
    evenCoshLift_smoothOn _ ((timeConvolution f f).smooth ⊤)
      (timeConvolution_even f f he he) (timeConvolution_compact f f hc hc)
  have hFs : Function.support F⊆Iic (Real.cosh (R+R)) :=
    evenCoshLift_support_of_time_support _ _ (add_nonneg hR hR)
      (timeConvolution_support f f R R hs hs)
  have hg := abelProfile_smoothOn_physical F hF (Real.cosh (R+R)) (Real.one_le_cosh _) hFs
  let z := horocyclePoint 0 y hy
  change 0≤(𝓕 (parabolicLineProfile (abelProfile F) z.im) n).re
  rw [parabolicLine_fourier_coefficient (abelProfile F) hg (Real.cosh (R+R))
    (abelProfile_support F _ hFs) z n]
  exact cylinderTimeSquare_period_coefficient_nonneg f hc he hr R hR hs (-n) z

/-- Positivity at integer frequencies on all heights yields positivity at
 every real frequency for the height-one profile. -/
theorem timeSquareLine_fourier_nonneg (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ→ℂ)) (he : Function.Even f)
    (hr : ∀ t,star (f t)=f t) (R : ℝ) (hR : 0≤R)
    (hs : Function.support f⊆Icc (-R) R) (ξ : ℝ) :
    0≤(𝓕 (parabolicLineProfile (abelProfile (evenCoshLift (timeConvolution f f))) 1) ξ).re := by
  let g := abelProfile (evenCoshLift (timeConvolution f f))
  have hsample (y : ℝ) (hy : 0<y) (n : ℤ) :
      0≤y*(𝓕 (parabolicLineProfile g 1) ((n:ℝ)*y)).re := by
    have hh := timeSquareLine_fourier_integer_nonneg f hc he hr R hR hs y hy n
    have hscale : parabolicLineProfile g y=fun x => parabolicLineProfile g 1 (x/y) :=
      funext (parabolicLineProfile_height_scale g y)
    change 0≤(𝓕 (parabolicLineProfile g y) n).re at hh
    rw [hscale,real_fourier_height_scale _ y hy] at hh
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hh
  rcases lt_trichotomy ξ 0 with hξ | hξ | hξ
  · have hh := hsample (-ξ) (neg_pos.mpr hξ) (-1)
    norm_num only [Int.cast_neg,Int.cast_one,neg_one_mul,neg_neg] at hh
    exact (mul_nonneg_iff_of_pos_left (neg_pos.mpr hξ)).mp hh
  · subst ξ
    simpa only [Int.cast_zero,zero_mul,one_mul] using hsample 1 zero_lt_one 0
  · have hh := hsample ξ hξ 1
    norm_num only [Int.cast_one,one_mul] at hh
    exact (mul_nonneg_iff_of_pos_left hξ).mp hh

#print axioms real_fourier_height_scale
#print axioms timeSquareLine_fourier_integer_nonneg
#print axioms timeSquareLine_fourier_nonneg

end QuantitativeMaass
