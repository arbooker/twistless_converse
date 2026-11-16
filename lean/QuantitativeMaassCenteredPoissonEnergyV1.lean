module

public import QuantitativeMaassHorizontalFourierPositiveV1
public import QuantitativeMaassPositiveFourierMassV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff FourierTransform SchwartzMap ENNReal

namespace QuantitativeMaass

/-- A nonnegative centered Poisson sum, written without complex cancellation. -/
theorem schwartz_centered_poisson_ofReal (F : SchwartzMap ℝ ℂ)
    (he : Function.Even F) (hp : ∀ n : ℕ,0≤(𝓕 F (n+1)).re) :
    ENNReal.ofReal ((∑' k : ℤ,F k)-𝓕 F 0).re=
      2*(∑' n : ℕ,ENNReal.ofReal (𝓕 F (n+1)).re) := by
  have hinj : Function.Injective (fun n : ℕ => (n:ℤ)+1) := by
    intro a b hab
    exact_mod_cast (add_right_cancel hab)
  have hi := (schwartz_integer_summable (𝓕 F)).comp_injective hinj
  have hs : Summable (fun n : ℕ => 𝓕 F (n+1)) := by
    simpa only [Function.comp_def,Int.cast_add,Int.cast_natCast,Int.cast_one] using hi
  rw [schwartz_centered_poisson F he]
  simp only [Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
  rw [←(Complex.hasSum_re hs.hasSum).tsum_eq,ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_ofNat,ENNReal.ofReal_tsum_of_nonneg hp (Complex.hasSum_re hs.hasSum).summable]

theorem parabolicLineProfile_even (g : ℝ→ℂ) (y : ℝ) :
    Function.Even (parabolicLineProfile g y) := by
  intro x
  simp only [parabolicLineProfile,neg_sq]

/-- The actual centered cylinder-column energy equals the sum of all
nonzero horizontal modes of its convolution-square profile. -/
theorem cylinderTimeColumn_centered_positive_modes (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ→ℂ)) (he : Function.Even f)
    (hr : ∀ t,star (f t)=f t) (R : ℝ) (hR : 0≤R)
    (hs : Function.support f⊆Icc (-R) R) (z : ℍ) :
    ENNReal.ofReal (‖cylinderTimeColumn f hc he R hR hs z-
      ∫ x in Icc (0:ℝ) 1,cylinderTimeColumn f hc he R hR hs (x+ᵥz)‖^2)=
      2*ENNReal.ofReal z.im*(∑' n : ℕ,ENNReal.ofReal
        (𝓕 (parabolicLineProfile (abelProfile (evenCoshLift (timeConvolution f f))) 1)
          (((n+1:ℕ):ℝ)*z.im)).re) := by
  let F := evenCoshLift (timeConvolution f f)
  let g := abelProfile F
  have hF : ContDiffOn ℝ ∞ F (Ici 1) :=
    evenCoshLift_smoothOn _ ((timeConvolution f f).smooth ⊤)
      (timeConvolution_even f f he he) (timeConvolution_compact f f hc hc)
  have hFs : Function.support F⊆Iic (Real.cosh (R+R)) :=
    evenCoshLift_support_of_time_support _ _ (add_nonneg hR hR)
      (timeConvolution_support f f R R hs hs)
  have hg := abelProfile_smoothOn_physical F hF (Real.cosh (R+R)) (Real.one_le_cosh _) hFs
  have hgs := abelProfile_support F _ hFs
  let Q := parabolicLineSchwartz g hg (Real.cosh (R+R)) hgs z.im z.im_pos
  have hzero := parabolicLine_fourier_coefficient g hg (Real.cosh (R+R)) hgs z 0
  simp only [Int.cast_zero,neg_zero,periodCharacter,fourier_zero,one_mul] at hzero
  have hdiag := cylinderRadialKernel_periodization g z 0
  simp only [zero_vadd,zero_add] at hdiag
  rw [cylinderTimeColumn_centered_kernel f hc he hr R hR hs z,←Complex.sub_re]
  change ENNReal.ofReal ((radialPoincareKernel 0 g z z)-
    ∫ x in Icc (0:ℝ) 1,radialPoincareKernel 0 g (x+ᵥz) z).re=_
  rw [←hzero,hdiag]
  change ENNReal.ofReal ((∑' k : ℤ,Q k)-𝓕 Q 0).re=_
  have hp (n : ℕ) : 0≤(𝓕 Q (n+1)).re := by
    change 0≤(𝓕 (parabolicLineProfile g z.im) (n+1)).re
    have hh := timeSquareLine_fourier_integer_nonneg f hc he hr R hR hs z.im z.im_pos ((n:ℤ)+1)
    simpa only [Int.cast_add,Int.cast_natCast,Int.cast_one] using hh
  rw [schwartz_centered_poisson_ofReal Q (parabolicLineProfile_even g z.im) hp]
  have hscale : parabolicLineProfile g z.im=fun x => parabolicLineProfile g 1 (x/z.im) :=
    funext (parabolicLineProfile_height_scale g z.im)
  have hv (n : ℕ) : ENNReal.ofReal (𝓕 Q (n+1)).re=
      ENNReal.ofReal z.im*ENNReal.ofReal
        (𝓕 (parabolicLineProfile g 1) (((n+1:ℕ):ℝ)*z.im)).re := by
    change ENNReal.ofReal (𝓕 (parabolicLineProfile g z.im) (n+1)).re=_
    rw [hscale,real_fourier_height_scale _ z.im z.im_pos]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
      Nat.cast_add,Nat.cast_one,ENNReal.ofReal_mul z.im_pos.le]
  simp_rw [hv]
  rw [ENNReal.tsum_mul_left,mul_assoc]

#print axioms schwartz_centered_poisson_ofReal
#print axioms parabolicLineProfile_even
#print axioms cylinderTimeColumn_centered_positive_modes

end QuantitativeMaass
