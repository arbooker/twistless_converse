module

public import QuantitativeMaassStationaryCrossMeanV1
public import QuantitativeMaassCylinderStationaryV1
public import QuantitativeMaassPhysicalAbelSmoothV1
public import QuantitativeMaassParabolicFourierV1
public import QuantitativeMaassParabolicLatticeSpacingV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff SchwartzMap FourierTransform

namespace QuantitativeMaass

variable (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
  (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
  (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)

include hr

/-- The actual cylinder means at arbitrary heights pair only with each
other; mixed mean and centered terms vanish. -/
theorem cylinderTimeColumn_cross_mean (z w : ℍ) :
    inner ℂ (cylinderTimeColumn f hc he R hR hs z)
      (∫ y in Icc (0:ℝ) 1,cylinderTimeColumn f hc he R hR hs (y+ᵥw))=
    inner ℂ (∫ y in Icc (0:ℝ) 1,cylinderTimeColumn f hc he R hR hs (y+ᵥz))
      (∫ y in Icc (0:ℝ) 1,cylinderTimeColumn f hc he R hR hs (y+ᵥw)) := by
  have hcont (u : ℍ) : Continuous (fun x : ℝ => cylinderTimeColumn f hc he R hR hs (x+ᵥu)) :=
    (cylinderAbelColumn_continuous _ _ R hR _).comp (cylinder_vadd_continuous u)
  have hstat (r x y : ℝ) :
      inner ℂ (cylinderTimeColumn f hc he R hR hs ((x+r)+ᵥz))
        (cylinderTimeColumn f hc he R hR hs ((y+r)+ᵥw))=
      inner ℂ (cylinderTimeColumn f hc he R hR hs (x+ᵥz))
        (cylinderTimeColumn f hc he R hR hs (y+ᵥw)) := by
    rw [cylinderTimeSquare_kernel_cross f hc he hr R hR hs,
      cylinderTimeSquare_kernel_cross f hc he hr R hR hs]
    rw [add_comm x r,add_comm y r,add_vadd,add_vadd,cylinderRadialKernel_translation]
  have hh := stationary_cross_mean_pairing _ _ (hcont z) (hcont w)
    (cylinderTimeColumn_periodic f hc he R hR hs w) hstat 0
  simpa only [zero_vadd] using hh

/-- Exact energy of the actual horizontal mean, expressed as its
height times the horizontal profile mass at height one. -/
theorem cylinderTimeColumn_mean_energy (z : ℍ) :
    ‖∫ y in Icc (0:ℝ) 1,cylinderTimeColumn f hc he R hR hs (y+ᵥz)‖^2=
      z.im*(∫ u,parabolicLineProfile
        (abelProfile (evenCoshLift (timeConvolution f f))) 1 u).re := by
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
  have hzero := parabolicLine_fourier_coefficient g hg (Real.cosh (R+R)) hgs z 0
  simp only [Int.cast_zero,neg_zero,periodCharacter,fourier_zero,one_mul] at hzero
  have hFourier : 𝓕 (parabolicLineProfile g z.im) 0=∫ u,parabolicLineProfile g z.im u := by
    simp only [Real.fourier_real_eq_integral_exp_smul,mul_zero,Complex.ofReal_zero,
      zero_mul,Complex.exp_zero,one_smul]
  rw [hFourier,parabolicLineProfile_mass_scale g z.im z.im_pos] at hzero
  have hi : IntegrableOn (fun y : ℝ => cylinderTimeColumn f hc he R hR hs (y+ᵥz)) (Icc (0:ℝ) 1) :=
    ((cylinderAbelColumn_continuous _ _ R hR _).comp (cylinder_vadd_continuous z)).integrableOn_Icc
  rw [←inner_self_eq_norm_sq (𝕜:=ℂ),←cylinderTimeColumn_cross_mean f hc he hr R hR hs z z,
    ←integral_inner hi]
  simp_rw [cylinderTimeSquare_kernel_cross f hc he hr R hR hs]
  change (∫ y in Icc (0:ℝ) 1,radialPoincareKernel 0 g (y+ᵥz) z).re=_
  rw [←hzero]
  simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rfl

#print axioms cylinderTimeColumn_cross_mean
#print axioms cylinderTimeColumn_mean_energy

end QuantitativeMaass
