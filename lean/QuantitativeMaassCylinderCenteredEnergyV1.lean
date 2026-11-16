module

public import QuantitativeMaassCylinderLatticeV1
public import QuantitativeMaassPhysicalAbelSmoothV1
public import AsymptoticHyperbolicAreaV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff SchwartzMap ENNReal

namespace QuantitativeMaass

/-- The actual centered cylinder column has a uniform squared norm bound
from the height-one variation of its convolution-square profile. -/
theorem cylinderTimeColumn_centered_energy_bound (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) (he : Function.Even f)
    (hr : ∀ t,star (f t)=f t) (R : ℝ) (hR : 0≤R)
    (hs : Function.support f⊆Icc (-R) R) (z : ℍ) :
    ‖cylinderTimeColumn f hc he R hR hs z-
      ∫ y in Icc (0:ℝ) 1,cylinderTimeColumn f hc he R hR hs (y+ᵥz)‖^2≤
        2*∫ v,‖deriv (parabolicLineProfile
          (abelProfile (evenCoshLift (timeConvolution f f))) 1) v‖ := by
  let F := evenCoshLift (timeConvolution f f)
  have hF : ContDiffOn ℝ ∞ F (Ici 1) :=
    evenCoshLift_smoothOn _ ((timeConvolution f f).smooth ⊤)
      (timeConvolution_even f f he he) (timeConvolution_compact f f hc hc)
  have hFs : Function.support F⊆Iic (Real.cosh (R+R)) :=
    evenCoshLift_support_of_time_support _ _ (add_nonneg hR hR)
      (timeConvolution_support f f R R hs hs)
  have hg := abelProfile_smoothOn_physical F hF (Real.cosh (R+R)) (Real.one_le_cosh _) hFs
  rw [cylinderTimeColumn_centered_kernel f hc he hr R hR hs z,←Complex.sub_re]
  exact (Complex.re_le_norm _).trans (cylinderRadialKernel_centered_bound
    (abelProfile F) hg (R+R) (add_nonneg hR hR) (abelProfile_support F _ hFs) z)

/-- An explicit finite tail integral for the genuine centered cylinder
column. This removes the constant-mode divergence before any residual
reconstruction is estimated. -/
theorem cylinderTimeColumn_centered_tail_bound (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) (he : Function.Even f)
    (hr : ∀ t,star (f t)=f t) (R : ℝ) (hR : 0≤R)
    (hs : Function.support f⊆Icc (-R) R) (Y : ℝ) (hY : 0<Y) :
    (∫⁻ z in AsymptoticCertificateOperators.highStrip Y,
      ENNReal.ofReal (‖cylinderTimeColumn f hc he R hR hs z-
        ∫ y in Icc (0:ℝ) 1,cylinderTimeColumn f hc he R hR hs (y+ᵥz)‖^2))≤
      ENNReal.ofReal (2*∫ v,‖deriv (parabolicLineProfile
        (abelProfile (evenCoshLift (timeConvolution f f))) 1) v‖)*ENNReal.ofReal Y⁻¹ := by
  calc
    _≤∫⁻ _z in AsymptoticCertificateOperators.highStrip Y,
        ENNReal.ofReal (2*∫ v,‖deriv (parabolicLineProfile
          (abelProfile (evenCoshLift (timeConvolution f f))) 1) v‖) :=
      lintegral_mono (fun z => ENNReal.ofReal_le_ofReal
        (cylinderTimeColumn_centered_energy_bound f hc he hr R hR hs z))
    _=_ := by
      have harea : volume (AsymptoticCertificateOperators.highStrip Y)=ENNReal.ofReal Y⁻¹ :=
        AsymptoticHyperbolicArea.closed_terminal_area hY
      rw [lintegral_const,Measure.restrict_apply_univ,harea]

#print axioms cylinderTimeColumn_centered_energy_bound
#print axioms cylinderTimeColumn_centered_tail_bound

end QuantitativeMaass
