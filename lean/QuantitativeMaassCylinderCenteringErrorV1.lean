module

public import QuantitativeMaassCylinderCrossMeanV1
public import QuantitativeMaassParabolicMassBoundV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff SchwartzMap

namespace QuantitativeMaass

variable (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
  (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
  (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)

include hr

/-- An explicit off-diagonal amplitude controls the genuine horizontal
mean energy, with no spectral-resolution assumption. -/
theorem cylinderTimeColumn_mean_energy_bound (C : ℝ) (hC : 0≤C)
    (hb : ∀ d : ℝ,0<d →
      ‖abelProfile (evenCoshLift (timeConvolution f f)) (Real.cosh d)‖≤C/Real.sqrt (Real.sinh d))
    (z : ℍ) :
    ‖∫ y in Icc (0:ℝ) 1,cylinderTimeColumn f hc he R hR hs (y+ᵥz)‖^2≤
      z.im*(C*(Real.pi*(2*(2*(|Real.cosh (2*R)|+1)+1)+2))) := by
  rw [cylinderTimeColumn_mean_energy f hc he hr R hR hs]
  apply mul_le_mul_of_nonneg_left _ z.im_pos.le
  apply (Complex.re_le_norm _).trans
  have hgs : Function.support (timeConvolution f f : ℝ→ℂ)⊆Icc (-(2*R)) (2*R) := by
    simpa only [two_mul] using timeConvolution_support f f R R hs hs
  exact parabolicLineProfile_mass_bound _ (Real.cosh (2*R)) C hC
    (abelProfile_support _ _ (evenCoshLift_support_of_time_support _ _ (by positivity) hgs)) hb

/-- Exact cross-kernel correction after deleting the horizontal constant
mode at both points. -/
theorem cylinderTimeColumn_centered_cross (z w : ℍ) :
    inner ℂ
      (cylinderTimeColumn f hc he R hR hs w-
        ∫ y in Icc (0:ℝ) 1,cylinderTimeColumn f hc he R hR hs (y+ᵥw))
      (cylinderTimeColumn f hc he R hR hs z-
        ∫ y in Icc (0:ℝ) 1,cylinderTimeColumn f hc he R hR hs (y+ᵥz))=
      radialPoincareKernel 0 (abelProfile (evenCoshLift (timeConvolution f f))) z w-
      inner ℂ (∫ y in Icc (0:ℝ) 1,cylinderTimeColumn f hc he R hR hs (y+ᵥw))
        (∫ y in Icc (0:ℝ) 1,cylinderTimeColumn f hc he R hR hs (y+ᵥz)) := by
  have h1 := cylinderTimeColumn_cross_mean f hc he hr R hR hs w z
  have h2 := congrArg (starRingEnd ℂ) (cylinderTimeColumn_cross_mean f hc he hr R hR hs z w)
  simp only [inner_conj_symm] at h2
  rw [inner_sub_left,inner_sub_right,inner_sub_right,h1,h2,
    cylinderTimeSquare_kernel_cross f hc he hr R hR hs]
  abel

/-- The mean correction costs the off-diagonal amplitude, rather than
its geometric mean with the full diagonal energy. -/
theorem cylinderTimeColumn_centering_error (C : ℝ) (hC : 0≤C)
    (hb : ∀ d : ℝ,0<d →
      ‖abelProfile (evenCoshLift (timeConvolution f f)) (Real.cosh d)‖≤C/Real.sqrt (Real.sinh d))
    (z w : ℍ) :
    ‖inner ℂ
      (cylinderTimeColumn f hc he R hR hs w-
        ∫ y in Icc (0:ℝ) 1,cylinderTimeColumn f hc he R hR hs (y+ᵥw))
      (cylinderTimeColumn f hc he R hR hs z-
        ∫ y in Icc (0:ℝ) 1,cylinderTimeColumn f hc he R hR hs (y+ᵥz))-
      radialPoincareKernel 0 (abelProfile (evenCoshLift (timeConvolution f f))) z w‖≤
      (C*(Real.pi*(2*(2*(|Real.cosh (2*R)|+1)+1)+2)))*(z.im+w.im)/2 := by
  rw [cylinderTimeColumn_centered_cross f hc he hr R hR hs]
  rw [sub_sub_cancel_left,norm_neg]
  apply (norm_inner_le_norm _ _).trans
  have hz := cylinderTimeColumn_mean_energy_bound f hc he hr R hR hs C hC hb z
  have hw := cylinderTimeColumn_mean_energy_bound f hc he hr R hR hs C hC hb w
  nlinarith [sq_nonneg (‖∫ y in Icc (0:ℝ) 1,cylinderTimeColumn f hc he R hR hs (y+ᵥz)‖-
    ‖∫ y in Icc (0:ℝ) 1,cylinderTimeColumn f hc he R hR hs (y+ᵥw)‖)]

#print axioms cylinderTimeColumn_mean_energy_bound
#print axioms cylinderTimeColumn_centered_cross
#print axioms cylinderTimeColumn_centering_error

end QuantitativeMaass
