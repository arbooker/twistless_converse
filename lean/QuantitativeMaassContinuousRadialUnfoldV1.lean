module

public import QuantitativeMaassCylinderPhysicalV1
public import QuantitativeMaassRadialKernelUnfoldV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Compact radial kernels unfold against every continuous invariant
function. Global quotient L2 membership of that function is unnecessary:
the unperiodized product has compact support and is absolutely integrable. -/
theorem continuous_radial_output_unfold (N : ℕ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (f : ℍ → ℂ) (hf : Continuous f) (hinv : ∀ γ : gamma N,∀ y,f (γ•y)=f y)
    (x : ℍ) :
    Integrable (fun y : ℍ => g (Real.cosh (dist y x))*f y) ∧
      Integrable (fun y => radialPoincareKernel N g x y*f y) (quotientMeasure N) ∧
      (radialKernelData N g hg R hR hs).output f x=
        ∫ y : ℍ,g (Real.cosh (dist y x))*f y := by
  let u := radialSeed g hg x R hR hs
  have hc : Continuous (fun y => upperFunction u.toFun y*f y) :=
    (upperFunction_continuous u.smooth).mul hf
  have hi : Integrable (fun y => upperFunction u.toFun y*f y) volume :=
    hc.integrable_of_hasCompactSupport u.compact.mul_right
  have hu := integral_poincare_unfold volume
    (fun γ : gamma N => AsymptoticRationalGroup.measurePreserving γ.val)
    (density N) (density_measurable N) (density_orbit_sum N)
    (fun y => upperFunction u.toFun y*f y) hc.measurable hi
  have he (y : ℍ) : (∑' γ : gamma N,upperFunction u.toFun (γ•y)*f (γ•y))=
      radialPoincareKernel N g x y*f y := by
    simp_rw [hinv]
    exact tsum_mul_right
  simp_rw [he] at hu
  have hu0 (y : ℍ) : upperFunction u.toFun y=g (Real.cosh (dist y x)) :=
    radialFunction_upper g x y
  refine ⟨?_,hu.1,?_⟩
  · simpa only [hu0] using hi
  · simpa only [hu0] using! hu.2

theorem principalEulerPhysical_cylinder_invariant (b : ℕ → ℂ) (r : ℝ) (σ : ℕ)
    (γ : gamma 0) (z : ℍ) :
    principalEulerPhysical b r σ (γ.val • z : ℍ)=principalEulerPhysical b r σ z := by
  obtain ⟨n,hn⟩ := gamma_zero_translation γ
  change principalEulerWave b r σ ((γ.val • z).re,(γ.val • z).im)=
    principalEulerWave b r σ (z.re,z.im)
  rw [hn,translation_re,AsymptoticCompactTranslation.label_im]
  have h := (principalEulerWave_periodic b r σ z.im).int_mul n z.re
  simpa only [zsmul_eq_mul,mul_one] using h

#print axioms continuous_radial_output_unfold
#print axioms principalEulerPhysical_cylinder_invariant

end QuantitativeMaass
