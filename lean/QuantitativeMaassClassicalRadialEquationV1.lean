module

public import QuantitativeMaassGreenUpperV1
public import QuantitativeMaassAbelKernelGraphV1
public import QuantitativeMaassEulerSmoothV1
public import QuantitativeMaassEulerWaveEquationV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem radial_convolution_integrable (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (f : ℍ → ℂ) (hf : Continuous f) (x : ℍ) :
    Integrable (fun y : ℍ => g (Real.cosh (dist y x))*f y) := by
  let u := radialSeed g hg x R hR hs
  have hi : Integrable (fun y : ℍ => upperFunction u.toFun y*f y) volume :=
    ((upperFunction_continuous u.smooth).mul hf).integrable_of_hasCompactSupport
    u.compact.mul_right
  change Integrable (fun y : ℍ => upperFunction (radialFunction g x) y*f y) volume at hi
  simpa only [radialFunction_upper] using! hi

/-- Green's formula transfers the actual classical Laplace equation to
compact radial convolution. The eigenfunction need not be globally L2. -/
theorem classical_radial_convolution_eigen (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hr : ∀ q,star (g q)=g q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support g⊆Iic (Real.cosh R))
    (u : ℝ×ℝ → ℂ) (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2}) (e : ℂ)
    (he : ∀ y : ℍ,upperLaplacian u y=e*upperFunction u y) (x : ℍ) :
    (∫ y : ℍ,radialLaplacianProfile g (Real.cosh (dist y x))*upperFunction u y)=
      e*(∫ y : ℍ,g (Real.cosh (dist y x))*upperFunction u y) := by
  have h := upper_green_symmetric (radialFunction_smooth g hg x) hu
    (radialSeed g hg x R hR hs).compact
  simp_rw [radialFunction_upper,radialFunction_laplacian g hg,hr,
    radialLaplacianProfile_real g hr,he,mul_left_comm (g _) e] at h
  rw [integral_const_mul] at h
  exact h.symm

/-- The literal Abel convolution satisfies the scalar tested wave equation
at every point, directly from the classical PDE and compact Green symmetry. -/
theorem classical_abel_convolution_equation (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (hr : ∀ q,star (F q)=F q)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (u : ℝ×ℝ → ℂ) (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2}) (e : ℂ)
    (he : ∀ y : ℍ,upperLaplacian u y=e*upperFunction u y) (x : ℍ) :
    (∫ y : ℍ,abelProfile (coshTimeOperator F) (Real.cosh (dist y x))*upperFunction u y)=
      (1/4-e)*(∫ y : ℍ,abelProfile F (Real.cosh (dist y x))*upperFunction u y) := by
  have hg := abelProfile_smooth F hF hc
  have hsg := abelProfile_support F _ hs
  have hH := abelProfile_smooth (coshTimeOperator F) (coshTimeOperator_smooth F hF)
    (coshTimeOperator_compact F hc)
  have hsH := abelProfile_support (coshTimeOperator F) _ (coshTimeOperator_support F _ hs)
  have hi := radial_convolution_integrable (abelProfile F) hg R hR hsg
    (upperFunction u) (upperFunction_continuous hu) x
  have hj := radial_convolution_integrable (abelProfile (coshTimeOperator F)) hH R hR hsH
    (upperFunction u) (upperFunction_continuous hu) x
  have heq := classical_radial_convolution_eigen (abelProfile F) hg
    (abelProfile_real F hr) R hR hsg u hu e he x
  simp_rw [abelProfile_laplacian F hF hc,sub_mul,mul_assoc] at heq
  rw [integral_sub (hi.const_mul (1/4:ℂ)) hj,integral_const_mul] at heq
  linear_combination -heq

#print axioms radial_convolution_integrable
#print axioms classical_radial_convolution_eigen
#print axioms classical_abel_convolution_equation

end QuantitativeMaass
