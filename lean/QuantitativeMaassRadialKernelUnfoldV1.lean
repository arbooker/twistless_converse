module

public import QuantitativeMaassRadialKernelOperatorV1
public import QuantitativeMaassPoincarePairingV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The actual quotient kernel output unfolds to an absolutely integrable
hyperbolic convolution for every invariant measurable L2 representative. -/
theorem radialKernel_output_unfold (N : ℕ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (f : ℍ → ℂ) (hf : Measurable f) (hinv : ∀ γ : gamma N, ∀ y,f (γ•y)=f y)
    (hL : MemLp f 2 (quotientMeasure N)) (x : ℍ) :
    Integrable (fun y : ℍ => g (Real.cosh (dist y x))*f y) ∧
      (radialKernelData N g hg R hR hs).output f x=
        ∫ y : ℍ,g (Real.cosh (dist y x))*f y := by
  let : ContinuousConstSMul (gamma N) ℍ :=
    ⟨fun γ => AsymptoticRationalBranches.action_continuous γ.val⟩
  let u := radialSeed g hg x R hR hs
  have hu := integral_poincare_pairing volume
    (fun γ : gamma N => AsymptoticRationalGroup.measurePreserving γ.val)
    (density N) (density_measurable N) (density_orbit_sum N)
    (fun y => star (f y)) (continuous_star.measurable.comp hf)
    (fun γ y => congrArg star (hinv γ y)) hL.star
    (upperFunction u.toFun) (upperFunction_continuous u.smooth) u.compact
  have he (y : ℍ) : upperFunction u.toFun y=g (Real.cosh (dist y x)) :=
    radialFunction_upper g x y
  constructor
  · simpa only [star_star,he,mul_comm] using hu.1
  · change (∫ y,radialPoincareKernel N g x y*f y ∂quotientMeasure N)=_
    have h := hu.2.2
    change (∫ y,star (star (f y))*radialPoincareKernel N g x y ∂quotientMeasure N)=
      ∫ y : ℍ,star (star (f y))*upperFunction (radialFunction g x) y at h
    simpa only [star_star,radialFunction_upper,mul_comm] using h

#print axioms radialKernel_output_unfold

end QuantitativeMaass
