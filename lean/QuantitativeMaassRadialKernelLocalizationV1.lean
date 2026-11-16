module

public import QuantitativeMaassRadialKernelUnfoldV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- A local oscillation estimate for the literal quotient convolution. The
normalization and error constant are the exact hyperbolic radial masses. -/
theorem radialKernel_output_local_error (N : ℕ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (f : ℍ → ℂ) (hf : Measurable f) (hinv : ∀ γ : gamma N, ∀ y,f (γ•y)=f y)
    (hL : MemLp f 2 (quotientMeasure N)) (x : ℍ) (ε : ℝ)
    (hnear : ∀ y ∈ Metric.closedBall x R,‖f y-f x‖≤ε) :
    ‖(radialKernelData N g hg R hR hs).output f x-
      ((2*Real.pi:ℂ)*∫ q in Ioi (1:ℝ),g q)*f x‖≤
        (2*Real.pi*(∫ q in Ioi (1:ℝ),‖g q‖))*ε := by
  let φ : ℍ → ℂ := fun y => g (Real.cosh (dist y x))
  have hφ : Integrable φ := hyperbolic_radial_integrable g hg.continuous x R hR hs
  have hu := radialKernel_output_unfold N g hg R hR hs f hf hinv hL x
  have hi : Integrable (fun y => φ y*(f y-f x)) := by
    have hh := hu.1.sub (hφ.mul_const (f x))
    change Integrable (fun y => φ y*f y-φ y*f x) at hh
    simpa only [mul_sub] using hh
  have he : (radialKernelData N g hg R hR hs).output f x-
      ((2*Real.pi:ℂ)*∫ q in Ioi (1:ℝ),g q)*f x=∫ y,φ y*(f y-f x) := by
    simp_rw [mul_sub]
    rw [integral_sub hu.1 (hφ.mul_const (f x)),integral_mul_const,hu.2]
    rw [integral_hyperbolic_radial]
  rw [he]
  calc
    _ ≤ ∫ y,‖φ y*(f y-f x)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y,‖φ y‖*ε := by
      apply integral_mono hi.norm (hφ.norm.mul_const ε)
      intro y
      dsimp only
      rw [norm_mul]
      by_cases hy : φ y=0
      · simp [hy]
      · apply mul_le_mul_of_nonneg_left (hnear y ?_) (norm_nonneg _)
        have hb := Real.cosh_le_cosh.mp (hs hy)
        rw [abs_of_nonneg dist_nonneg,abs_of_nonneg hR] at hb
        exact hb
    _ = _ := by
      rw [integral_mul_const]
      change (∫ y : ℍ,‖g (Real.cosh (dist y x))‖)*ε=_
      rw [integral_hyperbolic_radial_norm]

#print axioms radialKernel_output_local_error

end QuantitativeMaass
