module

public import QuantitativeMaassAbelNormalizedKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

def abelNormalizedOperator (N : ℕ) [NeZero N] (R : ℝ) (hR : 0<R) :
    AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  radialKernelOperator N (abelNormalizedProfile R) (abelNormalizedProfile_smooth R hR)
    R hR.le (abelNormalizedProfile_support R hR)

theorem abelNormalizedOperator_norm (N : ℕ) [NeZero N] (R : ℝ) (hR : 0<R) :
    ‖abelNormalizedOperator N R hR‖≤1 := by
  have h := radialKernelOperator_norm N (abelNormalizedProfile R)
    (abelNormalizedProfile_smooth R hR) R hR.le (abelNormalizedProfile_support R hR)
  rwa [abelNormalizedProfile_norm_mass R hR] at h

theorem abelNormalizedOperator_apply_norm (N : ℕ) [NeZero N] (R : ℝ) (hR : 0<R)
    (f : AutomorphicSpace N) : ‖abelNormalizedOperator N R hR f‖≤‖f‖ := by
  have h := ((abelNormalizedOperator N R hR).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (abelNormalizedOperator_norm N R hR) (norm_nonneg f))
  simpa only [one_mul] using h

/-- A bounded invariant input has the same pointwise bound after normalized
Abel convolution. This follows from the actual unfolded integral and mass1. -/
theorem abelNormalizedProfile_output_bound (N : ℕ) (R : ℝ) (hR : 0<R)
    (f : ℍ → ℂ) (hf : Measurable f) (hinv : ∀ γ : gamma N, ∀ y,f (γ•y)=f y)
    (hL : MemLp f 2 (quotientMeasure N)) (B : ℝ) (hb : ∀ y,‖f y‖≤B) (x : ℍ) :
    ‖(radialKernelData N (abelNormalizedProfile R) (abelNormalizedProfile_smooth R hR)
      R hR.le (abelNormalizedProfile_support R hR)).output f x‖≤B := by
  let g := abelNormalizedProfile R
  have hg := abelNormalizedProfile_smooth R hR
  have hs := abelNormalizedProfile_support R hR
  have hu := radialKernel_output_unfold N g hg R hR.le hs f hf hinv hL x
  have hi := hyperbolic_radial_integrable g hg.continuous x R hR.le hs
  rw [hu.2]
  calc
    _ ≤ ∫ y : ℍ,‖g (Real.cosh (dist y x))*f y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℍ,‖g (Real.cosh (dist y x))‖*B := by
      apply integral_mono hu.1.norm (hi.norm.mul_const B)
      intro y
      dsimp only
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb y) (norm_nonneg _)
    _ = B := by
      rw [integral_mul_const,integral_hyperbolic_radial_norm,
        abelNormalizedProfile_norm_mass R hR,one_mul]

#print axioms abelNormalizedOperator_norm
#print axioms abelNormalizedOperator_apply_norm
#print axioms abelNormalizedProfile_output_bound

end QuantitativeMaass
