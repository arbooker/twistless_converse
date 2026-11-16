module

public import QuantitativeMaassParabolicKernelSumV1
public import QuantitativeMaassCuspContinuousConstantV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open scoped Topology MatrixGroups ContDiff

namespace QuantitativeMaass

/-- The radial profile restricted to a horizontal line at height y. -/
def parabolicLineProfile (g : ℝ → ℂ) (y v : ℝ) : ℂ := g (1+v^2/(2*y^2))

theorem parabolicLineProfile_smooth (g : ℝ → ℂ) (hg : ContDiffOn ℝ ∞ g (Ici 1))
    (y : ℝ) : ContDiff ℝ ∞ (parabolicLineProfile g y) := by
  apply ContDiffOn.comp_contDiff hg (by fun_prop : ContDiff ℝ ∞ (fun v : ℝ => 1+v^2/(2*y^2)))
  intro v
  change 1≤1+v^2/(2*y^2)
  have hn : 0≤v^2/(2*y^2) := by positivity
  linarith

theorem equal_height_translated_cosh (z w : ℍ) (hh : z.im=w.im) (v : ℝ) :
    Real.cosh (dist (v+ᵥz) w)=1+(v+z.re-w.re)^2/(2*z.im^2) := by
  rw [cosh_dist',vadd_re,vadd_im,←hh]
  field_simp
  ring

/-- The actual high-cusp kernel is exactly a congruence-restricted integer
periodization of a single smooth real-line profile. -/
theorem radialPoincareKernel_high_cusp_line_sum (N : ℕ) (A : SL(2,ℤ))
    (g : ℝ → ℂ) (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (u : ℝ) (hu : R/2<u) (x y : ℝ) :
    radialPoincareKernel N g (cuspLogPoint N A u y) (cuspLogPoint N A u x)=
      ∑' n : {n : ℤ // (N:ℤ)∣n*(A 1 0)^2},
        parabolicLineProfile g (Real.exp u) ((n.val:ℝ)+(N:ℝ)*(x-y)) := by
  rw [cuspLogPoint,cuspLogPoint,radialPoincareKernel_high_cusp_parabolic_sum N A g R hR hs
    (horocyclePoint ((N:ℝ)*x) (Real.exp u) (Real.exp_pos u))
    (horocyclePoint ((N:ℝ)*y) (Real.exp u) (Real.exp_pos u)) rfl (Real.exp_lt_exp.mpr hu)]
  apply tsum_congr
  intro n
  rw [equal_height_translated_cosh
    (horocyclePoint ((N:ℝ)*x) (Real.exp u) (Real.exp_pos u))
    (horocyclePoint ((N:ℝ)*y) (Real.exp u) (Real.exp_pos u)) rfl]
  unfold parabolicLineProfile
  congr 2
  change ((n.val:ℝ)+(N:ℝ)*x-(N:ℝ)*y)^2/(2*(Real.exp u)^2)=
    ((n.val:ℝ)+(N:ℝ)*(x-y))^2/(2*(Real.exp u)^2)
  ring

#print axioms parabolicLineProfile_smooth
#print axioms equal_height_translated_cosh
#print axioms radialPoincareKernel_high_cusp_line_sum

end QuantitativeMaass
