module

public import QuantitativeMaassRadialKernelMassV1

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Joint measurability of the literal projective quotient kernel, proved
from its countable series rather than postulated for an abstract kernel. -/
theorem radialPoincareKernel_joint_measurable (N : ℕ) (g : ℝ → ℂ) (hg : Continuous g) :
    Measurable (fun p : ℍ×ℍ => radialPoincareKernel N g p.1 p.2) := by
  let : ContinuousConstSMul (gamma N) ℍ :=
    ⟨fun γ => AsymptoticRationalBranches.action_continuous γ.val⟩
  have he (w z : ℍ) : radialPoincareKernel N g w z=
      ∑' γ : gamma N,g (Real.cosh (dist (γ•z) w)) := by
    simp only [radialPoincareKernel,poincareSum,radialFunction_upper]
  simp_rw [he]
  apply Measurable.tsum
  intro γ
  exact (hg.comp (Real.continuous_cosh.comp
    (((continuous_const_smul γ).comp continuous_snd).dist continuous_fst))).measurable

/-- Both Schur integral bounds hold with one centre-independent finite real
constant, and the actual kernel is jointly measurable. The bounded L2
operator construction and spectral equality are separate remaining steps. -/
theorem radialPoincareKernel_schur_bounds (N : ℕ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R)) :
    ∃ C : ℝ, 0≤C ∧
      Measurable (fun p : ℍ×ℍ => radialPoincareKernel N g p.1 p.2) ∧
      (∀ w, Integrable (radialPoincareKernel N g w) (quotientMeasure N) ∧
        (∫ z,‖radialPoincareKernel N g w z‖ ∂quotientMeasure N)≤C) ∧
      (∀ z, (∫ w,‖radialPoincareKernel N g w z‖ ∂quotientMeasure N)≤C) := by
  refine ⟨2*Real.pi*(∫ q in Ioi (1:ℝ),‖g q‖),
    mul_nonneg (by positivity) (integral_nonneg (fun _ => norm_nonneg _)),
    radialPoincareKernel_joint_measurable N g hg.continuous,?_,?_⟩
  · intro w
    exact ⟨(radialPoincareKernel_mass N g hg w R hR hs).1,
      radialPoincareKernel_integral_norm_le N g hg w R hR hs⟩
  · intro z
    exact radialPoincareKernel_row_norm_le N g hg z R hR hs

#print axioms radialPoincareKernel_joint_measurable
#print axioms radialPoincareKernel_schur_bounds

end QuantitativeMaass
