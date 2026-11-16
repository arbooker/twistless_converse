module

public import QuantitativeMaassRadialKernelOperatorV1
public import QuantitativeMaassTranslationQuotientV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff ENNReal

namespace QuantitativeMaass.AllLevel

variable (N : ℕ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
  (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))

/-- The constructed ambient L2 integral operator lands in the actual
closed automorphic subspace, through a measurable invariant representative. -/
theorem radialKernel_operator_mem (f : Lp ℂ 2 (quotientMeasure N)) :
    (radialKernelData N g hg R hR hs).operator f∈AutomorphicSpace N := by
  let D := radialKernelData N g hg R hR hs
  have hm : D.output f∈AutomorphicL2.representatives (gamma N) (quotientMeasure N) := by
    refine ⟨D.output_measurable f (Lp.stronglyMeasurable f).measurable,?_,
      D.output_memLp f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)⟩
    intro γ x
    exact radialKernel_output_invariant N g hg R hR hs f γ x
  apply (LinearMap.range (AutomorphicL2.embedding (gamma N) (quotientMeasure N))).le_topologicalClosure
  refine ⟨⟨D.output f,hm⟩,?_⟩
  apply Lp.ext
  filter_upwards [hm.2.2.coeFn_toLp,D.operator_coeFn f] with x hx hy
  exact hx.trans hy.symm

/-- The radial kernel as a bounded operator on the genuine quotient
Hilbert space. No spectral or trace identity is assumed. -/
def radialKernelOperator : AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  (((radialKernelData N g hg R hR hs).operator).comp (AutomorphicSpace N).subtypeL).codRestrict
    (AutomorphicSpace N) (fun f => radialKernel_operator_mem N g hg R hR hs f.val)

theorem radialKernelOperator_coeFn (f : AutomorphicSpace N) :
    (radialKernelOperator N g hg R hR hs f).val=ᵐ[quotientMeasure N]
      (fun x => ∫ y,radialPoincareKernel N g x y*f.val y ∂quotientMeasure N) :=
  (radialKernelData N g hg R hR hs).operator_coeFn f.val

theorem radialKernelOperator_norm :
    ‖radialKernelOperator N g hg R hR hs‖≤2*Real.pi*(∫ q in Ioi (1:ℝ),‖g q‖) := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (by positivity) (integral_nonneg (fun _ => norm_nonneg _)))
  intro f
  exact (radialKernelData N g hg R hR hs).linear_norm f.val

/-- The normalized Abel profile now gives an actual bounded quotient
integral operator. Its equality with the spectral wave packet remains to prove. -/
def abelKernelOperator (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) :
    AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  radialKernelOperator N (abelProfile F) (abelProfile_smooth F hF hc) R hR (abelProfile_support F _ hs)

theorem radialKernelOperator_eq_positive [NeZero N] :
    radialKernelOperator N g hg R hR hs =
      QuantitativeMaass.radialKernelOperator N g hg R hR hs := rfl

#print axioms radialKernel_operator_mem
#print axioms radialKernelOperator_coeFn
#print axioms radialKernelOperator_norm
#print axioms radialKernelOperator_eq_positive
#print axioms abelKernelOperator

end QuantitativeMaass.AllLevel
