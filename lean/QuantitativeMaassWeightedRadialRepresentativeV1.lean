module

public import QuantitativeMaassWeightedQuotientEmbeddingV1
public import QuantitativeMaassCylinderKernelActionV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticCompactBranch
open AsymptoticIntegralSubgroup

open scoped Topology ContDiff

namespace QuantitativeMaass

/-- A radial output is independent of the quotient used to unfold it.
Only one quotient L2 hypothesis is needed. -/
theorem radial_output_change_level (N M : ℕ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hfM : ∀ γ : gamma M,∀ y,f.val (γ.val • y)=f.val y) (x : ℍ) :
    (radialKernelData M g hg R hR hs).output f.val x=
      (radialKernelData N g hg R hR hs).output f.val x := by
  have hN := radialKernel_output_unfold N g hg R hR hs f.val f.property.1
    f.property.2.1 f.property.2.2 x
  let u := radialSeed g hg x R hR hs
  have hu0 (y : ℍ) : upperFunction u.toFun y=g (Real.cosh (dist y x)) :=
    radialFunction_upper g x y
  have hi : Integrable (fun y => upperFunction u.toFun y*f.val y) volume := by
    simpa only [hu0] using hN.1
  have hu := integral_poincare_unfold volume
    (fun γ : gamma M => AsymptoticRationalGroup.measurePreserving γ.val)
    (density M) (density_measurable M) (density_orbit_sum M)
    (fun y => upperFunction u.toFun y*f.val y)
    ((upperFunction_continuous u.smooth).measurable.mul f.property.1) hi
  have he (y : ℍ) : (∑' γ : gamma M,upperFunction u.toFun (γ•y)*f.val (γ•y))=
      radialPoincareKernel M g x y*f.val y := by
    have hfi (γ : gamma M) (y : ℍ) : f.val (γ•y)=f.val y := hfM γ y
    simp_rw [hfi]
    exact tsum_mul_right
  simp_rw [he] at hu
  rw [hN.2]
  simpa only [hu0] using! hu.2

def radialOutputRepresentative (N : ℕ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    AutomorphicL2.representatives (gamma N) (quotientMeasure N) :=
  ⟨(radialKernelData N g hg R hR hs).output f.val,
    (radialKernelData N g hg R hR hs).output_measurable f.val f.property.1,
    radialKernel_output_invariant N g hg R hR hs f.val,
    (radialKernelData N g hg R hR hs).output_memLp f.val f.property.1 f.property.2.2⟩

theorem radialKernelOperator_representative (N : ℕ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    AllLevel.radialKernelOperator N g hg R hR hs (AutomorphicL2.denseEmbedding _ _ f)=
      AutomorphicL2.denseEmbedding _ _ (radialOutputRepresentative N g hg R hR hs f) := by
  apply Subtype.ext
  apply Lp.ext
  have he : ((AutomorphicL2.denseEmbedding _ _ f).val : ℍ → ℂ)=ᵐ[quotientMeasure N] f.val :=
    f.property.2.2.coeFn_toLp
  have ho := (radialKernelData N g hg R hR hs).output_congr_ae he
  filter_upwards [AllLevel.radialKernelOperator_coeFn N g hg R hR hs
    (AutomorphicL2.denseEmbedding _ _ f),
    (radialOutputRepresentative N g hg R hR hs f).property.2.2.coeFn_toLp] with x hx hy
  exact hx.trans ((congrFun ho x).trans hy.symm)

/-- On every measurable quotient representative, the bounded weighted
cylinder operator is exactly the weighted quotient radial output. -/
theorem cylinderCappedRadialOperator_weighted_representative (N : ℕ)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (R : ℝ) (hR : 0≤R)
    (hs : Function.support g⊆Iic (Real.cosh R)) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    cylinderCappedRadialOperator g hg R hR hs ε hε v
      (weightedQuotientRepresentative N hε hv f)=
      weightedQuotientRepresentative N hε hv (radialOutputRepresentative N g hg R hR hs f) := by
  let F := weightedQuotientRepresentative N hε hv f
  have hF : F=ᵐ[quotientMeasure 0] (fun y => (cappedHeightWeight ε v y:ℂ)*f.val y) :=
    (weightedRepresentative_memLp N hε hv f).coeFn_toLp
  have he : (fun y => (Real.exp (-Real.log (cappedHeightWeight ε v y)):ℂ)*F y)=ᵐ[quotientMeasure 0] f.val := by
    filter_upwards [hF] with y hy
    rw [hy,cappedHeightWeight_inverse_cancel hε]
  have ho := (radialKernelData 0 g hg R hR hs).output_congr_ae he
  have hi : ∀ γ : gamma 0,∀ y,f.val (γ.val • y)=f.val y := by
    intro γ y
    exact f.property.2.1 ⟨γ.val,gamma_le_of_dvd (dvd_zero N) γ.property⟩ y
  apply Lp.ext
  filter_upwards [cylinderCappedRadialOperator_kernel_coeFn g hg R hR hs ε hε v F,
    (weightedRepresentative_memLp N hε hv (radialOutputRepresentative N g hg R hR hs f)).coeFn_toLp]
    with x hx hy
  rw [hx,ho,radial_output_change_level N 0 g hg R hR hs f hi]
  exact hy.symm

#print axioms radial_output_change_level
#print axioms radialKernelOperator_representative
#print axioms cylinderCappedRadialOperator_weighted_representative

end QuantitativeMaass
