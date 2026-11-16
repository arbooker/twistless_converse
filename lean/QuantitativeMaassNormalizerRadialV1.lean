module

public import QuantitativeMaassWeightedRadialRepresentativeV1
public import QuantitativeMaassNormalizerActionV1
public import QuantitativeMaassCorrespondenceKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem rationalNormalizer_action_dist (g : AsymptoticRationalGroup.Group) (z w : ℍ) :
    dist (g•z) (g•w)=dist z w := by
  rw [←AsymptoticSlashGauge.representative_action g z,
    ←AsymptoticSlashGauge.representative_action g w]
  exact positiveGL_action_dist _
    (AsymptoticRationalGroup.representative_positive g (AsymptoticSlashGauge.representative_spec g)) z w

/-- Change of variables in the actual hyperbolic convolution proves
normalizer commutation before passage to the Hilbert completion. -/
theorem radialOutputRepresentative_normalizer (N : ℕ) (g : quotientNormalizerGroup N)
    (h : ℝ → ℂ) (hh : ContDiff ℝ ∞ h) (R : ℝ) (hR : 0≤R)
    (hs : Function.support h⊆Iic (Real.cosh R))
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    quotientNormalizerRepresentative N g (radialOutputRepresentative N h hh R hR hs f)=
      radialOutputRepresentative N h hh R hR hs (quotientNormalizerRepresentative N g f) := by
  apply Subtype.ext
  funext z
  change (radialKernelData N h hh R hR hs).output f.val (g.val • z)=
    (radialKernelData N h hh R hR hs).output (quotientNormalizerRepresentative N g f).val z
  rw [(radialKernel_output_unfold N h hh R hR hs f.val f.property.1
    f.property.2.1 f.property.2.2 (g.val • z)).2,
    (radialKernel_output_unfold N h hh R hR hs (quotientNormalizerRepresentative N g f).val
      (quotientNormalizerRepresentative N g f).property.1
      (quotientNormalizerRepresentative N g f).property.2.1
      (quotientNormalizerRepresentative N g f).property.2.2 z).2]
  let : ContinuousConstSMul AsymptoticRationalGroup.Group ℍ :=
    ⟨AsymptoticRationalBranches.action_continuous⟩
  have he := (AsymptoticRationalGroup.measurePreserving g.val).integral_comp
    (Homeomorph.smul g.val).measurableEmbedding
    (fun y : ℍ => h (Real.cosh (dist y (g.val • z)))*f.val y)
  symm
  change (∫ y : ℍ,h (Real.cosh (dist y z))*f.val (g.val • y))=
    ∫ y : ℍ,h (Real.cosh (dist y (g.val • z)))*f.val y
  simpa only [rationalNormalizer_action_dist] using he

/-- Every rational normalizer commutes with the actual radial operator
on all completed automorphic vectors. -/
theorem quotientNormalizerPullback_radial (N : ℕ) (g : quotientNormalizerGroup N)
    (h : ℝ → ℂ) (hh : ContDiff ℝ ∞ h) (R : ℝ) (hR : 0≤R)
    (hs : Function.support h⊆Iic (Real.cosh R)) (x : AutomorphicSpace N) :
    quotientNormalizerPullback N g (AllLevel.radialKernelOperator N h hh R hR hs x)=
      AllLevel.radialKernelOperator N h hh R hR hs (quotientNormalizerPullback N g x) := by
  have he : (fun x : AutomorphicSpace N =>
      quotientNormalizerPullback N g (AllLevel.radialKernelOperator N h hh R hR hs x))=
      fun x => AllLevel.radialKernelOperator N h hh R hR hs (quotientNormalizerPullback N g x) := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N)).equalizer
      ((quotientNormalizerPullback N g).continuous.comp
        (AllLevel.radialKernelOperator N h hh R hR hs).continuous)
      ((AllLevel.radialKernelOperator N h hh R hR hs).continuous.comp
        (quotientNormalizerPullback N g).continuous)
    funext f
    change quotientNormalizerPullback N g
      (AllLevel.radialKernelOperator N h hh R hR hs (AutomorphicL2.denseEmbedding _ _ f))=
      AllLevel.radialKernelOperator N h hh R hR hs
        (quotientNormalizerPullback N g (AutomorphicL2.denseEmbedding _ _ f))
    rw [radialKernelOperator_representative,quotientNormalizerPullback_representative,
      quotientNormalizerPullback_representative,radialKernelOperator_representative,
      radialOutputRepresentative_normalizer]
  exact congrFun he x

#print axioms rationalNormalizer_action_dist
#print axioms radialOutputRepresentative_normalizer
#print axioms quotientNormalizerPullback_radial

end QuantitativeMaass
