module

public import QuantitativeMaassWeightedRadialRepresentativeV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson

open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The actual weighted quotient embedding intertwines radial convolution
on the completed quotient and the bounded capped cylinder operator. -/
theorem weightedQuotientEmbedding_radial (N : ℕ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v) (x : AutomorphicSpace N) :
    cylinderCappedRadialOperator g hg R hR hs ε hε v (weightedQuotientEmbedding N hε hv x)=
      weightedQuotientEmbedding N hε hv (AllLevel.radialKernelOperator N g hg R hR hs x) := by
  have he : (fun x : AutomorphicSpace N =>
      cylinderCappedRadialOperator g hg R hR hs ε hε v (weightedQuotientEmbedding N hε hv x))=
      fun x => weightedQuotientEmbedding N hε hv (AllLevel.radialKernelOperator N g hg R hR hs x) := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N)).equalizer
      ((cylinderCappedRadialOperator g hg R hR hs ε hε v).continuous.comp
        (weightedQuotientEmbedding N hε hv).continuous)
      ((weightedQuotientEmbedding N hε hv).continuous.comp
        (AllLevel.radialKernelOperator N g hg R hR hs).continuous)
    funext f
    change cylinderCappedRadialOperator g hg R hR hs ε hε v
      (weightedQuotientEmbedding N hε hv (AutomorphicL2.denseEmbedding _ _ f))=
      weightedQuotientEmbedding N hε hv
        (AllLevel.radialKernelOperator N g hg R hR hs (AutomorphicL2.denseEmbedding _ _ f))
    rw [weightedQuotientEmbedding_representative,radialKernelOperator_representative,
      weightedQuotientEmbedding_representative]
    exact cylinderCappedRadialOperator_weighted_representative N g hg R hR hs hε hv f
  exact congrFun he x

/-- In particular the normalized Abel kernel and the actual spectral
wave packet have the same weighted action at every level. -/
theorem weightedQuotientEmbedding_coshWavePacket (N : ℕ)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (x : AutomorphicSpace N) :
    cylinderCappedRadialOperator (abelProfile F) (abelProfile_smooth F hF hc)
      R hR (abelProfile_support F _ hs) ε hε v (weightedQuotientEmbedding N hε hv x)=
      weightedQuotientEmbedding N hε hv (coshWavePacket N F hF R hR hs x) := by
  have he := weightedQuotientEmbedding_radial N (abelProfile F) (abelProfile_smooth F hF hc)
    R hR (abelProfile_support F _ hs) hε hv x
  change _=weightedQuotientEmbedding N hε hv (AllLevel.abelKernelOperator N F hF hc R hR hs x) at he
  rw [AllLevel.abelKernelOperator_eq_coshWavePacket N F hF hc hr R hR hs] at he
  exact he

#print axioms weightedQuotientEmbedding_radial
#print axioms weightedQuotientEmbedding_coshWavePacket

end QuantitativeMaass
