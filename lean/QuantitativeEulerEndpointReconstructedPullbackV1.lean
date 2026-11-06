module

public import QuantitativeEulerEndpointReconstructedInverseV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared

open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic QuantitativeEulerEndpointIsometricImage
open AsymptoticRegularReconstruction AsymptoticFiniteBranch AsymptoticRegularTrace
open AsymptoticSubgroupSupport AsymptoticIntegralSubgroup MeasureTheory ContinuousLinearMap

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)
variable (hN : 0 < N) (P : Parameters A) (e : Sector N)
variable (F V : UpperHalfPlane → Submodule ℂ RegularSpace)
variable [∀ z, CompleteSpace (F z)] [∀ z, CompleteSpace (V z)]
variable (hF : ∀ z, F z ≤ TerminalSpace A (AsymptoticReconstructedCount.parameters A P) z)
variable (hV : ∀ z, V z ≤ reconstructedImage A hN P e F hF z)

include hF hV in
omit [∀ z, CompleteSpace (V z)] in
theorem reconstruction_adjoint_norm_on (z : UpperHalfPlane) (y : RegularSpace)
    (hy : y ∈ V z) :
    ‖(normalizedRegularAmbientCountReconstruction A hN P e z).adjoint y‖ = ‖y‖ :=
  (reconstructed_image_inverse A hN P e F hF z y (hV z hy)).2.2

/-- Pull a surviving reconstructed subspace back by the actual adjoint.
This is a closed isometric image, rather than an assumed inverse subspace. -/
def reconstructedPullback (z : UpperHalfPlane) : Submodule ℂ RegularSpace :=
  imageSpace (normalizedRegularAmbientCountReconstruction A hN P e z).adjoint (V z)
    (reconstruction_adjoint_norm_on A hN P e F V hF hV z)

instance reconstructedPullback_complete (z : UpperHalfPlane) :
    CompleteSpace (reconstructedPullback A hN P e F V hF hV z) :=
  imageSpace_complete _ _ _

theorem reconstructed_pullback_projection (z : UpperHalfPlane) :
    (reconstructedPullback A hN P e F V hF hV z).starProjection =
      (normalizedRegularAmbientCountReconstruction A hN P e z).adjoint.comp
        ((V z).starProjection.comp (normalizedRegularAmbientCountReconstruction A hN P e z)) := by
  exact (image_projection _ _ _).trans (by rw [adjoint_adjoint])

theorem reconstructed_pullback_le (z : UpperHalfPlane) :
    reconstructedPullback A hN P e F V hF hV z ≤ F z := by
  rintro v ⟨y, he⟩
  have hm := (reconstructed_image_inverse A hN P e F hF z y (hV z y.property)).1
  exact he ▸ hm

/-- Forward reconstruction takes every pulled vector back into the surviving
image subspace, with exactly the same norm. -/
theorem reconstructed_pullback_forward (z : UpperHalfPlane) (v : RegularSpace)
    (hv : v ∈ reconstructedPullback A hN P e F V hF hV z) :
    normalizedRegularAmbientCountReconstruction A hN P e z v ∈ V z ∧
      ‖normalizedRegularAmbientCountReconstruction A hN P e z v‖ = ‖v‖ := by
  rcases hv with ⟨y, he⟩
  let U := normalizedRegularAmbientCountReconstruction A hN P e z
  have hi := reconstructed_image_inverse A hN P e F hF z y (hV z y.property)
  have hy : U v = (y : RegularSpace) := (congrArg U he).symm.trans hi.2.1
  exact ⟨hy.symm ▸ y.property, (congrArg norm hy).trans (hi.2.2.symm.trans (congrArg norm he))⟩

theorem reconstructed_pullback_trace
    (hmV : ∀ g k, Measurable (fun z => matrix (V z).starProjection g k))
    (hcV : Covariant (fun z => (V z).starProjection)) :
    trace volume (fun z => (reconstructedPullback A hN P e F V hF hV z).starProjection) =
      trace volume (fun z => (V z).starProjection) := by
  have hU := normalizedRegularCountReconstruction_regular A hN P e
  exact image_trace volume AsymptoticRationalGroup.measurePreserving _ V _
    (matrix_adjoint_measurable _ hU.1) (covariant_adjoint _ hU.2) hmV hcV

theorem reconstructed_pullback_regular
    (hmV : ∀ g k, Measurable (fun z => matrix (V z).starProjection g k))
    (hcV : Covariant (fun z => (V z).starProjection)) :
    (∀ g k, Measurable (fun z => matrix (reconstructedPullback A hN P e F V hF hV z).starProjection g k)) ∧
      Covariant (fun z => (reconstructedPullback A hN P e F V hF hV z).starProjection) := by
  have hU := normalizedRegularCountReconstruction_regular A hN P e
  simp only [reconstructed_pullback_projection]
  exact ⟨matrix_comp_measurable _ _ (matrix_adjoint_measurable _ hU.1)
    (matrix_comp_measurable _ _ hmV hU.1),
    covariant_comp _ _ (covariant_adjoint _ hU.2) (covariant_comp _ _ hcV hU.2)⟩

theorem reconstructed_pullback_supported (q : ℕ) [Fact q.Prime]
    (hqN : ¬q ∣ N) (hqQ : ¬q ∣ Q)
    (hs : ∀ z, Supported (integralGroup q) (V z).starProjection) (z : UpperHalfPlane) :
    Supported (integralGroup q) (reconstructedPullback A hN P e F V hF hV z).starProjection := by
  rw [reconstructed_pullback_projection]
  have hU := normalized_reconstruction_supported A q hN hqN hqQ P e z
  exact supported_comp _ _ _ (supported_adjoint _ _ hU) (supported_comp _ _ _ (hs z) hU)

#print axioms reconstructed_pullback_projection
#print axioms reconstructed_pullback_le
#print axioms reconstructed_pullback_forward
#print axioms reconstructed_pullback_trace
#print axioms reconstructed_pullback_regular
#print axioms reconstructed_pullback_supported

end QuantitativeEulerEndpointPrepared
