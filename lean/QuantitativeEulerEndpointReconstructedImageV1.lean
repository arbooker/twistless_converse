module

public import QuantitativeEulerEndpointNormalizedSupportV1
public import QuantitativeEulerEndpointIsometricImageV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared

open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic QuantitativeEulerEndpointIsometricImage
open AsymptoticRegularReconstruction AsymptoticFiniteBranch AsymptoticRegularTrace
open AsymptoticIntegralSubgroup AsymptoticSubgroupSupport MeasureTheory ContinuousLinearMap

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)
variable (hN : 0 < N) (P : Parameters A) (e : Sector N)

/-- The actual normalized ambient reconstruction is an isometry on every
closed subspace of its terminal source. -/
theorem normalized_reconstruction_norm_on (z : UpperHalfPlane)
    (F : Submodule ℂ RegularSpace)
    (hF : F ≤ TerminalSpace A (AsymptoticReconstructedCount.parameters A P) z)
    (v : RegularSpace) (hv : v ∈ F) :
    ‖normalizedRegularAmbientCountReconstruction A hN P e z v‖ = ‖v‖ := by
  let T := TerminalSpace A (AsymptoticReconstructedCount.parameters A P) z
  change ‖normalizedReconstruction (scaledRegularCountReconstruction A hN P e z)
    (T.subtypeL.adjoint v)‖ = _
  rw [normalizedRegularCountReconstruction_norm, Submodule.adjoint_subtypeL]
  exact congrArg norm (T.orthogonalProjectionOnto_mem_subspace_eq_self ⟨v, hF hv⟩)

def reconstructedImage (F : UpperHalfPlane → Submodule ℂ RegularSpace)
    [∀ z, CompleteSpace (F z)]
    (hF : ∀ z, F z ≤ TerminalSpace A (AsymptoticReconstructedCount.parameters A P) z)
    (z : UpperHalfPlane) : Submodule ℂ RegularSpace :=
  imageSpace (normalizedRegularAmbientCountReconstruction A hN P e z) (F z)
    (normalized_reconstruction_norm_on A hN P e z (F z) (hF z))

instance reconstructedImage_complete (F : UpperHalfPlane → Submodule ℂ RegularSpace)
    [∀ z, CompleteSpace (F z)]
    (hF : ∀ z, F z ≤ TerminalSpace A (AsymptoticReconstructedCount.parameters A P) z)
    (z : UpperHalfPlane) : CompleteSpace (reconstructedImage A hN P e F hF z) :=
  imageSpace_complete _ _ _

variable (F : UpperHalfPlane → Submodule ℂ RegularSpace) [∀ z, CompleteSpace (F z)]
variable (hF : ∀ z, F z ≤ TerminalSpace A (AsymptoticReconstructedCount.parameters A P) z)

theorem reconstructed_image_projection (z : UpperHalfPlane) :
    (reconstructedImage A hN P e F hF z).starProjection =
      (normalizedRegularAmbientCountReconstruction A hN P e z).comp
        ((F z).starProjection.comp (normalizedRegularAmbientCountReconstruction A hN P e z).adjoint) :=
  image_projection _ _ _

/-- No source trace is lost or multiplied when passing to reconstructed
vectors for the fresh-prime mixing argument. -/
theorem reconstructed_image_trace
    (hmF : ∀ g h, Measurable (fun z => matrix (F z).starProjection g h))
    (hcF : Covariant (fun z => (F z).starProjection)) :
    trace volume (fun z => (reconstructedImage A hN P e F hF z).starProjection) =
      trace volume (fun z => (F z).starProjection) :=
  image_trace volume AsymptoticRationalGroup.measurePreserving _ F _
    (normalizedRegularCountReconstruction_regular A hN P e).1
    (normalizedRegularCountReconstruction_regular A hN P e).2 hmF hcF

theorem reconstructed_image_regular
    (hmF : ∀ g h, Measurable (fun z => matrix (F z).starProjection g h))
    (hcF : Covariant (fun z => (F z).starProjection)) :
    (∀ g h, Measurable (fun z => matrix (reconstructedImage A hN P e F hF z).starProjection g h)) ∧
      Covariant (fun z => (reconstructedImage A hN P e F hF z).starProjection) := by
  have hU := normalizedRegularCountReconstruction_regular A hN P e
  simp only [reconstructed_image_projection]
  exact ⟨matrix_comp_measurable _ _ hU.1
    (matrix_comp_measurable _ _ hmF (matrix_adjoint_measurable _ hU.1)),
    covariant_comp _ _ hU.2 (covariant_comp _ _ hcF (covariant_adjoint _ hU.2))⟩

theorem reconstructed_image_supported (q : ℕ) [Fact q.Prime]
    (hqN : ¬q ∣ N) (hqQ : ¬q ∣ Q)
    (hs : ∀ z, Supported (integralGroup q) (F z).starProjection) (z : UpperHalfPlane) :
    Supported (integralGroup q) (reconstructedImage A hN P e F hF z).starProjection := by
  rw [reconstructed_image_projection]
  exact reconstructed_source_supported A q hN hqN hqQ P e z _ (hs z)

#print axioms normalized_reconstruction_norm_on
#print axioms reconstructed_image_projection
#print axioms reconstructed_image_trace
#print axioms reconstructed_image_regular
#print axioms reconstructed_image_supported

end QuantitativeEulerEndpointPrepared
