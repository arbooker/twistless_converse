module

public import QuantitativeEulerEndpointReconstructedImageV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared

open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic QuantitativeEulerEndpointIsometricImage
open AsymptoticRegularReconstruction AsymptoticFiniteBranch ContinuousLinearMap

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)
variable (hN : 0 < N) (P : Parameters A) (e : Sector N)

/-- The adjoint is the exact inverse on terminal source vectors. -/
theorem normalized_reconstruction_left_inverse (z : UpperHalfPlane) (v : RegularSpace)
    (hv : v ∈ TerminalSpace A (AsymptoticReconstructedCount.parameters A P) z) :
    (normalizedRegularAmbientCountReconstruction A hN P e z).adjoint
      (normalizedRegularAmbientCountReconstruction A hN P e z v) = v := by
  have he := congrArg (fun T : RegularSpace →L[ℂ] RegularSpace => T v)
    (normalizedRegularAmbientCountReconstruction_gram A hN P e z)
  exact he.trans ((AsymptoticOrbitRegion.mem_space _ _ v).1 hv)

variable (F : UpperHalfPlane → Submodule ℂ RegularSpace) [∀ z, CompleteSpace (F z)]
variable (hF : ∀ z, F z ≤ TerminalSpace A (AsymptoticReconstructedCount.parameters A P) z)

/-- Image membership refers to actual source vectors, without closure loss. -/
theorem mem_reconstructed_image (z : UpperHalfPlane) (y : RegularSpace) :
    y ∈ reconstructedImage A hN P e F hF z ↔
      ∃ v ∈ F z, normalizedRegularAmbientCountReconstruction A hN P e z v = y := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, v.property, hv⟩
  · rintro ⟨v, hv, he⟩
    exact ⟨⟨v, hv⟩, he⟩

/-- Every surviving image vector pulls back to its original source with
exact reconstruction and exact norm. -/
theorem reconstructed_image_inverse (z : UpperHalfPlane) (y : RegularSpace)
    (hy : y ∈ reconstructedImage A hN P e F hF z) :
    let U := normalizedRegularAmbientCountReconstruction A hN P e z
    U.adjoint y ∈ F z ∧ U (U.adjoint y) = y ∧ ‖U.adjoint y‖ = ‖y‖ := by
  rcases hy with ⟨v, he⟩
  have hv : (v : RegularSpace) ∈ F z := v.property
  let U := normalizedRegularAmbientCountReconstruction A hN P e z
  change U.adjoint y ∈ F z ∧ U (U.adjoint y) = y ∧ ‖U.adjoint y‖ = ‖y‖
  have hi : U.adjoint y = (v : RegularSpace) :=
    (congrArg U.adjoint he).symm.trans
      (normalized_reconstruction_left_inverse A hN P e z v (hF z hv))
  rw [hi]
  refine ⟨hv, he, ?_⟩
  exact (normalized_reconstruction_norm_on A hN P e z (F z) (hF z) v hv).symm.trans
    (congrArg norm he)

#print axioms normalized_reconstruction_left_inverse
#print axioms mem_reconstructed_image
#print axioms reconstructed_image_inverse

end QuantitativeEulerEndpointPrepared
