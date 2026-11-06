module

public import QuantitativeHolomorphicRegularSourceV1
public import QuantitativeSpectralObservabilityNewSourceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane ContinuousLinearMap AsymptoticOrbitDiagonal
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic AsymptoticRegularReconstruction
open AsymptoticRegularBranchFamily
open scoped lp

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- Every value of the actual normalized reconstruction is an actual
extension of its closed-terminal restriction. The normalization changes
the input coordinates but not this range identity. -/
theorem reconstructed_terminal_norm (hN : 0<N) (P : Parameters A)
    (e : Sector N) (x : ℍ) (v : ℓ²(OrbitGroup,ℂ)) :
    ‖normalizedRegularAmbientCountReconstruction A hN P e x v‖≤
      countReconstructionBound A P*
        ‖corner (AsymptoticCertificateOperators.highStrip
          (AsymptoticReconstructedCount.parameters A P).ε) x
          (normalizedRegularAmbientCountReconstruction A hN P e x v)‖ := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let R := includedExtension A hN P' (multiplier e) x
  let w := inverseSqrtCFC
    ((scaledRegularCountReconstruction A hN P e x).adjoint.comp
      (scaledRegularCountReconstruction A hN P e x))
    ((TerminalSpace A P' x).subtypeL.adjoint v)
  let g := (countReconstructionBound A P)⁻¹ • w
  have he : normalizedRegularAmbientCountReconstruction A hN P e x v=R g := by
    change ((countReconstructionBound A P)⁻¹ • R) w=R ((countReconstructionBound A P)⁻¹ • w)
    rw [smul_apply,map_smul_of_tower]
  have hk := parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) x
  have ht := includedExtension_terminal A hN P' (multiplier e) x
    (hk.trans (by norm_num)) g
  have hR : ‖R‖≤countReconstructionBound A P :=
    includedExtension_norm_le A hN P' (multiplier e) (fun q _ => multiplier_norm e q) x hk
  rw [he]
  change ‖R g‖≤countReconstructionBound A P*‖AsymptoticRegularCertificate.highProjection A P' x (R g)‖
  rw [ht]
  exact R.le_of_opNorm_le hR g

theorem reconstructed_norm_on_terminal (hN : 0<N) (P : Parameters A)
    (e : Sector N) (x : ℍ) (v : ℓ²(OrbitGroup,ℂ))
    (hv : v∈TerminalSpace A (AsymptoticReconstructedCount.parameters A P) x) :
    ‖normalizedRegularAmbientCountReconstruction A hN P e x v‖=‖v‖ := by
  let T := TerminalSpace A (AsymptoticReconstructedCount.parameters A P) x
  have hproj : T.subtypeL.adjoint v=(⟨v,hv⟩ : T) := by
    rw [Submodule.adjoint_subtypeL]
    apply Subtype.ext
    exact T.starProjection_eq_self_iff.mpr hv
  change ‖normalizedReconstruction (scaledRegularCountReconstruction A hN P e x)
    (T.subtypeL.adjoint v)‖=‖v‖
  rw [hproj,normalizedRegularCountReconstruction_norm]
  rfl

/-- The actual source input is controlled by the terminal coordinates of
its reconstructed vector, with the already proved certificate constant. -/
theorem terminal_input_le_reconstructed_terminal (hN : 0<N) (P : Parameters A)
    (e : Sector N) (x : ℍ) (v : ℓ²(OrbitGroup,ℂ))
    (hv : v∈TerminalSpace A (AsymptoticReconstructedCount.parameters A P) x) :
    ‖v‖≤countReconstructionBound A P*
      ‖corner (AsymptoticCertificateOperators.highStrip
        (AsymptoticReconstructedCount.parameters A P).ε) x
        (normalizedRegularAmbientCountReconstruction A hN P e x v)‖ := by
  rw [← reconstructed_norm_on_terminal A hN P e x v hv]
  exact reconstructed_terminal_norm A hN P e x v

#print axioms reconstructed_terminal_norm
#print axioms reconstructed_norm_on_terminal
#print axioms terminal_input_le_reconstructed_terminal

end QuantitativeSpectralObservability
