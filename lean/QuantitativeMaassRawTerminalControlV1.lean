module

public import QuantitativeMaassRawReconstructedInverseV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass.RawPrepared
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic AsymptoticRegularReconstruction AsymptoticFiniteBranch
open QuantitativeMaass.EulerHilbert.FullTerminal ContinuousLinearMap

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem terminal_input_le_reconstructed_terminal (hN : 0<N) (P : Parameters A)
    (e : Sector N) (z : UpperHalfPlane) (v : RegularSpace)
    (hv : v∈TerminalSpace A (AsymptoticReconstructedCount.parameters A P) z) :
    ‖v‖≤countReconstructionBound A P*
      ‖AsymptoticOrbitDiagonal.corner
        (AsymptoticCertificateOperators.highStrip (AsymptoticReconstructedCount.parameters A P).ε) z
        (normalizedRegularAmbient A hN P e z v)‖ := by
  let T := TerminalSpace A (AsymptoticReconstructedCount.parameters A P) z
  have hp : T.subtypeL.adjoint v=(⟨v,hv⟩:T) := by
    rw [Submodule.adjoint_subtypeL]
    exact T.orthogonalProjectionOnto_mem_subspace_eq_self ⟨v,hv⟩
  have hh := normalizedRegular_terminal_control A hN P e z ⟨v,hv⟩
  change ‖v‖≤countReconstructionBound A P*‖AsymptoticOrbitDiagonal.corner _ z
    (normalizedRegularReconstruction A hN P e z (T.subtypeL.adjoint v))‖
  rw [hp]
  exact hh

#print axioms terminal_input_le_reconstructed_terminal
end QuantitativeMaass.RawPrepared
