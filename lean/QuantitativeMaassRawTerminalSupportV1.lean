module

public import QuantitativeMaassFullRegularSourceV1
public import QuantitativeEulerEndpointTerminalGramV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass.RawPrepared
open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic QuantitativeEulerEndpointTerminalAlgebra
open AsymptoticRegularReconstruction AsymptoticFiniteBranch
open QuantitativeMaass.EulerHilbert.FullTerminal

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem normalized_right_terminal (hN : 0<N) (P : Parameters A)
    (e : Sector N) (z : UpperHalfPlane) :
    normalizedRegularAmbient A hN P e z*
      AsymptoticOrbitDiagonal.corner (terminalRegion A P) z=
      normalizedRegularAmbient A hN P e z := by
  let S := (TerminalSpace A (AsymptoticReconstructedCount.parameters A P) z).subtypeL
  have hS : S.adjoint.comp S=1 := AsymptoticOrbitRegion.adjoint_comp_subtype _ z
  have hP : S.comp S.adjoint=AsymptoticOrbitDiagonal.corner (terminalRegion A P) z :=
    AsymptoticOrbitRegion.subtype_comp_adjoint _ z
  change ((normalizedRegularReconstruction A hN P e z).comp S.adjoint).comp
    (AsymptoticOrbitDiagonal.corner (terminalRegion A P) z) =
      (normalizedRegularReconstruction A hN P e z).comp S.adjoint
  exact (congrArg (fun T =>
    ((normalizedRegularReconstruction A hN P e z).comp S.adjoint).comp T) hP.symm).trans
      (extension_right S (normalizedRegularReconstruction A hN P e z) hS)

#print axioms normalized_right_terminal
end QuantitativeMaass.RawPrepared
