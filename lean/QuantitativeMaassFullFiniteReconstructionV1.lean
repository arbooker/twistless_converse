module

public import QuantitativeMaassFullTerminalLeftInverseV1
public import QuantitativeHolomorphicFiniteNormalizationV1
public import AsymptoticCylinderFiniteReconstructionV1
public import AsymptoticFiniteBranchReconstructionV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set AsymptoticSectorSigns ContinuousLinearMap
namespace QuantitativeMaass.EulerHilbert.FullTerminal

variable {N Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
  (hN : 0<N) (P : FinitenessGlobalHeight.Parameters A)

/-- Finite weight-zero reconstruction on the whole terminal region. -/
def finiteReconstruction (e : Sector N) (d J : ℕ) :
    AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε →L[ℂ]
      AsymptoticCylinder.Space :=
  AsymptoticCylinderReconstruction.finiteExtension A hN
    (AsymptoticReconstructedCount.parameters A P) (multiplier e) d
      (Finset.Icc (-(J:ℤ)) J) 0

theorem finiteReconstruction_norm_le (e : Sector N) (d J : ℕ) :
    ‖finiteReconstruction A hN P e d J‖≤QuantitativeHolomorphic.countReconstructionBound A P := by
  exact AsymptoticCylinderReconstruction.finiteExtension_norm_le A hN _
    (AsymptoticReconstructedCount.parameters_bound A P).le
    (multiplier e) (fun q _ => multiplier_norm e q) d (Finset.Icc (-(J:ℤ)) J) 0

/-- Both finite truncation errors are explicit and uniform in the sector;
no holomorphic positive-weight specialization is used. -/
theorem finiteReconstruction_error (e : Sector N) (d J : ℕ) (hJ : 0<J) :
    ‖finiteReconstruction A hN P e d J-reconstruction A hN P e‖≤
      QuantitativeHolomorphic.countReconstructionError A P d J := by
  have hraw := QuantitativeHolomorphic.physical_reconstruction_explicit_error A hN
    (AsymptoticReconstructedCount.parameters A P)
    (AsymptoticReconstructedCount.parameters_bound A P).le
    (multiplier e) (fun q _ => multiplier_norm e q) 0 d J hJ
  have hcy := AsymptoticCylinderReconstruction.finiteExtension_error A hN
    (AsymptoticReconstructedCount.parameters A P) (multiplier e) d
    (Finset.Icc (-(J:ℤ)) J) 0
  exact hcy.trans hraw

/-- The full reconstruction has a finite rational-branch expression with
only terminal restriction; no horizontal zero-mode projection occurs. -/
theorem finiteReconstruction_eq_expression (e : Sector N) (d J : ℕ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    finiteReconstruction A hN P e d J=
      AsymptoticCylinderLift.lift.toContinuousLinearMap.adjoint.comp
        ((AsymptoticFiniteBranch.holomorphicSum
          (AsymptoticFiniteBranch.fullExpression A hN P' (multiplier e) d
            (Finset.Icc (-(J:ℤ)) J)) 0).comp
          ((AsymptoticGeometricReconstruction.TerminalSpace A P').subtypeL.comp
            (AsymptoticCylinderReconstruction.terminalLift A P'))) := by
  intro P'
  have he := AsymptoticFiniteBranch.holomorphicSum_fullExpression_on_terminal A hN P'
    (multiplier e) d (Finset.Icc (-(J:ℤ)) J) 0
  change (AsymptoticCylinderLift.lift.toContinuousLinearMap.adjoint.comp
    ((AsymptoticGeometricReconstruction.finiteFoldExtension A hN P' (multiplier e) d
      (Finset.Icc (-(J:ℤ)) J) 0).comp
      (AsymptoticCylinderReconstruction.terminalLift A P')))=_
  rw [←he]
  simp only [comp_assoc]

#print axioms finiteReconstruction_norm_le
#print axioms finiteReconstruction_error
#print axioms finiteReconstruction_eq_expression
end QuantitativeMaass.EulerHilbert.FullTerminal
