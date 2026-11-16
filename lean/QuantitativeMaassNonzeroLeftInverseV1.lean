module

public import QuantitativeMaassNonzeroReconstructionV1
public import QuantitativeMaassNormalizedLeftInverseV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory ContinuousLinearMap AsymptoticSectorSigns

namespace QuantitativeMaass.EulerHilbert.Nonzero

/-- Actual terminal restriction followed by the nonzero-mode projection. -/
def terminalRestriction (ε : ℝ) : AsymptoticCylinder.Space →L[ℂ] terminalNonzeroModes ε :=
  (terminalNonzeroModes ε).orthogonalProjectionOnto.comp (AsymptoticCylinderTerminal.projection ε)

theorem terminalRestriction_norm_le (ε : ℝ) : ‖terminalRestriction ε‖≤1 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  exact (mul_le_mul (terminalNonzeroModes ε).orthogonalProjectionOnto_norm_le
    (AsymptoticCylinderTerminal.projection_norm_le ε) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

variable {N Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
  (hN : 0<N) (P : FinitenessGlobalHeight.Parameters A)

/-- The actual extension agrees with its input on the terminal region,
so the nonzero-mode terminal restriction is an exact left inverse. -/
theorem terminalRestriction_reconstruction (e : Sector N)
    (g : terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε) :
    terminalRestriction (AsymptoticReconstructedCount.parameters A P).ε
      (reconstruction A hN P e g)=g := by
  have hterm := AsymptoticCylinderReconstruction.extension_terminal A hN
    (AsymptoticReconstructedCount.parameters A P) (multiplier e) 0
    (lt_trans (AsymptoticReconstructedCount.parameters_hyperbolic_contraction A hN P _
      (fun q _ => multiplier_norm e q) 0) (by norm_num))
    (terminalNonzeroInclusion _ g)
  change AsymptoticCylinderTerminal.projection (AsymptoticReconstructedCount.parameters A P).ε
    (reconstruction A hN P e g)=(g:AsymptoticCylinder.Space) at hterm
  change (terminalNonzeroModes _).orthogonalProjectionOnto
    (AsymptoticCylinderTerminal.projection _ (reconstruction A hN P e g))=g
  rw [hterm]
  exact (terminalNonzeroModes _).orthogonalProjectionOnto_mem_subspace_eq_self g

def terminalLeftInverse (e : Sector N) :
    AsymptoticCylinder.Space →L[ℂ]
      terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε :=
  QuantitativeMaass.normalizedTerminalLeftInverse (reconstruction A hN P e)
    (terminalRestriction (AsymptoticReconstructedCount.parameters A P).ε)

theorem terminalLeftInverse_normalized (e : Sector N)
    (g : terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε) :
    terminalLeftInverse A hN P e (normalized A hN P e g)=g := by
  apply QuantitativeMaass.normalizedTerminalLeftInverse_apply _ _
    (terminalRestriction_reconstruction A hN P e) (by norm_num : (0:ℝ)<1)
  intro v
  simpa only [one_mul] using
    pow_le_pow_left₀ (norm_nonneg v) (reconstruction_norm_ge A hN P e v) 2

theorem terminalLeftInverse_projection (e : Sector N) (v : AsymptoticCylinder.Space) :
    terminalLeftInverse A hN P e
      (AsymptoticCylinderTerminal.projection (AsymptoticReconstructedCount.parameters A P).ε v)=
      terminalLeftInverse A hN P e v := by
  unfold terminalLeftInverse QuantitativeMaass.normalizedTerminalLeftInverse terminalRestriction
  simp only [ContinuousLinearMap.comp_apply]
  rw [show AsymptoticCylinderTerminal.projection (AsymptoticReconstructedCount.parameters A P).ε
      (AsymptoticCylinderTerminal.projection (AsymptoticReconstructedCount.parameters A P).ε v)=
      AsymptoticCylinderTerminal.projection (AsymptoticReconstructedCount.parameters A P).ε v from
    AsymptoticRegionL2.projection_idempotent _ _ _ v]

/-- Physical terminal restriction still recovers the exact normalized
datum through the bounded terminal inverse. -/
theorem terminalLeftInverse_physical (e : Sector N)
    (g : terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε) :
    terminalLeftInverse A hN P e (AsymptoticCylinderLift.lift.toContinuousLinearMap.adjoint
      (AsymptoticCylinderTerminal.hyperProjection (AsymptoticReconstructedCount.parameters A P).ε
        (physicalIsometry A hN P e g)))=g := by
  change terminalLeftInverse A hN P e (AsymptoticCylinderLift.lift.toContinuousLinearMap.adjoint
    (AsymptoticCylinderTerminal.hyperProjection _
      (AsymptoticCylinderLift.lift (normalized A hN P e g))))=_
  rw [←AsymptoticCylinderTerminal.lift_projection,AsymptoticCylinderTerminal.adjoint_lift,
    terminalLeftInverse_projection,terminalLeftInverse_normalized]

#print axioms terminalRestriction_norm_le
#print axioms terminalRestriction_reconstruction
#print axioms terminalLeftInverse_normalized
#print axioms terminalLeftInverse_projection
#print axioms terminalLeftInverse_physical

end QuantitativeMaass.EulerHilbert.Nonzero
