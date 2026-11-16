module

public import QuantitativeMaassNonzeroReconstructionV1
public import QuantitativeMaassNormalizedLeftInverseV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory ContinuousLinearMap AsymptoticSectorSigns

namespace QuantitativeMaass.EulerHilbert.FullTerminal

/-- Restriction to the whole terminal region, before any Fourier projection. -/
def terminalRestriction (ε : ℝ) : AsymptoticCylinder.Space →L[ℂ] AsymptoticCylinderTerminal.Space ε :=
  AsymptoticRegionL2.restrict AsymptoticCylinder.measure
    (AsymptoticCylinderTerminal.region ε) (AsymptoticCylinderTerminal.region_measurable ε)

theorem terminalRestriction_norm_le (ε : ℝ) : ‖terminalRestriction ε‖≤1 := by
  apply opNorm_le_bound _ zero_le_one
  intro x
  exact (AsymptoticCylinderTerminal.projection ε).le_of_opNorm_le
    (AsymptoticCylinderTerminal.projection_norm_le ε) x

variable {N Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
  (hN : 0<N) (P : FinitenessGlobalHeight.Parameters A)

/-- Exact recovery of the unprojected terminal input. -/
theorem terminalRestriction_reconstruction (e : Sector N)
    (g : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε) :
    terminalRestriction (AsymptoticReconstructedCount.parameters A P).ε
      (reconstruction A hN P e g)=g := by
  apply Subtype.ext
  exact AsymptoticCylinderReconstruction.extension_terminal A hN
    (AsymptoticReconstructedCount.parameters A P) (multiplier e) 0
    (lt_trans (AsymptoticReconstructedCount.parameters_hyperbolic_contraction A hN P _
      (fun q _ => multiplier_norm e q) 0) (by norm_num)) g

/-- Gram normalization on the full terminal space remains an isometry. -/
def physicalIsometry (e : Sector N) :
    AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε →ₗᵢ[ℂ]
      AsymptoticHyperbolicSlash.Space where
  toLinearMap := AsymptoticCylinderLift.lift.toLinearMap.comp (normalized A hN P e).toLinearMap
  norm_map' g := by
    change ‖AsymptoticCylinderLift.lift (normalized A hN P e g)‖=‖g‖
    rw [AsymptoticCylinderLift.lift_norm,normalized_norm]

def terminalLeftInverse (e : Sector N) :
    AsymptoticCylinder.Space →L[ℂ]
      AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε :=
  QuantitativeMaass.normalizedTerminalLeftInverse (reconstruction A hN P e)
    (terminalRestriction (AsymptoticReconstructedCount.parameters A P).ε)

theorem terminalLeftInverse_normalized (e : Sector N)
    (g : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε) :
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
  have hh : terminalRestriction (AsymptoticReconstructedCount.parameters A P).ε
      (AsymptoticCylinderTerminal.projection (AsymptoticReconstructedCount.parameters A P).ε v)=
      terminalRestriction (AsymptoticReconstructedCount.parameters A P).ε v := by
    apply Subtype.ext
    exact AsymptoticRegionL2.projection_idempotent _ _ _ v
  unfold terminalLeftInverse QuantitativeMaass.normalizedTerminalLeftInverse
  simp only [ContinuousLinearMap.comp_apply,hh]

/-- Physical terminal restriction still recovers the exact normalized
datum through the bounded terminal inverse. -/
theorem terminalLeftInverse_physical (e : Sector N)
    (g : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε) :
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

end QuantitativeMaass.EulerHilbert.FullTerminal
