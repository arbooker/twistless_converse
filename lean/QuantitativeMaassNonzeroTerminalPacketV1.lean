module

public import QuantitativeMaassNonzeroLeftInverseV1
public import QuantitativeMaassCenteredTerminalPhysicalV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory AsymptoticSectorSigns
open scoped SchwartzMap ContDiff

namespace QuantitativeMaass.EulerHilbert.Nonzero

variable {N Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
  (hN : 0<N) (P : FinitenessGlobalHeight.Parameters A)
  (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
  (he : Function.Even f) (hr : ∀ s,star (f s)=f s)
  (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)

/-- Actual finite-energy packet on normalized nonzero terminal data. -/
def centeredTerminalPacket (e : Sector N) :=
  let P' := AsymptoticReconstructedCount.parameters A P
  ((terminalLeftInverse A hN P e).comp AsymptoticCylinderLift.lift.toContinuousLinearMap.adjoint).comp
    ((physicalCenteredTerminalPacket f hc he hr R hR hs P'.ε (P'.s+3) P'.ε P'.epsilon_pos).comp
      (productCylinderToTranslation.toContinuousLinearMap.comp (normalized A hN P e)))

/-- Square summability for the constructed terminal packet has no
residual trace assumption. -/
theorem centeredTerminalPacket_summable {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ
      (terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε)) (e : Sector N) :
    Summable (fun i => ‖centeredTerminalPacket A hN P f hc he hr R hR hs e (basis i)‖^2) :=
  physicalCenteredTerminalPacket_composition_summable f hc he hr R hR hs
    (AsymptoticReconstructedCount.parameters A P).ε
    ((AsymptoticReconstructedCount.parameters A P).s+3)
    (AsymptoticReconstructedCount.parameters A P).ε
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos basis
    (productCylinderToTranslation.toContinuousLinearMap.comp (normalized A hN P e))
    ((terminalLeftInverse A hN P e).comp AsymptoticCylinderLift.lift.toContinuousLinearMap.adjoint)

/-- Every original solution retains its exact scalar action after
centering, terminal restriction and inversion of normalized reconstruction. -/
theorem centeredTerminalPacket_original (e : Sector N) (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b)
    (g : terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε)
    (hg : physicalIsometry A hN P e g=
      principalEulerWeightedLp hN A (AsymptoticReconstructedCount.parameters A P) r σ hb) :
    centeredTerminalPacket A hN P f hc he hr R hR hs e g=cosinePacket f r • g := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have hin : productCylinderToTranslation (normalized A hN P e g)=
      principalEulerCylinderLp hN A P' r σ hb := by
    apply cylinderZeroExtension.injective
    rw [productCylinderToTranslation_lift,principalEulerCylinderLp_physical]
    exact hg
  change terminalLeftInverse A hN P e (AsymptoticCylinderLift.lift.toContinuousLinearMap.adjoint
    (physicalCenteredTerminalPacket f hc he hr R hR hs P'.ε (P'.s+3) P'.ε P'.epsilon_pos
      (productCylinderToTranslation (normalized A hN P e g))))=_
  rw [hin,physicalCenteredTerminalPacket_original,←hg,map_smul,map_smul,
    terminalLeftInverse_physical]

#print axioms centeredTerminalPacket_summable
#print axioms centeredTerminalPacket_original

end QuantitativeMaass.EulerHilbert.Nonzero
