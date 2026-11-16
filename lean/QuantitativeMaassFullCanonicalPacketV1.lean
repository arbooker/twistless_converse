module

public import QuantitativeMaassCenteredNonzeroPacketV1
public import QuantitativeMaassFullTerminalEmbeddingV1
public import QuantitativeMaassFullTerminalPacketV1
public import QuantitativeMaassCompletedNewSignPacketV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory AsymptoticSectorSigns QuantitativeNewGap
open AsymptoticClassicalPetersson
open scoped Topology ContDiff SchwartzMap

namespace QuantitativeMaass

/-- Exact intertwining of the constructed finite-energy terminal operator
with the genuine spectral packet on the completed cuspidal new/sign space. -/
theorem completedNewSignFullTerminalEmbedding_packet {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N]
    (χ : admissibleGeneratorIndex N hN → ℂ) (e : Sector N)
    (hχW : χ (frickeGeneratorIndex N hN)=sign e.1)
    (hχS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN p)= -delta e p.val)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ s,star (f s)=f s)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (x : completedNewSignSpace N hN χ) :
    EulerHilbert.FullTerminal.centeredTerminalPacket A hN P f hc he hr R hR hs e
      (completedNewSignFullTerminalEmbedding A hN P χ e x)=
      completedNewSignFullTerminalEmbedding A hN P χ e
        (completedNewSignTimePacket N hN χ f (f.smooth ⊤) he hc hr R hR hs x) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let J := completedNewSignWeightedEmbedding N hN P'.epsilon_pos (show 1≤P'.s+3 by omega) χ
  let D := completedNewSignTimePacket N hN χ f (f.smooth ⊤) he hc hr R hR hs
  have hJ : J x∈cylinderNonzeroModes :=
    weightedQuotientEmbedding_cuspidal_nonzero N hN P'.epsilon_pos (show 1≤P'.s+3 by omega) x.val x.property.1
  change EulerHilbert.FullTerminal.terminalLeftInverse A hN P e
    (AsymptoticCylinderLift.lift.toContinuousLinearMap.adjoint
      (physicalCenteredTerminalPacket f hc he hr R hR hs P'.ε (P'.s+3) P'.ε P'.epsilon_pos
        (productCylinderToTranslation (EulerHilbert.normalized A hN P e
          (completedNewSignFullTerminalEmbedding A hN P χ e x))))) = _
  rw [completedNewSignFullTerminalEmbedding_normalized A hN P χ e hχW hχS,
    translationToProductCylinder_inverse,
    physicalCenteredTerminalPacket_nonzero f hc he hr R hR hs P'.ε P'.epsilon_pos (P'.s+3)
      P'.ε P'.epsilon_pos (J x) hJ,
    completedNewSignTimePacket_intertwining]
  have hl : cylinderZeroExtension (J (D x))=
      AsymptoticCylinderLift.lift (translationToProductCylinder (J (D x))) := by
    rw [←productCylinderToTranslation_lift,translationToProductCylinder_inverse]
  change EulerHilbert.FullTerminal.terminalLeftInverse A hN P e
    (AsymptoticCylinderLift.lift.toContinuousLinearMap.adjoint
      (AsymptoticCylinderTerminal.hyperProjection P'.ε (cylinderZeroExtension (J (D x)))))=_
  rw [hl,←AsymptoticCylinderTerminal.lift_projection,AsymptoticCylinderTerminal.adjoint_lift,
    EulerHilbert.FullTerminal.terminalLeftInverse_projection]
  rfl

#print axioms completedNewSignFullTerminalEmbedding_packet

end QuantitativeMaass
