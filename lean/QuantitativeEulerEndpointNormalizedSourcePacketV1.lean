module

public import QuantitativeEulerEndpointIsometricChainV1
public import QuantitativeEulerEndpointReconstructedChainPullbackV1
public import QuantitativeEulerEndpointPacketChainV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic QuantitativeEulerEndpointIsometricImage
open AsymptoticRegularReconstruction AsymptoticRegularCompactBranch QuantitativeSpectralDeflationChain
open QuantitativeSpectralCornerCutRow

variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A) (e : Sector N)
variable (F : UpperHalfPlane → ClosedSubmodule ℂ Space)
variable {s : Set UpperHalfPlane} (hs : IsCompact s) (a c : ℝ) (l : List (EligiblePrime N))

def normalizedBaselineSource (x : UpperHalfPlane) : ClosedSubmodule ℂ Space :=
  step (F x) (newBaselineDetector N e hs (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+4) x *
    normalizedRegularAmbientCountReconstruction A (NeZero.pos N) P e x) (Real.sqrt a)

def normalizedSourcePacket (x : UpperHalfPlane) : ClosedSubmodule ℂ Space :=
  chain (normalizedBaselineSource A P e F hs a x)
    (fun i => packetSequence N (NeZero.pos N) (sign e.1) hs
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) l i x *
      normalizedRegularAmbientCountReconstruction A (NeZero.pos N) P e x) c l.length

theorem normalized_baseline_source_le (x : UpperHalfPlane) :
    normalizedBaselineSource A P e F hs a x≤F x := nextSpace_le _ _ _

theorem normalized_source_packet_le (x : UpperHalfPlane) :
    normalizedSourcePacket A P e F hs a c l x≤F x :=
  (chain_antitone _ _ c (Nat.zero_le l.length)).trans (normalized_baseline_source_le A P e F hs a x)

variable (hF : ∀ x,(F x).toSubmodule≤TerminalSpace A (AsymptoticReconstructedCount.parameters A P) x)

/-- The initial normalized source cut reconstructs to the original baseline cut exactly. -/
theorem normalized_baseline_image (x : UpperHalfPlane) :
    closedImage (normalizedRegularAmbientCountReconstruction A (NeZero.pos N) P e x)
      (normalizedBaselineSource A P e F hs a x)
      (fun v hv => normalized_reconstruction_norm_on A (NeZero.pos N) P e x (F x).toSubmodule (hF x) v
        (normalized_baseline_source_le A P e F hs a x hv))=
      closedReconstructedBaseline A P e (fun x => (F x).toSubmodule) hF hs a x := by
  exact closed_image_step _ (F x)
    (normalized_reconstruction_norm_on A (NeZero.pos N) P e x (F x).toSubmodule (hF x)) _ _

/-- The original-prime packet is exactly the isometric image of the packet of
original rows composed with normalized reconstruction. -/
theorem normalized_source_packet_image (hc : 0<c) (x : UpperHalfPlane) :
    closedImage (normalizedRegularAmbientCountReconstruction A (NeZero.pos N) P e x)
      (normalizedSourcePacket A P e F hs a c l x)
      (fun v hv => normalized_reconstruction_norm_on A (NeZero.pos N) P e x (F x).toSubmodule (hF x) v
        (normalized_source_packet_le A P e F hs a c l x hv))=
      reconstructedChainImage A P e (fun x => (F x).toSubmodule) hF hs a c l x := by
  let U := normalizedRegularAmbientCountReconstruction A (NeZero.pos N) P e x
  let B := fun i => packetSequence N (NeZero.pos N) (sign e.1) hs
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+4) l i x
  have hb := normalized_baseline_image A P e F hs a hF x
  have hh := closed_image_chain U (normalizedBaselineSource A P e F hs a x)
    (fun v hv => normalized_reconstruction_norm_on A (NeZero.pos N) P e x (F x).toSubmodule (hF x) v
      (normalized_baseline_source_le A P e F hs a x hv)) B c l.length
  rw [hb] at hh
  exact hh.trans (primeChain_eq_packet N (NeZero.pos N) (sign e.1) hs
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+4) c hc
    (closedReconstructedBaseline A P e (fun x => (F x).toSubmodule) hF hs a) l x).symm

#print axioms normalized_baseline_source_le
#print axioms normalized_source_packet_le
#print axioms normalized_baseline_image
#print axioms normalized_source_packet_image
end QuantitativeEulerEndpointPrepared
