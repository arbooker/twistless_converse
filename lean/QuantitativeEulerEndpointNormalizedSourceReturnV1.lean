module

public import QuantitativeEulerEndpointNormalizedSourcePacketV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic QuantitativeEulerEndpointIsometricImage
open AsymptoticRegularReconstruction AsymptoticRegularCompactBranch
open AsymptoticRegularTrace MeasureTheory

variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A) (e : Sector N)
variable (F : UpperHalfPlane → ClosedSubmodule ℂ Space)
variable {s : Set UpperHalfPlane} (hs : IsCompact s) (a c : ℝ) (l : List (EligiblePrime N))
variable (hF : ∀ x,(F x).toSubmodule≤TerminalSpace A (AsymptoticReconstructedCount.parameters A P) x)

/-- The composed-row source packet is exactly the previously constructed adjoint pullback. -/
theorem normalized_source_packet_eq_pullback (hc : 0<c) (x : UpperHalfPlane) :
    (normalizedSourcePacket A P e F hs a c l x).toSubmodule=
      reconstructedChainPullback A P e (fun x => (F x).toSubmodule) hF hs a c l x := by
  let U := normalizedRegularAmbientCountReconstruction A (NeZero.pos N) P e x
  let V := (normalizedSourcePacket A P e F hs a c l x).toSubmodule
  let I := (reconstructedChainImage A P e (fun x => (F x).toSubmodule) hF hs a c l x).toSubmodule
  have hnorm : ∀ v∈V,‖U v‖=‖v‖ := fun v hv =>
    normalized_reconstruction_norm_on A (NeZero.pos N) P e x (F x).toSubmodule (hF x) v
      (normalized_source_packet_le A P e F hs a c l x hv)
  have himage : imageSpace U V hnorm=I := congrArg (fun W : ClosedSubmodule ℂ Space => W.toSubmodule)
    (normalized_source_packet_image A P e F hs a c l hF hc x)
  have hi (v : Space) (hv : v∈V) : U.adjoint (U v)=v :=
    normalized_reconstruction_left_inverse A (NeZero.pos N) P e x v
      (hF x (normalized_source_packet_le A P e F hs a c l x hv))
  ext v
  constructor
  · intro hv
    have hy : U v∈I := himage ▸ (show U v∈imageSpace U V hnorm from ⟨⟨v,hv⟩,rfl⟩)
    exact ⟨⟨U v,hy⟩,hi v hv⟩
  · rintro ⟨y,hy⟩
    have hm : (y : Space)∈imageSpace U V hnorm := himage.symm ▸ y.property
    rcases hm with ⟨w,hw⟩
    have he : U.adjoint (y : Space)=(w : Space) := (congrArg U.adjoint hw).symm.trans (hi w w.property)
    have hv : (w : Space)=v := he.symm.trans hy
    exact hv ▸ w.property

theorem normalized_source_packet_eq_closed_pullback (hc : 0<c) (x : UpperHalfPlane) :
    normalizedSourcePacket A P e F hs a c l x=
      closedReconstructedChainPullback A P e (fun x => (F x).toSubmodule) hF hs a c l x := by
  apply SetLike.coe_injective
  exact congrArg (fun W : Submodule ℂ Space => (W : Set Space))
    (normalized_source_packet_eq_pullback A P e F hs a c l hF hc x)

theorem normalized_source_packet_mass
    (hmF : ∀ g k,Measurable (fun x => matrix (F x).toSubmodule.starProjection g k))
    (hcF : Covariant (fun x => (F x).toSubmodule.starProjection)) (ha : 0<a) (hc : 0<c) :
    cornerMass (normalizedSourcePacket A P e F hs a c l)=
      cornerMass (reconstructedChainImage A P e (fun x => (F x).toSubmodule) hF hs a c l) := by
  have he := funext (normalized_source_packet_eq_closed_pullback A P e F hs a c l hF hc)
  rw [he]
  exact reconstructed_chain_pullback_mass A P e (fun x => (F x).toSubmodule) hF hs a c l hmF hcF ha hc

include hF in
theorem normalized_source_packet_regular
    (hmF : ∀ g k,Measurable (fun x => matrix (F x).toSubmodule.starProjection g k))
    (hcF : Covariant (fun x => (F x).toSubmodule.starProjection)) (ha : 0<a) (hc : 0<c) :
    (∀ g k,Measurable (fun x => matrix (normalizedSourcePacket A P e F hs a c l x).toSubmodule.starProjection g k)) ∧
      Covariant (fun x => (normalizedSourcePacket A P e F hs a c l x).toSubmodule.starProjection) := by
  simp only [normalized_source_packet_eq_pullback A P e F hs a c l hF hc]
  exact reconstructed_chain_pullback_regular A P e (fun x => (F x).toSubmodule) hF hs a c l hmF hcF ha hc

#print axioms normalized_source_packet_eq_pullback
#print axioms normalized_source_packet_eq_closed_pullback
#print axioms normalized_source_packet_mass
#print axioms normalized_source_packet_regular
end QuantitativeEulerEndpointPrepared
