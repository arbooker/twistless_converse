module

public import QuantitativeEulerEndpointRegularBaseV1
public import QuantitativeEulerEndpointMassTransferV1
public import QuantitativeEulerEndpointPacketTraceV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPreparedHalf
open UpperHalfPlane MeasureTheory AsymptoticRegularTrace
open AsymptoticRegularCompactBranch (Space)
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointRegularBase
open QuantitativeEulerEndpointSubcorner QuantitativeEulerEndpointCanonicalHalf
open scoped ENNReal

variable {s : Set ℍ} (hs : IsCompact s) (p : Corner hs) (hp : IsStarProjection p)
  (U : Base → ClosedSubmodule ℂ Space)
  (hU : ∀ x, (U x).toSubmodule.starProjection=
    QuantitativeSpectralRegularAlgebra.representation AsymptoticRationalGroup.Group Base
      action_measurable (region s) (region_measurable hs) p x)
local notation "𝔄" => Subcorner action_measurable (region s) (region_measurable hs) p hp
local notation "ρ" => representation action_measurable (region s) (region_measurable hs) p hp

def half (A : 𝔄) : ℍ → ClosedSubmodule ℂ Space :=
  fun x => space (α:=Base) action_measurable (region s) (region_measurable hs) p hp A (show Base from x)

include U hU in
theorem half_regular (A : 𝔄) (hA : IsSelfAdjoint A) :
    (∀ g h, Measurable (fun x : ℍ => matrix (half hs p hp A x).toSubmodule.starProjection g h)) ∧
      Covariant (fun x : ℍ => (half hs p hp A x).toSubmodule.starProjection) := by
  let q := projection (α:=Base) action_measurable (region s) (region_measurable hs) p hp U hU A hA
  exact ⟨QuantitativeSpectralRegularAlgebra.representation_matrix_measurable
      AsymptoticRationalGroup.Group Base action_measurable (region s) (region_measurable hs) q,
    QuantitativeSpectralRegularAlgebra.representation_covariant
      AsymptoticRationalGroup.Group Base action_measurable (region s) (region_measurable hs) q⟩

include U hU in
theorem half_finite (A : 𝔄) (hA : IsSelfAdjoint A) :
    trace volume (fun x : ℍ => (half hs p hp A x).toSubmodule.starProjection)<∞ :=
  QuantitativeEulerEndpointMassTransfer.high_trace_finite
    action_measurable (region s) (region_measurable hs) p hp measure (region_finite hs)
    U hU A hA (1/2) (by norm_num)

theorem half_le (A : 𝔄) (hA0 : 0≤A) (W : ℍ → ClosedSubmodule ℂ Space)
    (hAW : ∀ x, ρ A x≤(W x).toSubmodule.starProjection) (x : ℍ) :
    (half hs p hp A x).toSubmodule≤(W x).toSubmodule :=
  space_le_baseline (α:=Base) action_measurable (region s) (region_measurable hs) p hp A hA0 W hAW x

theorem half_supported (A : 𝔄) (hA : IsSelfAdjoint A)
    (S : Subgroup AsymptoticRationalGroup.Group)
    (hAS : ∀ x, AsymptoticSubgroupSupport.Supported S (ρ A x)) (x : ℍ) :
    AsymptoticSubgroupSupport.Supported S (half hs p hp A x).toSubmodule.starProjection :=
  QuantitativeSpectralCutRegularity.highAt_supported S (ρ A x) (hAS x)
    (hA.map (QuantitativeEulerEndpointCornerCut.evaluation
      action_measurable (region s) (region_measurable hs) p hp x)) (1/2)

theorem packet_mass_eq (A : 𝔄) (N : ℕ) (hN : 0<N) (w : ℂ)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (l : List (EligiblePrime N)) (c : ℝ) (hc : 0<c) :
    (trace measure (QuantitativeSpectralRegularPacket.projectionFamily
      (fun x : Base => half hs p hp A x) (packetRows N hN w hs hε t l) c l.length)).toReal=
    cornerMass (primeChain N hN w hs hε t c (half hs p hp A) l) := by
  congr 1
  congr 1
  funext x
  change (QuantitativeSpectralDeflationChain.chain (half hs p hp A x)
    (fun i => packetSequence N hN w hs hε t l i x) c l.length).toSubmodule.starProjection=_
  exact congrArg (fun V : ClosedSubmodule ℂ Space => V.toSubmodule.starProjection)
    (primeChain_eq_packet N hN w hs hε t c hc (half hs p hp A) l (show ℍ from x)).symm

#print axioms half_regular
#print axioms half_finite
#print axioms half_le
#print axioms half_supported
#print axioms packet_mass_eq
end QuantitativeEulerEndpointPreparedHalf
