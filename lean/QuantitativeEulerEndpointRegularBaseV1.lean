module

public import QuantitativeEulerEndpointCanonicalHalfV1
public import QuantitativeEulerEndpointPacketRegularV1

set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointRegularBase
open UpperHalfPlane MeasureTheory AsymptoticRegularTrace
open AsymptoticRegularCompactBranch (Space)
open QuantitativeEulerEndpointPrepared
open scoped ENNReal

/-- A discrete topological copy of the original measurable upper half-plane.
Only the topology used to package bounded operator families changes; the
measurable sets, hyperbolic measure and rational action are the originals. -/
def Base := ℍ
instance : TopologicalSpace Base := ⊥
instance : DiscreteTopology Base := ⟨rfl⟩
instance : MeasurableSpace Base := inferInstanceAs (MeasurableSpace ℍ)
instance : MulAction AsymptoticRationalGroup.Group Base :=
  inferInstanceAs (MulAction AsymptoticRationalGroup.Group ℍ)

def measure : Measure Base := (volume : Measure ℍ)
def region (s : Set ℍ) : Set Base := s

theorem action_measurable (g : AsymptoticRationalGroup.Group) :
    Measurable (fun x : Base => g • x) :=
  (AsymptoticRationalGroup.measurePreserving g).measurable

theorem action_preserving (g : AsymptoticRationalGroup.Group) :
    MeasurePreserving (fun x : Base => g • x) measure measure :=
  AsymptoticRationalGroup.measurePreserving g

theorem region_measurable {s : Set ℍ} (hs : IsCompact s) : MeasurableSet (region s) :=
  hs.measurableSet

theorem region_finite {s : Set ℍ} (hs : IsCompact s) : measure (region s)<∞ :=
  (show (volume : Measure ℍ) s<∞ from hs.measure_lt_top)

/-- The concrete finite algebra uses the original compact region, whose
compactness is always tested in the original upper half-plane topology. -/
abbrev Corner {s : Set ℍ} (hs : IsCompact s) :=
  QuantitativeSpectralRegularAlgebra.FiniteCorner AsymptoticRationalGroup.Group Base
    action_measurable (region s) (region_measurable hs)

def packetRows (N : ℕ) (hN : 0<N) (w : ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (l : List (EligiblePrime N))
    (i : ℕ) (x : Base) : Space →L[ℂ] Space :=
  packetSequence N hN w hs hε t l i x

theorem packetRows_regular (N : ℕ) (hN : 0<N) (w : ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (l : List (EligiblePrime N)) (i : ℕ) :
    (∀ g h, Measurable (fun x => matrix (packetRows N hN w hs hε t l i x) g h)) ∧
      Covariant (packetRows N hN w hs hε t l i) :=
  packet_sequence_regular N hN w hs hε t l i

theorem packetRows_norm (N : ℕ) (hN : 0<N) (w : ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (l : List (EligiblePrime N)) (i : ℕ) (x : Base) :
    ‖packetRows N hN w hs hε t l i x‖≤packetSequenceBound N hN w hs hε t l i :=
  packet_sequence_norm N hN w hs hε t l i x

theorem trace_eq (F : Base → Space →L[ℂ] Space) :
    trace measure F=trace (volume : Measure ℍ) (fun x => F x) := rfl

#print axioms action_measurable
#print axioms action_preserving
#print axioms region_finite
#print axioms packetRows_regular
#print axioms packetRows_norm
#print axioms trace_eq
end QuantitativeEulerEndpointRegularBase
