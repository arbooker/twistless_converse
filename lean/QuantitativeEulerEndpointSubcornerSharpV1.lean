module

public import QuantitativeEulerEndpointSubcornerSmallMassV1
public import QuantitativeEulerEndpointSharpPacketV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointSubcornerSharp

open AsymptoticRegularTrace AsymptoticOrbitDiagonal
open QuantitativeEulerEndpointSubcorner
open QuantitativeEulerEndpointSubcornerEmbedding QuantitativeSpectralRegularPacket
open QuantitativeSpectralDeflationChain QuantitativeSpectralPacketAssembly
open QuantitativeSpectralPacketFactor QuantitativeSpectralTriangularAssembly
open QuantitativeEulerEndpointSubcornerIntrinsic QuantitativeEulerEndpointSubcornerSourceGram
open QuantitativeEulerEndpointSubcornerDeterminantData
open MeasureTheory
open scoped lp ENNReal

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]
variable (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)
  (p : QuantitativeSpectralRegularAlgebra.FiniteCorner G α hact s hs) (hp : IsStarProjection p)
  (U : α → ClosedSubmodule ℂ ℓ²(G,ℂ))
  (hU : ∀ x, (U x).toSubmodule.starProjection = QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x)
  (B : ℕ → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
  (hmB : ∀ i g h, Measurable (fun x => matrix (B i x) g h))
  (hcB : ∀ i, Covariant (B i)) (C : ℕ → ℝ) (hC : ∀ i x, ‖B i x‖ ≤ C i)
  (c : ℝ) (hc : 0 < c) (hsource : ∀ i x, B i x * QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x = B i x)

local notation "P" => projectionElement hact s hs p hp U hU B hmB hcB C hC c hc
local notation "E" => rowElement hact s hs p hp U hU B hmB hcB C hC c hc hsource
local notation "ρ" => representation hact s hs p hp
local notation "A" => Subcorner hact s hs p hp

local notation "Q" => blockElements hact s hs p hp U hU B hmB hcB C hC c hc
local notation "L" => rowElements hact s hs p hp U hU B hmB hcB C hC c hc hsource
local notation "D" => diagonalElement hact s hs p hp U hU B hmB hcB C hC c hc
local notation "V" => strictElement hact s hs p hp U hU B hmB hcB C hC c hc hsource
local notation "F" => fun i => gramElement hact s hs p hp (B i) (hmB i) (hcB i) (C i) (hC i) (hsource i)

local notation "S" => regularizedGram hact s hs p hp B hmB hcB C hC hsource

variable (μ : Measure α) (hf : μ s < ∞)
  (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
local notation "τ" => rootedTrace hact s hs p hp μ hf

/-- The finite-corner rooted functional and the positive regular orbit trace
agree on the actual surviving projection. This is the bridge between packet
contraction and the determinant spectral-distribution estimate. -/
theorem rooted_projection_trace (n : ℕ) :
    τ (P n) = (trace μ (projectionFamily U B c n)).toReal := by
  change signedTrace μ (projectionFamily U B c n) = _
  have hr := projection_regular U B c (initial_matrix_measurable hact s hs p U hU)
    (initial_covariant hact s hs p U hU) hmB hcB C hC hc n
  apply signedTrace_eq_toReal μ _ (hr.1 1 1)
  intro x
  apply ContinuousLinearMap.nonneg_iff_isPositive.mp
  have hproj := projectionElement_projection hact s hs p hp U hU B hmB hcB C hC c hc n
  exact (pointwise_le_iff hact s hs p hp 0 (P n)).mpr hproj.nonneg x

include hU hc hmp in
/-- Sharp source spectral bound for a packet inside an arbitrary regular
subcorner. The incoming mass is the trace of p, not the geometric area.
All packet factorization and trace-log estimates are proved for these operators. -/
theorem packet_source_sharp_log_error (n : ℕ) {d K : ℝ}
    (hd : 0<d) (hK : 0<K) (hcut : 2*d^2<K)
    (hbound : (∑ i : Fin n, (C i)^2)+d^2≤K) :
    let q := (trace μ (projectionFamily U B c n)).toReal
    let area := QuantitativeSpectralFiniteCornerTrace.rootedTrace μ hact s hs hf p
    (QuantitativeTracialSpectralMeasure.measure τ (rootedTrace_mono hact s hs p hp μ hf)
      (∑ i : Fin n, F i)
      (sourceSum_nonneg hact s hs p hp B hmB hcB C hC hsource n).isSelfAdjoint).real
      {x : spectrum ℝ (∑ i : Fin n, F i) | (x : ℝ)≤d^2}≤
      q+(area-q)*Real.log (K/c^2)/Real.log (K/(2*d^2))+
        q*Real.log 2/Real.log (K/(2*d^2)) := by
  have h := QuantitativeEulerEndpointSubcornerSmallMass.packet_source_small_mass
    hact s hs p hp U hU B hmB hcB C hC c hc hsource μ hf hmp n hd hK hcut hbound
  rw [QuantitativeEulerEndpointSharpPacket.log_quotient_exact
      (sq_pos_of_pos hc) (sq_pos_of_pos hd) hK hcut,
    rooted_projection_trace hact s hs p hp U hU B hmB hcB C hC c hc μ hf n] at h
  exact h

#print axioms rooted_projection_trace
#print axioms packet_source_sharp_log_error
end QuantitativeEulerEndpointSubcornerSharp
