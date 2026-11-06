module

public import QuantitativeSpectralPacketSmallMassV1
public import QuantitativeSpectralLogErrorV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralPacketLogError

open AsymptoticRegularTrace AsymptoticOrbitDiagonal
open QuantitativeSpectralRegularAlgebra QuantitativeSpectralRegularOrder
open QuantitativeSpectralPacketEmbedding QuantitativeSpectralRegularPacket
open QuantitativeSpectralDeflationChain QuantitativeSpectralPacketAssembly
open QuantitativeSpectralPacketFactor QuantitativeSpectralTriangularAssembly
open QuantitativeSpectralPacketIntrinsic QuantitativeSpectralSourceGram
open QuantitativeSpectralFiniteCornerDistribution QuantitativeSpectralFiniteCornerTrace
open QuantitativeSpectralPacketDeterminantData
open MeasureTheory
open scoped lp ENNReal

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]
variable (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)
  (U : α → ClosedSubmodule ℂ ℓ²(G,ℂ))
  (hU : ∀ x, (U x).toSubmodule.starProjection = corner s x)
  (B : ℕ → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
  (hmB : ∀ i g h, Measurable (fun x => matrix (B i x) g h))
  (hcB : ∀ i, Covariant (B i)) (C : ℕ → ℝ) (hC : ∀ i x, ‖B i x‖ ≤ C i)
  (c : ℝ) (hc : 0 < c) (hsource : ∀ i x, B i x * corner s x = B i x)

local notation "P" => projectionElement hact s hs U hU B hmB hcB C hC c hc
local notation "E" => rowElement hact s hs U hU B hmB hcB C hC c hc hsource
local notation "ρ" => representation G α hact s hs
local notation "A" => FiniteCorner G α hact s hs

local notation "Q" => blockElements hact s hs U hU B hmB hcB C hC c hc
local notation "L" => rowElements hact s hs U hU B hmB hcB C hC c hc hsource
local notation "D" => diagonalElement hact s hs U hU B hmB hcB C hC c hc
local notation "V" => strictElement hact s hs U hU B hmB hcB C hC c hc hsource
local notation "F" => fun i => gramElement hact s hs (B i) (hmB i) (hcB i) (C i) (hC i) (hsource i)

local notation "S" => regularizedGram hact s hs B hmB hcB C hC hsource

variable (μ : Measure α) (hf : μ s < ∞)
  (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
local notation "τ" => rootedTrace μ hact s hs hf

/-- The finite-corner rooted functional and the positive regular orbit trace
agree on the actual surviving projection. This is the bridge between packet
contraction and the determinant spectral-distribution estimate. -/
theorem rooted_projection_trace (n : ℕ) :
    τ (P n) = (trace μ (projectionFamily U B c n)).toReal := by
  change signedTrace μ (projectionFamily U B c n) = _
  have hr := projection_regular U B c (initial_matrix_measurable hact s hs U hU)
    (initial_covariant s U hU) hmB hcB C hC hc n
  apply signedTrace_eq_toReal μ _ (hr.1 1 1)
  intro x
  apply ContinuousLinearMap.nonneg_iff_isPositive.mp
  have hp := projectionElement_projection hact s hs U hU B hmB hcB C hC c hc n
  exact (pointwise_le_iff hact s hs 0 (P n)).mpr hp.nonneg x

include hmp hU hc in
/-- Explicit collective bound for the unregularized source spectrum: the
actual surviving trace plus a logarithmic error. The row count enters only
through the source norm bound `K`; no product of polynomial filter degrees is
introduced. -/
theorem packet_source_log_error (n : ℕ) {d K : ℝ} (hd : 0 < d)
    (hK : 0 < K) (hcut : 2*d^2 < K) (hcK : c^2 ≤ K)
    (hbound : (∑ i : Fin n, (C i)^2) + d^2 ≤ K) :
    (QuantitativeTracialSpectralMeasure.measure τ (rootedTrace_mono hact s hs μ hf)
      (∑ i : Fin n, F i)
      (sourceSum_nonneg hact s hs B hmB hcB C hC hsource n).isSelfAdjoint).real
      {x : spectrum ℝ (∑ i : Fin n, F i) | (x : ℝ) ≤ d^2} ≤
      (trace μ (projectionFamily U B c n)).toReal +
        (μ s).toReal * Real.log (2*K/c^2) / Real.log (K/(2*d^2)) := by
  have hp := projectionElement_projection hact s hs U hU B hmB hcB C hC c hc n
  have hp0 : 0 ≤ τ (P n) := by
    simpa only [map_zero] using rootedTrace_mono hact s hs μ hf hp.nonneg
  have hp1 : τ (P n) ≤ (μ s).toReal := by
    simpa only [rootedTrace_one hact s hs μ hf] using rootedTrace_mono hact s hs μ hf hp.le_one
  have hm := QuantitativeSpectralPacketSmallMass.packet_source_small_mass
    hact s hs U hU B hmB hcB C hC c hc hsource μ hf hmp n hd hK hcut hbound
  have he := QuantitativeSpectralLogError.log_quotient_le_survivor hp0 hp1
    (sq_pos_of_pos hc) (sq_pos_of_pos hd) hK hcK hcut
  have hh := hm.trans he
  rwa [rooted_projection_trace hact s hs U hU B hmB hcB C hC c hc μ hf n] at hh

#print axioms rooted_projection_trace
#print axioms packet_source_log_error

end QuantitativeSpectralPacketLogError
