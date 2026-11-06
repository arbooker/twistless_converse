module

public import QuantitativeEulerEndpointSubcornerDeterminantDataV1
public import QuantitativeSpectralCollectiveMassV1
public import QuantitativeSpectralTranslationV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointSubcornerSmallMass

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

include hmp in
theorem packet_trace_log_lower (n : ℕ) {d : ℝ} (hd : 0 < d) :
    τ (P n) * Real.log (d^2) + (QuantitativeSpectralFiniteCornerTrace.rootedTrace μ hact s hs hf p - τ (P n)) * Real.log (c^2) ≤
      τ (CFC.log (S n d)) := by
  have ht := log_lower_bound hact s hs p hp μ hf hmp (Q n)
    (blockElements_sum hact s hs p hp U hU B hmB hcB C hC c hc n)
    (fun i => (blockElements_projection hact s hs p hp U hU B hmB hcB C hC c hc n i).isIdempotentElem.eq)
    (strictElement_below hact s hs p hp U hU B hmB hcB C hC c hc hsource n hd)
    (D n d) (diagonalElement_isUnit hact s hs p hp U hU B hmB hcB C hC c hc n hd) (S n d)
    (factor_gram_le hact s hs p hp U hU B hmB hcB C hC c hc hsource n hd)
  rw [diagonalElement_gram hact s hs p hp U hU B hmB hcB C hC c hc n d,
    QuantitativeSpectralDiagonalLog.trace_log_two_blocks τ (P n)
      (projectionElement_projection hact s hs p hp U hU B hmB hcB C hC c hc n).isSelfAdjoint
      (projectionElement_projection hact s hs p hp U hU B hmB hcB C hC c hc n).isIdempotentElem,
    rootedTrace_one hact s hs p hp μ hf] at ht
  exact ht

include hmp in
/-- A quantitative collective small-spectrum bound for the actual recursively
constructed regular packet. No spectral cuts, triangular factor, trace-log
estimate, domination inequality, or spectral measure are assumed as inputs.
The cutoff `lam` is independent of the regularization `d²`, allowing the later
choice `lam=2*d²` before translating to the unregularized source Gram sum. -/
theorem packet_small_mass (n : ℕ) {d K lam : ℝ} (hd : 0 < d)
    (hK : 0 < K) (hlam : 0 < lam) (hlamK : lam < K)
    (hbound : (∑ i : Fin n, (C i)^2) + d^2 ≤ K) :
    (QuantitativeTracialSpectralMeasure.measure τ (rootedTrace_mono hact s hs p hp μ hf)
      (S n d) (regularizedGram_strictlyPositive hact s hs p hp B hmB hcB C hC hsource n hd).isSelfAdjoint).real
      {x : spectrum ℝ (S n d) | (x : ℝ) ≤ lam} ≤
      (QuantitativeSpectralFiniteCornerTrace.rootedTrace μ hact s hs hf p * Real.log K -
        (τ (P n) * Real.log (d^2) + (QuantitativeSpectralFiniteCornerTrace.rootedTrace μ hact s hs hf p - τ (P n)) * Real.log (c^2))) /
        Real.log (K/lam) := by
  have hpos := regularizedGram_strictlyPositive hact s hs p hp B hmB hcB C hC hsource n hd
  have hn := (regularizedGram_norm_le hact s hs p hp B hmB hcB C hC hsource n d).trans hbound
  have hh := QuantitativeSpectralCollectiveMass.small_mass_of_trace_log_lower τ
    (rootedTrace_mono hact s hs p hp μ hf) (S n d) hpos.isSelfAdjoint hpos hK hlam hlamK hn
    (packet_trace_log_lower hact s hs p hp U hU B hmB hcB C hC c hc hsource μ hf hmp n hd)
  rwa [rootedTrace_one hact s hs p hp μ hf] at hh

include hmp in
/-- The actual source Gram sum, without regularization, has small spectral mass
at `d²`. The proof applies the packet determinant bound at `2*d²` and then
uses exact translation of the CFC spectral measure, including boundary atoms. -/
theorem packet_source_small_mass (n : ℕ) {d K : ℝ} (hd : 0 < d)
    (hK : 0 < K) (hcut : 2*d^2 < K)
    (hbound : (∑ i : Fin n, (C i)^2) + d^2 ≤ K) :
    (QuantitativeTracialSpectralMeasure.measure τ (rootedTrace_mono hact s hs p hp μ hf)
      (∑ i : Fin n, F i)
      (sourceSum_nonneg hact s hs p hp B hmB hcB C hC hsource n).isSelfAdjoint).real
      {x : spectrum ℝ (∑ i : Fin n, F i) | (x : ℝ) ≤ d^2} ≤
      (QuantitativeSpectralFiniteCornerTrace.rootedTrace μ hact s hs hf p * Real.log K -
        (τ (P n) * Real.log (d^2) + (QuantitativeSpectralFiniteCornerTrace.rootedTrace μ hact s hs hf p - τ (P n)) * Real.log (c^2))) /
        Real.log (K/(2*d^2)) := by
  have hh := packet_small_mass hact s hs p hp U hU B hmB hcB C hC c hc hsource
    μ hf hmp n hd hK (mul_pos (by norm_num : (0:ℝ)<2) (sq_pos_of_pos hd)) hcut hbound
  have he := QuantitativeSpectralTranslation.low_mass_double_shift τ
    (rootedTrace_mono hact s hs p hp μ hf) (∑ i : Fin n, F i)
    (sourceSum_nonneg hact s hs p hp B hmB hcB C hC hsource n).isSelfAdjoint (d^2)
  change (QuantitativeTracialSpectralMeasure.measure τ _ (S n d) _).real _ = _ at he
  rwa [← he]

#print axioms packet_source_small_mass

#print axioms packet_trace_log_lower
#print axioms packet_small_mass

end QuantitativeEulerEndpointSubcornerSmallMass
