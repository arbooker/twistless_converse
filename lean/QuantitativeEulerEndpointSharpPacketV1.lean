module

public import QuantitativeSpectralPacketLogErrorV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointSharpPacket

/-- Exact remainder in the determinant quotient. Retaining area-p is
essential when a packet is applied repeatedly to smaller source spaces. -/
theorem log_quotient_exact {area p h eps K : ℝ}
    (hh : 0<h) (heps : 0<eps) (hK : 0<K) (hcut : 2*eps<K) :
    (area*Real.log K-(p*Real.log eps+(area-p)*Real.log h))/Real.log (K/(2*eps))=
      p+(area-p)*Real.log (K/h)/Real.log (K/(2*eps))+
        p*Real.log 2/Real.log (K/(2*eps)) := by
  have hd : 0<Real.log (K/(2*eps)) :=
    Real.log_pos ((one_lt_div (mul_pos (by norm_num) heps)).mpr hcut)
  apply (div_eq_iff hd.ne').mpr
  rw [add_mul,add_mul,div_mul_cancel₀ _ hd.ne',div_mul_cancel₀ _ hd.ne']
  rw [Real.log_div hK.ne' hh.ne',Real.log_div hK.ne' (mul_ne_zero (by norm_num) heps.ne'),
    Real.log_mul (by norm_num : (2:ℝ)≠0) heps.ne']
  ring

/-- A block packet's logarithmic cost multiplies the REMOVED mass. After
inserting its contraction, the same cost is relative to the incoming excess;
only the explicit regularization term remains additive. -/
theorem excess_after_block {mass area p target ρ θ η D : ℝ}
    (hmass : mass≤p+(area-p)*θ+p*η)
    (hpacket : p-target≤ρ*(area-target))
    (hθ : θ≤1) (hη : 0≤η) (hpD : p≤D) :
    mass-target≤(ρ+(1-ρ)*θ)*(area-target)+D*η := by
  have hweighted := mul_le_mul_of_nonneg_left hpacket (sub_nonneg.mpr hθ)
  have heta := mul_le_mul_of_nonneg_right hpD hη
  nlinarith

open AsymptoticRegularTrace AsymptoticOrbitDiagonal
open QuantitativeSpectralRegularAlgebra QuantitativeSpectralRegularOrder
open QuantitativeSpectralPacketEmbedding QuantitativeSpectralRegularPacket
open QuantitativeSpectralDeflationChain QuantitativeSpectralSourceGram
open QuantitativeSpectralFiniteCornerDistribution QuantitativeSpectralFiniteCornerTrace
open QuantitativeSpectralPacketDeterminantData QuantitativeSpectralPacketLogError
open MeasureTheory
open scoped lp ENNReal

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]
variable (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)
  (U : α → ClosedSubmodule ℂ ℓ²(G,ℂ))
  (hU : ∀ x, (U x).toSubmodule.starProjection=corner s x)
  (B : ℕ → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
  (hmB : ∀ i g h, Measurable (fun x : α => matrix (B i x) g h))
  (hcB : ∀ i, Covariant (B i)) (C : ℕ → ℝ) (hC : ∀ i x, ‖B i x‖≤C i)
  (c : ℝ) (hc : 0<c) (hsource : ∀ i x, B i x*corner s x=B i x)
  (μ : Measure α) (hf : μ s<∞)
  (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
local notation "τ" => rootedTrace μ hact s hs hf
local notation "F" => fun i => gramElement hact s hs (B i) (hmB i) (hcB i) (C i) (hC i) (hsource i)

include hU hc hmp in
/-- The actual original packet estimate with its sharper removed-trace
coefficient. No assumed spectral measure, factorization or logdet bound. -/
theorem packet_source_sharp_log_error (n : ℕ) {d K : ℝ}
    (hd : 0<d) (hK : 0<K) (hcut : 2*d^2<K)
    (hbound : (∑ i : Fin n, (C i)^2)+d^2≤K) :
    let p := (trace μ (projectionFamily U B c n)).toReal
    (QuantitativeTracialSpectralMeasure.measure τ (rootedTrace_mono hact s hs μ hf)
      (∑ i : Fin n, F i)
      (sourceSum_nonneg hact s hs B hmB hcB C hC hsource n).isSelfAdjoint).real
      {x : spectrum ℝ (∑ i : Fin n, F i) | (x : ℝ)≤d^2}≤
      p+((μ s).toReal-p)*Real.log (K/c^2)/Real.log (K/(2*d^2))+
        p*Real.log 2/Real.log (K/(2*d^2)) := by
  have h := QuantitativeSpectralPacketSmallMass.packet_source_small_mass
    hact s hs U hU B hmB hcB C hC c hc hsource μ hf hmp n hd hK hcut hbound
  rw [log_quotient_exact (sq_pos_of_pos hc) (sq_pos_of_pos hd) hK hcut,
    rooted_projection_trace hact s hs U hU B hmB hcB C hC c hc μ hf n] at h
  exact h

#print axioms excess_after_block
#print axioms packet_source_sharp_log_error
end QuantitativeEulerEndpointSharpPacket
