module

public import QuantitativeEulerEndpointBlockGramV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBlockMass
open ContinuousLinearMap AsymptoticRegularTrace QuantitativeSpectralCut
open QuantitativeEulerEndpointSubcorner QuantitativeEulerEndpointBlockGram
open QuantitativeEulerEndpointSubcornerSharp QuantitativeEulerEndpointMassTransfer MeasureTheory
open scoped lp ENNReal

section Algebra
variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]
theorem high_mass_complement (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ)
    (A : 𝔄) (hA : IsSelfAdjoint A) (t : ℝ) :
    τ 1-(QuantitativeTracialSpectralMeasure.measure τ hτ A hA).real
      {x : spectrum ℝ A | (x:ℝ)≤t}≤
    (QuantitativeTracialSpectralMeasure.measure τ hτ A hA).real
      {x : spectrum ℝ A | t≤(x:ℝ)} := by
  have he : {x : spectrum ℝ A | (x:ℝ)≤t}∪{x : spectrum ℝ A | t≤(x:ℝ)}=Set.univ := by
    ext x
    simp only [Set.mem_union,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
    exact le_total _ _
  have hh := measureReal_union_le (μ := QuantitativeTracialSpectralMeasure.measure τ hτ A hA)
    {x : spectrum ℝ A | (x:ℝ)≤t} {x : spectrum ℝ A | t≤(x:ℝ)}
  rw [he,QuantitativeTracialSpectralMeasure.measure_real_univ] at hh
  linarith
end Algebra

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]
variable (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)
  (p : QuantitativeSpectralRegularAlgebra.FiniteCorner G α hact s hs) (hp : IsStarProjection p)
  (μ : Measure α) (hf : μ s<∞)
  (U : α → ClosedSubmodule ℂ ℓ²(G,ℂ))
  (hU : ∀ x, (U x).toSubmodule.starProjection = QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x)
  (q : QuantitativeSpectralRegularAlgebra.FiniteCorner G α hact s hs) (hq : IsStarProjection q)
  (V : α → ClosedSubmodule ℂ ℓ²(G,ℂ))
  (hV : ∀ x, (V x).toSubmodule.starProjection = QuantitativeSpectralRegularAlgebra.representation G α hact s hs q x)
  (B : ℕ → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
  (hmB : ∀ i g h, Measurable (fun x => matrix (B i x) g h))
  (hcB : ∀ i, Covariant (B i)) (C : ℕ → ℝ) (hC : ∀ i x, ‖B i x‖≤C i)
  (hsource : ∀ i x, B i x*QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x=B i x)
local notation "𝔄" => Subcorner hact s hs p hp
local notation "ρ" => representation hact s hs p hp
local notation "τ" => rootedTrace hact s hs p hp μ hf
local notation "hτ" => rootedTrace_mono hact s hs p hp μ hf
local notation "F" => gramSum hact s hs p hp B hmB hcB C hC hsource
local notation "R" => rows hact s hs B q
local notation "hmR" => rows_measurable hact s hs B hmB q
local notation "hcR" => rows_covariant hact s hs B hcB q
local notation "hCR" => rows_norm hact s hs B C hC q hq
local notation "hsrcR" => rows_source hact s hs B q hq
local notation "D" => gramSum hact s hs q hq R hmR hcR C hCR hsrcR
local notation "υ" => rootedTrace hact s hs q hq μ hf
local notation "hυ" => rootedTrace_mono hact s hs q hq μ hf

include U hU V hV hq in
/-- Whole-packet detected mass for the actual soft source energy. The
hard packet determinant estimate and all hard-to-soft spectral comparisons
are discharged for the original rows restricted to the half cut. -/
theorem block_detected_mass
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (A : 𝔄) (hA : 0≤A)
    (hhalf : ∀ x, QuantitativeSpectralRegularAlgebra.representation G α hact s hs q x=
      (highAt (ρ A x) (1/2)).starProjection)
    (n : ℕ) (c : ℝ) (hc : 0<c) {d K : ℝ}
    (hd : 0<d) (hK : 0<K) (hcut : 2*d^2<K)
    (hbound : (∑ i : Fin n, (C i)^2)+d^2≤K) :
    let m := QuantitativeSpectralFiniteCornerTrace.rootedTrace μ hact s hs hf q
    let r := (trace μ (QuantitativeSpectralRegularPacket.projectionFamily V R c n)).toReal
    m-(r+(m-r)*Real.log (K/c^2)/Real.log (K/(2*d^2))+
      r*Real.log 2/Real.log (K/(2*d^2)))≤
    (QuantitativeTracialSpectralMeasure.measure τ hτ (A*F n*A)
      (IsSelfAdjoint.of_nonneg (conjugate_nonneg_of_nonneg
        (gramSum_nonneg hact s hs p hp B hmB hcB C hC hsource n) hA))).real
      {x : spectrum ℝ (A*F n*A) | d^2/32≤(x:ℝ)} := by
  have hF := gramSum_nonneg hact s hs p hp B hmB hcB C hC hsource n
  have hD := gramSum_nonneg hact s hs q hq R hmR hcR C hCR hsrcR n
  have hl := packet_source_sharp_log_error hact s hs q hq V hV R hmR hcR C hCR c hc hsrcR
    μ hf hmp n hd hK hcut hbound
  have hh := high_mass_complement υ hυ (D n) (IsSelfAdjoint.of_nonneg hD) (d^2)
  have ht := compressed_energy_mass hact s hs p hp μ hf U hU q hq V hV hmp A (F n) (D n)
    hA hF (IsSelfAdjoint.of_nonneg hD) (fun x => by
      rw [restricted_gramSum,hhalf]) (div_pos (sq_pos_of_pos hd) (by norm_num : (0:ℝ)<32))
  have he : 32*(d^2/32)=d^2 := by ring
  simp only [he] at ht
  have hh' := hh.trans ht
  rw [rootedTrace_one] at hh'
  dsimp only at hl ⊢
  change (QuantitativeTracialSpectralMeasure.measure υ hυ (D n)
    (IsSelfAdjoint.of_nonneg hD)).real {x : spectrum ℝ (D n) | (x:ℝ)≤d^2}≤_ at hl
  linarith

#print axioms high_mass_complement
#print axioms block_detected_mass
end QuantitativeEulerEndpointBlockMass
