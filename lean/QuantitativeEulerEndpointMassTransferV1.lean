module

public import QuantitativeEulerEndpointHighTransferV1
public import QuantitativeEulerEndpointCutMassV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointMassTransfer
open ContinuousLinearMap AsymptoticRegularTrace QuantitativeSpectralCut
open QuantitativeEulerEndpointSubcorner QuantitativeEulerEndpointCornerCut MeasureTheory
open scoped lp ENNReal

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]
variable (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)
  (p : QuantitativeSpectralRegularAlgebra.FiniteCorner G α hact s hs) (hp : IsStarProjection p)
  (μ : Measure α) (hf : μ s<∞)
local notation "𝔄" => Subcorner hact s hs p hp
local notation "ρ" => representation hact s hs p hp
local notation "τ" => rootedTrace hact s hs p hp μ hf
local notation "hτ" => rootedTrace_mono hact s hs p hp μ hf

include hf in
theorem represented_trace_finite (A : 𝔄) : trace μ (ρ A)<∞ := by
  exact (AsymptoticOrbitDiagonal.trace_le_corner μ hs (ρ A)
    (QuantitativeSpectralRegularAlgebra.representation_norm_le G α hact s hs A.val)
    (QuantitativeSpectralRegularAlgebra.representation_supported G α hact s hs A.val)).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf)

variable (U : α → ClosedSubmodule ℂ ℓ²(G,ℂ))
  (hU : ∀ x, (U x).toSubmodule.starProjection = QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x)

include hf U hU in
theorem high_trace_finite (A : 𝔄) (hA : IsSelfAdjoint A) (a : ℝ) (ha : 0≤a) :
    trace μ (fun x => (highAt (ρ A x) a).starProjection)<∞ :=
  represented_trace_finite hact s hs p hp μ hf
    (cutElement hact s hs p hp U hU A hA a ha)

variable (q : QuantitativeSpectralRegularAlgebra.FiniteCorner G α hact s hs) (hq : IsStarProjection q)
  (V : α → ClosedSubmodule ℂ ℓ²(G,ℂ))
  (hV : ∀ x, (V x).toSubmodule.starProjection = QuantitativeSpectralRegularAlgebra.representation G α hact s hs q x)
local notation "𝔅" => Subcorner hact s hs q hq
local notation "σ" => representation hact s hs q hq
local notation "υ" => rootedTrace hact s hs q hq μ hf
local notation "hυ" => rootedTrace_mono hact s hs q hq μ hf

include U hU V hV in
/-- Hard spectral mass transfers to the actual soft Gram with a fixed
factor32 in the threshold. The two spectral measures may live in different
actual subcorners. The Gram identities are ordinary operator identities. -/
theorem hard_to_soft_mass
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (A C : 𝔄) (D : 𝔅) (hA : IsSelfAdjoint A) (hC : IsSelfAdjoint C) (hD : IsSelfAdjoint D)
    (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hmB : ∀ g h, Measurable (fun x => matrix (B x) g h)) (hcB : Covariant B)
    (N : ℝ) (hN : ∀ x, ‖B x‖≤N)
    (hsoft : ∀ x, ρ C x=(B x*ρ A x).adjoint.comp (B x*ρ A x))
    (hhard : ∀ x, σ D x=
      (B x*(highAt (ρ A x) (1/2)).starProjection).adjoint.comp
        (B x*(highAt (ρ A x) (1/2)).starProjection))
    {lam : ℝ} (hlam : 0<lam) :
    (QuantitativeTracialSpectralMeasure.measure υ hυ D hD).real
      {x : spectrum ℝ D | 32*lam≤(x:ℝ)}≤
    (QuantitativeTracialSpectralMeasure.measure τ hτ C hC).real
      {x : spectrum ℝ C | lam≤(x:ℝ)} := by
  have hlow := (spectral_mass_high_trace_sandwich hact s hs q hq V hV μ hf D hD
    (by positivity : 0≤16*lam) (by linarith : 16*lam<32*lam)).1
  have hhigh := (spectral_mass_high_trace_sandwich hact s hs p hp U hU μ hf C hC
    hlam.le (by linarith : lam<2*lam)).2
  have hcompare := QuantitativeEulerEndpointHighInverse.hard_to_soft_high_trace μ hmp
    (ρ A) B
    (QuantitativeSpectralRegularAlgebra.representation_matrix_measurable G α hact s hs A.val)
    (QuantitativeSpectralRegularAlgebra.representation_covariant G α hact s hs A.val)
    hmB hcB (fun x => hA.map (evaluation hact s hs p hp x)) ‖A‖ N
    (QuantitativeSpectralRegularAlgebra.representation_norm_le G α hact s hs A.val) hN
    (by norm_num : (0:ℝ)<1/2) (by positivity : 0≤2*lam)
    (by norm_num; linarith : 2*lam*((1/2:ℝ)⁻¹)^2<16*lam)
  dsimp only at hcompare
  simp only [← hsoft,← hhard] at hcompare
  have hfin := high_trace_finite hact s hs p hp μ hf U hU C hC (2*lam) (by positivity)
  have hm := ENNReal.toReal_mono hfin.ne hcompare
  apply ((hlow.trans hm).trans hhigh).trans
  refine measureReal_mono ?_ (by finiteness)
  intro x hx
  change lam<(x:ℝ) at hx
  change lam≤(x:ℝ)
  exact hx.le

#print axioms represented_trace_finite
#print axioms high_trace_finite
#print axioms hard_to_soft_mass
end QuantitativeEulerEndpointMassTransfer
