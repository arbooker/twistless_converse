module

public import QuantitativeEulerEndpointMassTransferV1
public import QuantitativeEulerEndpointSoftTraceLossV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointMassTransfer
open ContinuousLinearMap AsymptoticRegularTrace QuantitativeSpectralCut
open QuantitativeEulerEndpointSubcorner QuantitativeEulerEndpointCornerCut MeasureTheory
open scoped lp ENNReal

section Algebra
variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]
theorem sqrt_gram (A F : 𝔄) (hA : IsSelfAdjoint A) (hF : 0≤F) :
    star (CFC.sqrt F*A)*(CFC.sqrt F*A)=A*F*A := by
  rw [star_mul,hA.star_eq,(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg F)).star_eq,
    ← mul_assoc,mul_assoc A (CFC.sqrt F) (CFC.sqrt F),CFC.sqrt_mul_sqrt_self F hF]
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
local notation "𝔄" => Subcorner hact s hs p hp
local notation "ρ" => representation hact s hs p hp
local notation "τ" => rootedTrace hact s hs p hp μ hf
local notation "hτ" => rootedTrace_mono hact s hs p hp μ hf
local notation "𝔅" => Subcorner hact s hs q hq
local notation "σ" => representation hact s hs q hq
local notation "υ" => rootedTrace hact s hs q hq μ hf
local notation "hυ" => rootedTrace_mono hact s hs q hq μ hf

include U hU V hV in
/-- Transfer for the actual compressed positive energy. The square-root
family and its regularity, norm bound and soft Gram identity are constructed
from F. Only identification of D with the hard compression remains as input. -/
theorem compressed_energy_mass
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (A F : 𝔄) (D : 𝔅) (hA : 0≤A) (hF : 0≤F) (hD : IsSelfAdjoint D)
    (hhard : ∀ x, σ D x=(highAt (ρ A x) (1/2)).starProjection*ρ F x*
      (highAt (ρ A x) (1/2)).starProjection)
    {lam : ℝ} (hlam : 0<lam) :
    (QuantitativeTracialSpectralMeasure.measure υ hυ D hD).real
      {x : spectrum ℝ D | 32*lam≤(x:ℝ)}≤
    (QuantitativeTracialSpectralMeasure.measure τ hτ (A*F*A)
      (IsSelfAdjoint.of_nonneg (conjugate_nonneg_of_nonneg hF hA))).real
      {x : spectrum ℝ (A*F*A) | lam≤(x:ℝ)} := by
  let B := ρ (CFC.sqrt F)
  apply hard_to_soft_mass hact s hs p hp μ hf U hU q hq V hV hmp A (A*F*A) D
    (IsSelfAdjoint.of_nonneg hA) _ hD B
    (QuantitativeSpectralRegularAlgebra.representation_matrix_measurable G α hact s hs (CFC.sqrt F).val)
    (QuantitativeSpectralRegularAlgebra.representation_covariant G α hact s hs (CFC.sqrt F).val)
    ‖CFC.sqrt F‖
    (QuantitativeSpectralRegularAlgebra.representation_norm_le G α hact s hs (CFC.sqrt F).val)
    _ _ hlam
  · intro x
    exact (congrArg (fun a : 𝔄 => ρ a x) (sqrt_gram A F (IsSelfAdjoint.of_nonneg hA) hF)).symm
  · intro x
    rw [hhard]
    let P := (highAt (ρ A x) (1/2)).starProjection
    have hP : star P=P := isSelfAdjoint_starProjection _
    have hB : star (B x)*B x=ρ F x := by
      have he : star (CFC.sqrt F)*CFC.sqrt F=F := by
        rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg F)).star_eq,CFC.sqrt_mul_sqrt_self F hF]
      exact congrArg (fun a : 𝔄 => ρ a x) he
    change P*ρ F x*P=star (B x*P)*(B x*P)
    rw [star_mul,hP,← mul_assoc,mul_assoc P (star (B x)) (B x),hB]

#print axioms sqrt_gram
#print axioms compressed_energy_mass
end QuantitativeEulerEndpointMassTransfer
