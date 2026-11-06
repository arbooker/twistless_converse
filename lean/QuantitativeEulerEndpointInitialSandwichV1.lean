module

public import QuantitativeEulerEndpointBlockGramV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointInitialSandwich
open ContinuousLinearMap QuantitativeEulerEndpointSubcorner
open QuantitativeEulerEndpointSubcornerSourceGram QuantitativeEulerEndpointCornerCut
open AsymptoticRegularTrace MeasureTheory
open scoped lp

section Algebra
variable {𝔄 𝔅 : Type*} [CStarAlgebra 𝔄] [CStarAlgebra 𝔅]

/-- Norm swapping identifies the external detector sandwich with the
intrinsic compressed Gram sandwich. The homomorphism need not be unital. -/
theorem detector_norm_eq (φ : 𝔄 →⋆ₙₐ[ℂ] 𝔅) (X G : 𝔄) (hX : IsSelfAdjoint X)
    (B : 𝔅) (hG : φ G=star B*B) :
    ‖B*φ (X^2)*star B‖=‖φ (X*G*X)‖ := by
  have hx : star (φ X)=φ X := (hX.map φ).star_eq
  have hleft : B*φ (X^2)*star B=(B*φ X)*star (B*φ X) := by
    rw [pow_two,map_mul,star_mul,hx]
    simp only [mul_assoc]
  have hright : φ (X*G*X)=star (B*φ X)*(B*φ X) := by
    rw [map_mul,map_mul,hG,star_mul,hx]
    simp only [mul_assoc]
  rw [hleft,hright,CStarRing.norm_self_mul_star,CStarRing.norm_star_mul_self]
end Algebra

section Order
variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]

theorem weighted_sandwich_norm (X G D : 𝔄) (hX : IsSelfAdjoint X) (hD : 0≤D)
    {w : ℝ} (hw : 0≤w) (hDG : w • D≤G) :
    w*‖X*D*X‖≤‖X*G*X‖ := by
  have hconj := hX.conjugate_le_conjugate hDG
  have hs : X*(w • D)*X=w • (X*D*X) := by
    rw [mul_smul_comm,smul_mul_assoc]
  rw [hs] at hconj
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg hconj
    (smul_nonneg hw (hX.conjugate_nonneg hD))
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hw] using hn
end Order

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]
variable (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)
  (p : QuantitativeSpectralRegularAlgebra.FiniteCorner G α hact s hs) (hp : IsStarProjection p)
  (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
  (hmB : ∀ g h, Measurable (fun x => matrix (B x) g h)) (hcB : Covariant B)
  (C : ℝ) (hC : ∀ x, ‖B x‖≤C)
  (hsource : ∀ x, B x*QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x=B x)
local notation "𝔄" => Subcorner hact s hs p hp
local notation "ρ" => representation hact s hs p hp
local notation "D" => gramElement hact s hs p hp B hmB hcB C hC hsource

theorem actual_detector_norm_le (X : 𝔄) (hX : IsSelfAdjoint X) (x : α) :
    ‖B x*ρ (X^2) x*star (B x)‖≤‖X*D*X‖ := by
  exact (detector_norm_eq (evaluation hact s hs p hp x) X D hX (B x) rfl).le.trans
    (QuantitativeSpectralRegularAlgebra.representation_norm_le G α hact s hs (X*D*X).val x)

#print axioms detector_norm_eq
#print axioms weighted_sandwich_norm
#print axioms actual_detector_norm_le
end QuantitativeEulerEndpointInitialSandwich
