module

public import QuantitativeEulerEndpointSubcornerEmbeddingV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointSubcornerSourceGram

open AsymptoticRegularTrace AsymptoticOrbitDiagonal
open QuantitativeEulerEndpointSubcorner
open MeasureTheory ContinuousLinearMap
open scoped lp

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]
variable (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)
  (p : QuantitativeSpectralRegularAlgebra.FiniteCorner G α hact s hs) (hp : IsStarProjection p)
  (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
  (hm : ∀ g h, Measurable (fun x => matrix (B x) g h)) (hc : Covariant B)
  (C : ℝ) (hn : ∀ x, ‖B x‖ ≤ C) (hsource : ∀ x, B x * QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x = B x)

/-- A residual may have output outside the terminal corner. Its Gram
operator nevertheless lies in that corner, without compressing its output. -/
def gramElement : Subcorner hact s hs p hp := by
  have hmG := matrix_comp_measurable _ _ (matrix_adjoint_measurable _ hm) hm
  have hcG := covariant_comp _ _ (covariant_adjoint _ hc) hc
  have hnG (x : α) : ‖star (B x) * B x‖ ≤ C^2 := by
    have hh : ‖star (B x)‖ ≤ C := (_root_.norm_star (B x)).le.trans (hn x)
    simpa only [pow_two] using norm_mul_le_of_le hh (hn x)
  refine ofFamily hact s hs p hp (fun x => star (B x) * B x) (C^2) hnG hmG hcG ?_ ?_
  · intro x
    have hh : QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x * star (B x) = star (B x) := by
      have he := congrArg star (hsource x)
      have hsc : star (QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x) =
          QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x :=
        congrArg (fun a => QuantitativeSpectralRegularAlgebra.representation G α hact s hs a x) hp.isSelfAdjoint.star_eq
      simpa only [star_mul, hsc] using he
    rw [← ContinuousLinearMap.mul_def, ← mul_assoc, hh]
  · intro x
    rw [← ContinuousLinearMap.mul_def, mul_assoc, hsource]

@[simp] theorem representation_gramElement :
    representation hact s hs p hp (gramElement hact s hs p hp B hm hc C hn hsource) =
      (fun x => star (B x) * B x) := rfl

theorem gramElement_nonneg : 0 ≤ gramElement hact s hs p hp B hm hc C hn hsource := by
  apply (pointwise_le_iff hact s hs p hp 0 _).mp
  intro x
  change 0 ≤ star (B x) * B x
  exact star_mul_self_nonneg (B x)

theorem gramElement_norm_le : ‖gramElement hact s hs p hp B hm hc C hn hsource‖ ≤ C^2 := by
  apply (BoundedContinuousFunction.norm_le (sq_nonneg C)).mpr
  intro x
  change ‖star (B x) * B x‖ ≤ C^2
  have hh : ‖star (B x)‖ ≤ C := (_root_.norm_star (B x)).le.trans (hn x)
  simpa only [pow_two] using norm_mul_le_of_le hh (hn x)

#print axioms gramElement
#print axioms representation_gramElement
#print axioms gramElement_nonneg
#print axioms gramElement_norm_le

end QuantitativeEulerEndpointSubcornerSourceGram
