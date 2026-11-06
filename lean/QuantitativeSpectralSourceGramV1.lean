module

public import QuantitativeSpectralPacketEmbeddingV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralSourceGram

open AsymptoticRegularTrace AsymptoticOrbitDiagonal
open QuantitativeSpectralRegularAlgebra QuantitativeSpectralRegularEmbedding
open QuantitativeSpectralRegularOrder QuantitativeSpectralFiniteCornerDistribution
open MeasureTheory ContinuousLinearMap
open scoped lp

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]
variable (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)
  (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
  (hm : ∀ g h, Measurable (fun x => matrix (B x) g h)) (hc : Covariant B)
  (C : ℝ) (hn : ∀ x, ‖B x‖ ≤ C) (hsource : ∀ x, B x * corner s x = B x)

/-- A residual may have output outside the terminal corner. Its Gram
operator nevertheless lies in that corner, without compressing its output. -/
def gramElement : FiniteCorner G α hact s hs := by
  have hmG := matrix_comp_measurable _ _ (matrix_adjoint_measurable _ hm) hm
  have hcG := covariant_comp _ _ (covariant_adjoint _ hc) hc
  have hnG (x : α) : ‖star (B x) * B x‖ ≤ C^2 := by
    have hh : ‖star (B x)‖ ≤ C := (_root_.norm_star (B x)).le.trans (hn x)
    simpa only [pow_two] using norm_mul_le_of_le hh (hn x)
  refine ofFamily hact s hs (fun x => star (B x) * B x) (C^2) hnG hmG hcG ?_ ?_
  · intro x
    have hh : corner s x * star (B x) = star (B x) := by
      have he := congrArg star (hsource x)
      have hsc : star (corner (G := G) s x) = corner s x := corner_adjoint s x
      simpa only [star_mul, hsc] using he
    rw [← ContinuousLinearMap.mul_def, ← mul_assoc, hh]
  · intro x
    rw [← ContinuousLinearMap.mul_def, mul_assoc, hsource]

@[simp] theorem representation_gramElement :
    representation G α hact s hs (gramElement hact s hs B hm hc C hn hsource) =
      (fun x => star (B x) * B x) := rfl

theorem gramElement_nonneg : 0 ≤ gramElement hact s hs B hm hc C hn hsource := by
  apply (pointwise_le_iff hact s hs 0 _).mp
  intro x
  change 0 ≤ star (B x) * B x
  exact star_mul_self_nonneg (B x)

theorem gramElement_norm_le : ‖gramElement hact s hs B hm hc C hn hsource‖ ≤ C^2 := by
  apply (BoundedContinuousFunction.norm_le (sq_nonneg C)).mpr
  intro x
  change ‖star (B x) * B x‖ ≤ C^2
  have hh : ‖star (B x)‖ ≤ C := (_root_.norm_star (B x)).le.trans (hn x)
  simpa only [pow_two] using norm_mul_le_of_le hh (hn x)

#print axioms gramElement
#print axioms representation_gramElement
#print axioms gramElement_nonneg
#print axioms gramElement_norm_le

end QuantitativeSpectralSourceGram
