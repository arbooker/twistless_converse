module

public import QuantitativeSpectralRegularCutRowV1
public import QuantitativeSpectralCornerCutRowV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralRegularCornerStep

open AsymptoticRegularTrace AsymptoticSubgroupSupport
open QuantitativeSpectralCornerCutRow QuantitativeSpectralCutRow
open QuantitativeSpectralCutRegularity QuantitativeSpectralRegularCutRow
open MeasureTheory ContinuousLinearMap
open scoped lp

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]

/-- A complete regular deflation step: both its surviving projection and
its normalized residual row are actual measurable covariant families. -/
theorem step_regular
    (U : α → Submodule ℂ ℓ²(G,ℂ)) [∀ x, CompleteSpace (U x)]
    (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hmU : ∀ g h, Measurable (fun x => matrix (U x).starProjection g h))
    (hcU : Covariant (fun x => (U x).starProjection))
    (hmB : ∀ g h, Measurable (fun x => matrix (B x) g h)) (hcB : Covariant B)
    (C : ℝ) (hC : ∀ x, ‖B x‖ ≤ C) (c : ℝ) (hc : 0 < c) :
    ((∀ g h, Measurable (fun x => matrix (nextSpace (U x) (B x) c).starProjection g h)) ∧
      Covariant (fun x => (nextSpace (U x) (B x) c).starProjection)) ∧
    ((∀ g h, Measurable (fun x => matrix (row (U x) (B x) c) g h)) ∧
      Covariant (fun x => row (U x) (B x) c)) := by
  let T := fun x => restricted (U x) (B x)
  have hmT : ∀ g h, Measurable (fun x => matrix (T x) g h) :=
    matrix_comp_measurable _ _ hmB hmU
  have hcT : Covariant T := covariant_comp _ _ hcB hcU
  have hnT (x : α) : ‖T x‖ ≤ C := by
    have hh := norm_mul_le_of_le (hC x) (U x).starProjection_norm_le
    simpa only [T, restricted, mul_one] using hh
  have hnG (x : α) : ‖star (T x) * T x‖ ≤ C^2 := by
    have hs : ‖star (T x)‖ ≤ C := (_root_.norm_star (T x)).le.trans (hnT x)
    simpa only [pow_two] using norm_mul_le_of_le hs (hnT x)
  have hR := highAt_regular (fun x => star (T x) * T x)
    (matrix_comp_measurable _ _ (matrix_adjoint_measurable _ hmT) hmT)
    (covariant_comp _ _ (covariant_adjoint _ hcT) hcT)
    (fun x => IsSelfAdjoint.star_mul_self (T x)) (C^2) hnG (c^2)
  have hW := cutNormalizer_regular T hmT hcT C hnT c hc
  constructor
  · simp only [nextSpace_projection]
    exact ⟨matrix_sub_measurable _ _ hmU hR.1, covariant_sub _ _ hcU hR.2⟩
  · exact ⟨matrix_comp_measurable _ _ hW.1 hmB, covariant_comp _ _ hW.2 hcB⟩

omit [Countable G] in
/-- Exact integrality of the whole corner update at an unused prime.
Every operation is shown to remain in the chosen subgroup algebra. -/
theorem step_supported (S : Subgroup G)
    (U : Submodule ℂ ℓ²(G,ℂ)) [CompleteSpace U] (B : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hU : Supported S U.starProjection) (hB : Supported S B) (c : ℝ) (hc : 0 < c) :
    Supported S (nextSpace U B c).starProjection ∧ Supported S (row U B c) := by
  have hT : Supported S (restricted U B) := supported_comp _ _ _ hB hU
  have hG : Supported S (star (restricted U B) * restricted U B) :=
    supported_comp _ _ _ (supported_adjoint S _ hT) hT
  have hR := highAt_supported S _ hG (IsSelfAdjoint.star_mul_self (restricted U B)) (c^2)
  constructor
  · rw [nextSpace_projection]
    exact supported_sub S _ _ hU hR
  · exact supported_comp _ _ _ (cutNormalizer_supported S _ hT c hc) hB

#print axioms step_regular
#print axioms step_supported

end QuantitativeSpectralRegularCornerStep
