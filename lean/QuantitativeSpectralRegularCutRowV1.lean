module

public import QuantitativeSpectralRegularRowV1
public import QuantitativeSpectralCutRegularityV1
public import QuantitativeSpectralCutRowV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeSpectralRegularCutRow

open AsymptoticRegularTrace AsymptoticSubgroupSupport
open QuantitativeSpectralCutRow QuantitativeSpectralCutRegularity
open QuantitativeSpectralNormalizedRow QuantitativeSpectralRegularInverse
open MeasureTheory ContinuousLinearMap
open scoped lp

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]

theorem cutNormalizer_regular (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h, Measurable (fun x => matrix (B x) g h)) (hc : Covariant B)
    (C : ℝ) (hC : ∀ x, ‖B x‖ ≤ C) (c : ℝ) (hcpos : 0 < c) :
    (∀ g h, Measurable (fun x => matrix (cutNormalizer (B x) c) g h)) ∧
      Covariant (fun x => cutNormalizer (B x) c) := by
  have hmG := matrix_comp_measurable _ _ (matrix_adjoint_measurable _ hm) hm
  have hcG := covariant_comp _ _ (covariant_adjoint _ hc) hc
  have hnG (x : α) : ‖star (B x) * B x‖ ≤ C^2 := by
    have hh : ‖star (B x)‖ ≤ C := (_root_.norm_star (B x)).le.trans (hC x)
    simpa only [pow_two] using norm_mul_le_of_le hh (hC x)
  have hR := highAt_regular (fun x => star (B x) * B x) hmG hcG
    (fun x => IsSelfAdjoint.star_mul_self (B x)) (C^2) hnG (c^2)
  exact QuantitativeSpectralRegularRow.normalizer_regular (fun x => removed (B x) c) B
    hR.1 hR.2 hm hc (fun x => removed_projection (B x) c) c hcpos
    (fun x => removed_coercive (B x) c) C hC

omit [Countable G] in
/-- The explicit inverse normalization preserves subgroup support. This
keeps all earlier cut operations integral at every unused prime. -/
theorem normalizer_supported (S : Subgroup G)
    (R B : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hR : Supported S R) (hB : Supported S B) (c : ℝ) (hc : 0 < c)
    (hcoercive : c^2 • R ≤ R * star B * B * R) :
    Supported S (normalizer R B c) := by
  have hG : Supported S (R * star B * B * R) :=
    supported_comp _ _ _ (supported_comp _ _ _
      (supported_comp _ _ _ hR (supported_adjoint S B hB)) hB) hR
  have hM : Supported S (augmentedGram R B c) := by
    apply supported_add
    · exact supported_smul S _ hG (((c^2)⁻¹ : ℝ) : ℂ)
    · exact supported_sub S _ _ (supported_one S) hR
  have hp := augmentedGram_ge_one R B c hc hcoercive
  have hI : Supported S (Ring.inverse (augmentedGram R B c)) := by
    rw [inverse_eq_cfc _ hp]
    exact supported_cfc S _ hM
      (IsStrictlyPositive.of_le isStrictlyPositive_one hp).nonneg.isSelfAdjoint
      _ clippedInverse_continuous
  exact supported_smul S _
    (supported_comp _ _ _ (supported_comp _ _ _ hI hR) (supported_adjoint S B hB))
    ((c⁻¹ : ℝ) : ℂ)

omit [Countable G] in
/-- Subgroup support for the actual cut normalizer, with its cut and
coercivity discharged by the spectral construction. -/
theorem cutNormalizer_supported (S : Subgroup G) (B : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : Supported S B) (c : ℝ) (hc : 0 < c) : Supported S (cutNormalizer B c) := by
  have hG : Supported S (star B * B) := supported_comp _ _ _ (supported_adjoint S B hB) hB
  have hR := highAt_supported S (star B * B) hG (IsSelfAdjoint.star_mul_self B) (c^2)
  exact normalizer_supported S (removed B c) B hR hB c hc (removed_coercive B c)

#print axioms cutNormalizer_regular
#print axioms normalizer_supported
#print axioms cutNormalizer_supported

end QuantitativeSpectralRegularCutRow
