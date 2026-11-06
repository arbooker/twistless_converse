module

public import QuantitativeSpectralRegularInverseV1
public import AsymptoticRegularSignedTraceV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeSpectralRegularRow

open QuantitativeSpectralNormalizedRow QuantitativeSpectralRegularInverse
open AsymptoticRegularTrace MeasureTheory ContinuousLinearMap
open scoped lp

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]

/-- Actual explicit inverse rows preserve regularity. The inverse family is
constructed by continuous functional calculus using its proved lower bound. -/
theorem normalizer_regular
    (R B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hmR : ∀ g h, Measurable (fun x => matrix (R x) g h)) (hcR : Covariant R)
    (hmB : ∀ g h, Measurable (fun x => matrix (B x) g h)) (hcB : Covariant B)
    (hpR : ∀ x, IsStarProjection (R x)) (c : ℝ) (hc : 0 < c)
    (hcoercive : ∀ x, c^2 • R x ≤ R x * star (B x) * B x * R x)
    (C : ℝ) (hC : ∀ x, ‖B x‖ ≤ C) :
    (∀ g h, Measurable (fun x => matrix (normalizer (R x) (B x) c) g h)) ∧
      Covariant (fun x => normalizer (R x) (B x) c) := by
  let F := fun x => R x * star (B x) * B x * R x
  have hmF : ∀ g h, Measurable (fun x => matrix (F x) g h) :=
    matrix_comp_measurable _ _
      (matrix_comp_measurable _ _ (matrix_comp_measurable _ _ hmR
        (matrix_adjoint_measurable _ hmB)) hmB) hmR
  have hcF : Covariant F := covariant_comp _ _
    (covariant_comp _ _ (covariant_comp _ _ hcR (covariant_adjoint _ hcB)) hcB) hcR
  let M := fun x => augmentedGram (R x) (B x) c
  have hmM : ∀ g h, Measurable (fun x => matrix (M x) g h) := by
    apply matrix_add_measurable _ _
    · exact matrix_smul_measurable (((c^2)⁻¹ : ℝ) : ℂ) F hmF
    · exact matrix_sub_measurable _ _ (fun _ _ => measurable_const) hmR
  have hcM : Covariant M := covariant_add _ _
    (covariant_smul (((c^2)⁻¹ : ℝ) : ℂ) F hcF) (covariant_sub _ _ covariant_one hcR)
  have hnM (x : α) : ‖M x‖ ≤ (c^2)⁻¹ * C^2 + 2 := by
    have hnR : ‖R x‖ ≤ 1 :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg _ (hpR x).nonneg).mpr (hpR x).le_one
    have hnstar : ‖star (B x)‖ ≤ C := (_root_.norm_star (B x)).le.trans (hC x)
    have hn1 : ‖(1 : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hnF : ‖F x‖ ≤ C^2 := by
      have hh := norm_mul_le_of_le
        (norm_mul_le_of_le (norm_mul_le_of_le hnR hnstar)
          (hC x)) hnR
      simpa only [one_mul, mul_one, ← pow_two] using hh
    have hnS : ‖(1 : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) - R x‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by linarith)
    change ‖(c^2)⁻¹ • F x + (1 - R x)‖ ≤ _
    apply (norm_add_le _ _).trans
    apply add_le_add _ hnS
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg c))]
    exact mul_le_mul_of_nonneg_left hnF (inv_nonneg.mpr (sq_nonneg c))
  have hreg := inverse_regular M hmM hcM
    (fun x => augmentedGram_ge_one (R x) (B x) c hc (hcoercive x)) _ hnM
  constructor
  · exact matrix_smul_measurable ((c⁻¹ : ℝ) : ℂ) _
      (matrix_comp_measurable _ _ (matrix_comp_measurable _ _ hreg.1 hmR)
        (matrix_adjoint_measurable _ hmB))
  · exact covariant_smul ((c⁻¹ : ℝ) : ℂ) _
      (covariant_comp _ _ (covariant_comp _ _ hreg.2 hcR) (covariant_adjoint _ hcB))

#print axioms normalizer_regular

end QuantitativeSpectralRegularRow
