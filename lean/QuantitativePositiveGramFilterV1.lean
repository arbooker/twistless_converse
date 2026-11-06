module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativePositiveGramFilter

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem row_gram_le (B : H →L[ℂ] K) :
    B.adjoint.comp B ≤ ‖B‖^2 • (1 : H →L[ℂ] H) := by
  have hp : 0 ≤ B.adjoint.comp B :=
    ContinuousLinearMap.nonneg_iff_isPositive.mpr B.isPositive_adjoint_comp_self
  calc
    _ ≤ algebraMap ℝ (H →L[ℂ] H) ‖B.adjoint.comp B‖ :=
      IsSelfAdjoint.le_algebraMap_norm_self _ (IsSelfAdjoint.of_nonneg hp)
    _ = ‖B.adjoint.comp B‖ • (1 : H →L[ℂ] H) := Algebra.algebraMap_eq_smul_one _
    _ ≤ _ := by
      apply smul_le_smul_of_nonneg_right _ zero_le_one
      calc
        _ ≤ ‖B.adjoint‖ * ‖B‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ = _ := by rw [ContinuousLinearMap.adjoint.norm_map,pow_two]

theorem gram_sum_bounds {ι : Type*} (qs : Finset ι) (B : ι → H →L[ℂ] K) :
    0 ≤ ∑ q ∈ qs, (B q).adjoint.comp (B q) ∧
      (∑ q ∈ qs, (B q).adjoint.comp (B q)) ≤
        (1 + ∑ q ∈ qs, ‖B q‖^2) • (1 : H →L[ℂ] H) := by
  refine ⟨Finset.sum_nonneg (fun q _ =>
    ContinuousLinearMap.nonneg_iff_isPositive.mpr (B q).isPositive_adjoint_comp_self),?_⟩
  calc
    _ ≤ ∑ q ∈ qs, ‖B q‖^2 • (1 : H →L[ℂ] H) :=
      Finset.sum_le_sum (fun q _ => row_gram_le (B q))
    _ = (∑ q ∈ qs, ‖B q‖^2) • (1 : H →L[ℂ] H) := (Finset.sum_smul ..).symm
    _ ≤ _ := by
      apply smul_le_smul_of_nonneg_right _ zero_le_one
      linarith

theorem filter_order (S : H →L[ℂ] H) {b : ℝ} (hb : 0 < b)
    (h0 : 0 ≤ S) (h1 : S ≤ b • (1 : H →L[ℂ] H)) (d : ℕ) :
    0 ≤ (1-b⁻¹ • S)^d ∧ (1-b⁻¹ • S)^d ≤ 1 ∧ ‖(1-b⁻¹ • S)^d‖ ≤ 1 := by
  have hscaled : b⁻¹ • S ≤ (1 : H →L[ℂ] H) := by
    have hh := smul_le_smul_of_nonneg_left h1 (inv_nonneg.mpr hb.le)
    simpa only [smul_smul,inv_mul_cancel₀ hb.ne',one_smul] using hh
  have hbase0 := sub_nonneg.mpr hscaled
  have hbase1 : 1-b⁻¹ • S ≤ 1 := sub_le_self _ (smul_nonneg (inv_nonneg.mpr hb.le) h0)
  have hp0 := CStarAlgebra.pow_nonneg _ d hbase0
  have hp1 : (1-b⁻¹ • S)^d ≤ 1 := by
    simpa using CStarAlgebra.pow_antitone hbase1 hbase0 (Nat.zero_le d)
  exact ⟨hp0,hp1,(CStarAlgebra.norm_le_one_iff_of_nonneg _ hp0).mpr hp1⟩

#print axioms row_gram_le
#print axioms filter_order

end QuantitativePositiveGramFilter
