module

public import QuantitativeMaassCuspidalizerV1
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

set_option autoImplicit false

@[expose] public section

namespace QuantitativeMaass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Positivity and contraction of the actual bounded LV polynomial. The
normalization hypothesis is a scalar operator-norm bound, not a spectral
assumption about eigenvectors or the desired counting theorem. -/
theorem lvFilter_order (D : H →L[ℂ] H) (hD : IsSelfAdjoint D)
    (c : ℝ) (hc : 0 ≤ c) (hcD : c * ‖D‖ ^ 2 ≤ 1) (d : ℕ) :
    0 ≤ lvFilter D c d ∧ lvFilter D c d ≤ 1 := by
  have hsq : 0 ≤ D ^ 2 := by
    simpa only [pow_two, hD.star_eq] using star_mul_self_nonneg D
  have hsqbound : D ^ 2 ≤ ‖D‖ ^ 2 • (1 : H →L[ℂ] H) := by
    simpa only [pow_two, hD.star_eq, Algebra.algebraMap_eq_smul_one] using
      CStarAlgebra.star_mul_le_algebraMap_norm_sq D
  have hscaled0 : 0 ≤ c • D ^ 2 := smul_nonneg hc hsq
  have hscaled1 : c • D ^ 2 ≤ (1 : H →L[ℂ] H) := by
    calc
      c • D ^ 2 ≤ c • (‖D‖ ^ 2 • (1 : H →L[ℂ] H)) :=
        smul_le_smul_of_nonneg_left hsqbound hc
      _ = (c * ‖D‖ ^ 2) • (1 : H →L[ℂ] H) := by rw [smul_smul]
      _ ≤ 1 • (1 : H →L[ℂ] H) := smul_le_smul_of_nonneg_right hcD zero_le_one
      _ = 1 := one_smul ℝ _
  have hbase0 : 0 ≤ 1 - c • D ^ 2 := sub_nonneg.mpr hscaled1
  have hbase1 : 1 - c • D ^ 2 ≤ 1 := sub_le_self _ hscaled0
  have hpow0 := CStarAlgebra.pow_nonneg (1 - c • D ^ 2) d hbase0
  have hpow1 : (1 - c • D ^ 2) ^ d ≤ 1 := by
    simpa using CStarAlgebra.pow_antitone hbase1 hbase0 (Nat.zero_le d)
  exact ⟨sub_nonneg.mpr hpow1, sub_le_self _ hpow0⟩

theorem lvFilter_norm_le_one (D : H →L[ℂ] H) (hD : IsSelfAdjoint D)
    (c : ℝ) (hc : 0 ≤ c) (hcD : c * ‖D‖ ^ 2 ≤ 1) (d : ℕ) :
    ‖lvFilter D c d‖ ≤ 1 := by
  obtain ⟨h0, h1⟩ := lvFilter_order D hD c hc hcD d
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ h0).mpr h1

/-- The normalization used in the analytic construction, with any positive
B bounding the operator norm, gives a positive contraction. -/
theorem lvFilter_normalized_order (D : H →L[ℂ] H) (hD : IsSelfAdjoint D)
    (B : ℝ) (hB : 0 < B) (hDB : ‖D‖ ≤ B) (d : ℕ) :
    0 ≤ lvFilter D (B ^ 2)⁻¹ d ∧
      lvFilter D (B ^ 2)⁻¹ d ≤ 1 ∧ ‖lvFilter D (B ^ 2)⁻¹ d‖ ≤ 1 := by
  have hc : 0 ≤ (B ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg B)
  have hcD : (B ^ 2)⁻¹ * ‖D‖ ^ 2 ≤ 1 := by
    calc
      (B ^ 2)⁻¹ * ‖D‖ ^ 2 ≤ (B ^ 2)⁻¹ * B ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg D) hDB 2) hc
      _ = 1 := inv_mul_cancel₀ (ne_of_gt (sq_pos_of_pos hB))
  obtain ⟨h0, h1⟩ := lvFilter_order D hD _ hc hcD d
  exact ⟨h0, h1, lvFilter_norm_le_one D hD _ hc hcD d⟩

#print axioms lvFilter_order
#print axioms lvFilter_norm_le_one
#print axioms lvFilter_normalized_order

end QuantitativeMaass
