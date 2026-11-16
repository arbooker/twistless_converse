module

public import QuantitativeMaassTestPowerBoundsV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

theorem positiveTestPower_pointwise_bound (φ : PositiveSmoothTest) (R : ℝ)
    (hR : ∀ t∈tsupport φ,‖t‖≤R) (n : ℕ) (t : ℝ) :
    ‖positiveTestPower n φ t‖≤‖φ t‖*R^n := by
  rw [positiveTestPower_apply,norm_mul,norm_pow]
  by_cases hz : φ t=0
  · simp only [hz,norm_zero,zero_mul,le_refl]
  · exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hR t (subset_tsupport _ hz)) n) (norm_nonneg _)

/-- A common support radius gives an L1 bound for every polynomial moment
with the same base test's L1 mass. -/
theorem positiveTestPower_L1_bound (φ : PositiveSmoothTest) (R : ℝ)
    (hR : ∀ t∈tsupport φ,‖t‖≤R) (n : ℕ) :
    (∫ t,‖positiveTestPower n φ t‖)≤(∫ t,‖φ t‖)*R^n := by
  have hp : Integrable (positiveTestPower n φ : ℝ → ℝ) :=
    (positiveTestPower n φ).continuous.integrable_of_hasCompactSupport (positiveTestPower n φ).hasCompactSupport
  have hφ : Integrable (φ : ℝ → ℝ) := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  calc
    _ ≤ ∫ t,‖φ t‖*R^n := integral_mono hp.norm (hφ.norm.mul_const _) (positiveTestPower_pointwise_bound φ R hR n)
    _ = _ := integral_mul_const _ _

theorem positiveSmoothTest_radius (φ : PositiveSmoothTest) :
    ∃ R : ℝ,0≤R ∧ ∀ t∈tsupport φ,‖t‖≤R := by
  let I := positiveSmoothTestInterval φ
  refine ⟨I.right,I.right_nonneg,?_⟩
  intro t ht
  rw [Real.norm_eq_abs,abs_of_nonneg (I.left_pos.le.trans (I.subset ht).1)]
  exact (I.subset ht).2

#print axioms positiveTestPower_L1_bound
#print axioms positiveSmoothTest_radius

end QuantitativeMaass
