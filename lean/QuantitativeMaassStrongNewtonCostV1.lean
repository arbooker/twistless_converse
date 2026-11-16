module

public import QuantitativeMaassNewtonCostV1
public import QuantitativeMaassStrongNewtonScheduleV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
open Filter
open scoped Topology
namespace QuantitativeMaass.Strong

/-- The entire proved normalization perturbation cost is absorbed by a
single one of the available weighted exceptional estimates. -/
theorem bandNewtonDepth_weighted_cost :
    ∀ᶠ t in atTop,
      2*((6:ℝ)^(2*(4^(bandNewtonDepth t)))+
        10*((3^(bandNewtonDepth t):ℕ):ℝ)*(9:ℝ)^(2*(4^(bandNewtonDepth t))))≤
      Real.exp ((2*Real.log 5346)*strongScale t) := by
  filter_upwards [bandNewtonDepth_cost_bound] with t ht
  apply (compressedNewton_cost_bound (bandNewtonDepth t)).trans
  have he : (5346:ℝ)^(4^(bandNewtonDepth t))=
      Real.exp (((4^(bandNewtonDepth t):ℕ):ℝ)*Real.log 5346) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<5346)]
  rw [he]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right ht (Real.log_nonneg (by norm_num : (1:ℝ)≤5346))
  push_cast
  nlinarith only [hh]

#print axioms bandNewtonDepth_weighted_cost
end QuantitativeMaass.Strong
