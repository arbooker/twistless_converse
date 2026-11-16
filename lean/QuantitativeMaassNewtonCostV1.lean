module

public import QuantitativeMaassNewtonScheduleV1
public import QuantitativeMaassCompressedNewtonEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Filter
open scoped Topology

namespace QuantitativeMaass

theorem compressedNewton_cost_bound (n : ℕ) :
    2*((6:ℝ)^(2*(4^n))+10*((3^n:ℕ):ℝ)*(9:ℝ)^(2*(4^n)))≤
      (5346:ℝ)^(4^n) := by
  have hk : 1≤4^n := Nat.one_le_pow n 4 (by norm_num)
  have hn : n≤4^n := (Nat.lt_pow_self (by norm_num : 1<(4:ℕ))).le
  have hthree : 1≤(3:ℝ)^n := one_le_pow₀ (by norm_num)
  have hsix : (6:ℝ)^(2*(4^n))≤(3:ℝ)^n*(9:ℝ)^(2*(4^n)) :=
    (pow_le_pow_left₀ (by norm_num) (by norm_num : (6:ℝ)≤9) _).trans
      (le_mul_of_one_le_left (by positivity) hthree)
  have h22 : (22:ℝ)≤22^(4^n) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤22) hk
  have h3 : (3:ℝ)^n≤3^(4^n) := pow_le_pow_right₀ (by norm_num) hn
  push_cast
  calc
    _ ≤ 22*((3:ℝ)^n*(9:ℝ)^(2*(4^n))) := by nlinarith only [hsix]
    _ ≤ 22^(4^n)*((3:ℝ)^(4^n)*(9:ℝ)^(2*(4^n))) := by
      apply mul_le_mul h22 _ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = _ := by
      rw [pow_mul,←mul_pow,←mul_pow]
      norm_num

/-- The entire proved normalization perturbation cost is absorbed by a
single one of the available weighted exceptional estimates. -/
theorem bandNewtonDepth_weighted_cost :
    ∀ᶠ t in atTop,
      2*((6:ℝ)^(2*(4^(bandNewtonDepth t)))+
        10*((3^(bandNewtonDepth t):ℕ):ℝ)*(9:ℝ)^(2*(4^(bandNewtonDepth t))))≤
      Real.exp ((2*Real.log 5346)*fourthRootScale t) := by
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

#print axioms compressedNewton_cost_bound
#print axioms bandNewtonDepth_weighted_cost

end QuantitativeMaass
