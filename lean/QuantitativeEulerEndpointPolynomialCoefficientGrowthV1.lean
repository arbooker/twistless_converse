module

public import QuantitativeEulerEndpointExponentialCostsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPolynomialGrowth
open Polynomial

theorem two_power_le (d : ℕ) : (2:ℝ)^d≤Real.exp (d:ℝ) := by
  have h : (2:ℝ)≤Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) h d
  simpa only [←Real.exp_nat_mul,mul_one] using hh

theorem three_power_le (d : ℕ) : (3:ℝ)^d≤Real.exp (2*(d:ℝ)) := by
  have h : (3:ℝ)≤Real.exp 2 := by linarith [Real.add_one_le_exp (2:ℝ)]
  have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) h d
  simpa only [←Real.exp_nat_mul,mul_comm (d:ℝ) 2] using hh

theorem coefficient_envelope (d h : ℕ) :
    ((d:ℝ)+1)*(((h:ℝ)+2)*3^h)*2^d≤Real.exp (2*(d:ℝ)+3*(h:ℝ)+1) := by
  have hd : (d:ℝ)+1≤Real.exp (d:ℝ) := Real.add_one_le_exp _
  have hh : (h:ℝ)+2≤Real.exp ((h:ℝ)+1) := by linarith [Real.add_one_le_exp ((h:ℝ)+1)]
  have hp := mul_le_mul hh (three_power_le h) (by positivity : (0:ℝ)≤3^h) (Real.exp_pos _).le
  have hq := mul_le_mul (mul_le_mul hd hp (by positivity) (Real.exp_pos _).le)
    (two_power_le d) (by positivity) (by positivity)
  apply hq.trans_eq
  rw [←Real.exp_add,←Real.exp_add,←Real.exp_add]
  congr 1
  ring

/-- The coefficient bound from the actual initial sharpening theorem has
an exponential envelope polynomial in J and m. -/
theorem initial_coefficient_bound (J m : ℕ) :
    ((((16*J^5+1)*(2*m):ℕ):ℝ)+1)*((((16*J^5:ℕ):ℝ)+2)*3^(16*J^5))*2^((2*m)*(16*J^5+1))≤
      Real.exp (119*((J:ℝ)+1)^5*((m:ℝ)+1)) := by
  have h := coefficient_envelope ((16*J^5+1)*(2*m)) (16*J^5)
  rw [Nat.mul_comm (2*m) (16*J^5+1)]
  apply h.trans
  apply Real.exp_le_exp.mpr
  push_cast
  have hJ : (J:ℝ)^5≤((J:ℝ)+1)^5 := pow_le_pow_left₀ (by positivity) (by linarith) 5
  have hJ1 : (1:ℝ)≤((J:ℝ)+1)^5 := one_le_pow₀ (by have hh : (0:ℝ)≤J := Nat.cast_nonneg _; linarith)
  have hm := mul_le_mul_of_nonneg_right hJ (Nat.cast_nonneg m : (0:ℝ)≤m)
  nlinarith [show (0:ℝ)≤m from Nat.cast_nonneg m]

theorem initial_degree_bound (J m : ℕ) :
    (((16*J^5+1)*(2*m):ℕ):ℝ)≤34*((J:ℝ)+1)^5*((m:ℝ)+1) := by
  push_cast
  have hJ : (J:ℝ)^5≤((J:ℝ)+1)^5 := pow_le_pow_left₀ (by positivity) (by linarith) 5
  have hJ1 : (1:ℝ)≤((J:ℝ)+1)^5 := one_le_pow₀ (by have hh : (0:ℝ)≤J := Nat.cast_nonneg _; linarith)
  have hm := mul_le_mul_of_nonneg_right hJ (Nat.cast_nonneg m : (0:ℝ)≤m)
  nlinarith [show (0:ℝ)≤m from Nat.cast_nonneg m]

#print axioms coefficient_envelope
#print axioms initial_coefficient_bound
#print axioms initial_degree_bound
end QuantitativeEulerEndpointPolynomialGrowth
