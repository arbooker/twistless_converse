module

public import QuantitativeEulerEndpointExponentialCostsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointNestedExpression
open Polynomial Finset QuantitativeEulerEndpointExponentialParameters

def scheduleConstant (D : ℝ) : ℝ :=
  Real.log 8+Real.log 18+5*Real.log (280*D+3)+Real.log 34

theorem scheduleConstant_nonneg {D : ℝ} (hD : 0≤D) : 0≤scheduleConstant D := by
  unfold scheduleConstant
  have h := Real.log_nonneg (show 1≤280*D+3 by linarith)
  have h8 := Real.log_nonneg (by norm_num : (1:ℝ)≤8)
  have h18 := Real.log_nonneg (by norm_num : (1:ℝ)≤18)
  have h34 := Real.log_nonneg (by norm_num : (1:ℝ)≤34)
  linarith

theorem scheduled_cost_sum (n : ℕ) (E : ℕ → ℝ) (q : ℕ → ℝ[X]) {D : ℝ}
    (hD : 0≤D) (hE : ∀ j, j≤n → 0≤E j)
    (hq : ∀ j, j<n → (q j).natDegree≤16*(sharpness D (E (j+1)))^5+1) :
    (∑ j∈range n,logarithmicCost (fun i => power (E i)) q j)≤
      scheduleConstant D*n+17*((∑ j∈range n,E j)+E n) := by
  have hs : (∑ j∈range n,E (j+1))≤(∑ j∈range n,E j)+E n := by
    have h := sum_range_succ' E n
    rw [sum_range_succ] at h
    linarith [hE 0 (Nat.zero_le n)]
  have htotal : 0≤∑ j∈range n,E j := sum_nonneg (fun j hj => hE j (mem_range.mp hj).le)
  have hterm := sum_le_sum (s:=range n) (fun j hj => scheduled_logarithmic_cost hD
    (hE j (mem_range.mp hj).le) (hE (j+1) (mem_range.mp hj)) (q j) (hq j (mem_range.mp hj)))
  change (∑ j∈range n,logarithmicCost (fun i => power (E i)) q j)≤
    ∑ j∈range n, (scheduleConstant D+15*E (j+1)+2*E j) at hterm
  simp only [sum_add_distrib,←mul_sum,sum_const,card_range,nsmul_eq_mul] at hterm
  nlinarith [hE n le_rfl]

theorem scheduled_cost_geometric (n : ℕ) (E : ℕ → ℝ) (q : ℕ → ℝ[X]) {D Q : ℝ}
    (hD : 0≤D) (hE : ∀ j, j≤n → 0≤E j)
    (hq : ∀ j, j<n → (q j).natDegree≤16*(sharpness D (E (j+1)))^5+1)
    (hbudget : (∑ j∈range n,E j)+E n≤Q*(4:ℝ)^n) :
    (∑ j∈range n,logarithmicCost (fun i => power (E i)) q j)≤
      (scheduleConstant D+17*Q)*(4:ℝ)^n := by
  have hn2 : (n:ℝ)≤(2:ℝ)^n := by exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le
  have hn : (n:ℝ)≤(4:ℝ)^n := hn2.trans (pow_le_pow_left₀ (by norm_num) (by norm_num) n)
  have hc := mul_le_mul_of_nonneg_left hn (scheduleConstant_nonneg hD)
  have hs := scheduled_cost_sum n E q hD hE hq
  nlinarith

#print axioms scheduled_cost_sum
#print axioms scheduled_cost_geometric
end QuantitativeEulerEndpointNestedExpression
