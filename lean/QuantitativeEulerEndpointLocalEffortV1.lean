module

public import QuantitativeEulerEndpointBlockScheduleV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointLocalEffort
open Finset QuantitativeEulerEndpointBlocks

/-- Threshold cost is paid at the block's own geometric scale. The extra
common height cost is not charged at the final worst-case scale each time. -/
def effort (n j : ℕ) (M : ℝ) : ℝ := ((4:ℝ)^j+M)*(2:ℝ)^(n-j)

theorem geometric_identity (n j : ℕ) (hj : j≤n) :
    (4:ℝ)^j*(2:ℝ)^(n-j)=(2:ℝ)^(n+j) := by
  have hp : (4:ℝ)^j=(2:ℝ)^(2*j) := by rw [pow_mul]; norm_num
  rw [hp,←pow_add]
  congr 1
  omega

theorem effort_lower (n j : ℕ) (hj : j≤n) {M : ℝ} (hM : 0≤M) :
    blockEffort n j≤effort n j M := by
  unfold effort blockEffort
  rw [←geometric_identity n j hj]
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

theorem effort_pos (n j : ℕ) {M : ℝ} (hM : 0≤M) : 0<effort n j M := by
  unfold effort
  positivity

theorem effort_one_le (n j : ℕ) {M : ℝ} (hM : 0≤M) : 1≤effort n j M := by
  have h4 : (1:ℝ)≤4^j := one_le_pow₀ (by norm_num)
  have h2 : (1:ℝ)≤2^(n-j) := one_le_pow₀ (by norm_num)
  unfold effort
  nlinarith

theorem effort_ratio (n j : ℕ) (hj : j≤n) {M : ℝ} (hM : 0≤M) :
    M/effort n j M≤blockRelativeLoss n j := by
  apply (div_le_iff₀ (effort_pos n j hM)).mpr
  have hid : blockRelativeLoss n j*effort n j M=(4:ℝ)^j+M := by
    unfold blockRelativeLoss effort
    have hpow : (2:ℝ)^n=(2:ℝ)^j*(2:ℝ)^(n-j) := by rw [←pow_add]; congr 1; omega
    rw [hpow]
    field_simp
  rw [hid]
  linarith [pow_nonneg (by norm_num : (0:ℝ)≤4) j]

theorem effort_inverse (n j : ℕ) (hj : j≤n) {M : ℝ} (hM : 0≤M) :
    1/effort n j M≤blockAdditiveLoss n j :=
  one_div_le_one_div_of_le (blockEffort_pos n j) (effort_lower n j hj hM)

theorem sum_reverse_two_powers (n : ℕ) :
    (∑ j∈range n, (2:ℝ)^(n-j))=2*((2:ℝ)^n-1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have hh : (∑ j∈range n, (2:ℝ)^(n+1-j))=2*∑ j∈range n, (2:ℝ)^(n-j) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      have hn : n+1-j=(n-j)+1 := by have := mem_range.mp hj; omega
      rw [hn,pow_succ,mul_comm]
    rw [hh,ih]
    simp only [Nat.add_sub_cancel_left,pow_succ]
    ring

theorem effort_sum_bound (n : ℕ) (M : ℕ → ℝ) {Q T : ℝ}
    (hQ : 0≤Q) (hT : 0≤T) (hM : ∀ j, j<n → M j≤Q*(4:ℝ)^j+T) :
    (∑ j∈range n, effort n j (M j))≤(1+Q)*(4:ℝ)^n+2*T*(2:ℝ)^n := by
  have hterm (j : ℕ) (hj : j<n) : effort n j (M j)≤
      (1+Q)*blockEffort n j+T*(2:ℝ)^(n-j) := by
    have hh := mul_le_mul_of_nonneg_right (hM j hj) (show 0≤(2:ℝ)^(n-j) by positivity)
    have he := geometric_identity n j hj.le
    unfold effort blockEffort
    rw [←he]
    nlinarith only [hh]
  calc
    _ ≤ ∑ j∈range n, ((1+Q)*blockEffort n j+T*(2:ℝ)^(n-j)) := sum_le_sum (fun j hj => hterm j (mem_range.mp hj))
    _ = (1+Q)*(∑ j∈range n, blockEffort n j)+T*(2*((2:ℝ)^n-1)) := by
      rw [sum_add_distrib,←mul_sum,←mul_sum,sum_reverse_two_powers]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (blockEffort_total_le n) (show 0≤1+Q by positivity)
      nlinarith only [hh,hT]

/-- A logarithmic common-height overhead T=O(n+1) still costs O(4^n)
over the entire finite horizon. -/
theorem effort_sum_linear_overhead (n : ℕ) (M : ℕ → ℝ) {Q : ℝ}
    (hQ : 0≤Q) (hM : ∀ j, j<n → M j≤Q*((4:ℝ)^j+(n+1:ℕ))) :
    (∑ j∈range n, effort n j (M j))≤(1+3*Q)*(4:ℝ)^n := by
  have hb := effort_sum_bound n M hQ (show 0≤Q*(n+1:ℕ) by positivity)
    (fun j hj => by simpa only [mul_add] using hM j hj)
  have hn : ((n+1:ℕ):ℝ)≤(2:ℝ)^n := by exact_mod_cast Nat.succ_le_of_lt (show n<2^n from Nat.lt_two_pow_self)
  have hp : (2:ℝ)^n*(2:ℝ)^n=(4:ℝ)^n := by rw [←mul_pow]; norm_num
  have hm := mul_le_mul_of_nonneg_left hn (show 0≤2*Q*(2:ℝ)^n by positivity)
  have hm' : 2*(Q*((n+1:ℕ):ℝ))*(2:ℝ)^n≤2*Q*(4:ℝ)^n := by
    calc
      _ = 2*Q*(2:ℝ)^n*((n+1:ℕ):ℝ) := by ring
      _ ≤ 2*Q*(2:ℝ)^n*(2:ℝ)^n := hm
      _ = _ := by rw [mul_assoc (2*Q),hp]
  nlinarith only [hb,hm']

#print axioms effort_ratio
#print axioms effort_inverse
#print axioms effort_sum_bound
#print axioms effort_sum_linear_overhead
end QuantitativeEulerEndpointLocalEffort
