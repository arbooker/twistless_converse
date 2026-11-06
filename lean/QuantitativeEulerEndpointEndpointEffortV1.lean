module

public import QuantitativeEulerEndpointLocalEffortV1

set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointLocalEffort
open Finset

/-- The last update uses the NEXT effort for its sharpening; this term
must be paid in addition to the sum over j<n. -/
theorem endpoint_effort_bound (n : ℕ) {M Q : ℝ} (hQ : 0≤Q)
    (hM : M≤Q*((4:ℝ)^n+n+1)) : effort n n M≤(1+2*Q)*(4:ℝ)^n := by
  have hn2 : ((n+1:ℕ):ℝ)≤(2:ℝ)^n := by
    exact_mod_cast Nat.succ_le_of_lt (show n<2^n from Nat.lt_two_pow_self)
  have hn : (n:ℝ)+1≤(4:ℝ)^n := by
    push_cast at hn2
    exact hn2.trans (pow_le_pow_left₀ (by norm_num) (by norm_num) n)
  have hh := mul_le_mul_of_nonneg_left hn hQ
  simp only [effort,Nat.sub_self,pow_zero,mul_one]
  nlinarith only [hM,hh]

theorem effort_sum_with_endpoint (n : ℕ) (M : ℕ → ℝ) {Q : ℝ}
    (hQ : 0≤Q) (hM : ∀ j, j≤n → M j≤Q*((4:ℝ)^j+n+1)) :
    (∑ j∈range n, effort n j (M j))+effort n n (M n)≤(2+5*Q)*(4:ℝ)^n := by
  have hsum := effort_sum_linear_overhead n M hQ (fun j hj => by
    simpa only [Nat.cast_add,Nat.cast_one,←add_assoc] using hM j hj.le)
  have hend := endpoint_effort_bound n hQ (hM n le_rfl)
  linarith

#print axioms endpoint_effort_bound
#print axioms effort_sum_with_endpoint
end QuantitativeEulerEndpointLocalEffort
