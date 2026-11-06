module

public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointBarrier

/-- The scalar error envelope used by the present collective log-determinant
argument, even after granting the endpoint prime-product estimate. Here
s=log X and m=log(1/lambda). This is not the actual counting error. -/
def envelope (s m : ℝ) : ℝ := 1/s+s/m

/-- The existing envelope has a square-root floor. This is an obstruction
to optimizing that upper bound, not a lower bound on the Euler count. -/
theorem envelope_floor {s m : ℝ} (hs : 0<s) (hm : 0<m) :
    4 ≤ m * (envelope s m)^2 := by
  unfold envelope
  have hid : m * (1/s+s/m)^2 - 4 = (s^2-m)^2/(s^2*m) := by
    field_simp
    ring
  have hn : 0 ≤ (s^2-m)^2/(s^2*m) := by positivity
  linarith

/-- An endpoint 1/L bound from this envelope would require a quadratic,
not linear, budget in L for log(1/lambda). -/
theorem endpoint_requires_quadratic_budget {s m L A : ℝ}
    (hs : 0<s) (hm : 0<m) (hL : 0<L)
    (h : envelope s m ≤ A/L) : 4*L^2 ≤ A^2*m := by
  have he : 0 ≤ envelope s m := by unfold envelope; positivity
  have hmul : L * envelope s m ≤ A := by
    simpa only [mul_comm] using (le_div_iff₀ hL).mp h
  have hsq : (L * envelope s m)^2 ≤ A^2 :=
    pow_le_pow_left₀ (mul_nonneg hL.le he) hmul 2
  have hscaled := mul_le_mul_of_nonneg_right hsq hm.le
  have hfloor := mul_le_mul_of_nonneg_left (envelope_floor hs hm) (sq_nonneg L)
  nlinarith

/-- With the current linear transfer budget m<=C*L, the envelope cannot
obey A/L once L>A^2*C/4, whatever prime cutoff is chosen. -/
theorem linear_budget_obstruction {s m L A C : ℝ}
    (hs : 0<s) (hm : 0<m) (hL : 0<L)
    (hbudget : m≤C*L) (h : envelope s m≤A/L) : 4*L≤A^2*C := by
  have hq := endpoint_requires_quadratic_budget hs hm hL h
  have hb := mul_le_mul_of_nonneg_left hbudget (sq_nonneg A)
  nlinarith

#print axioms envelope_floor
#print axioms endpoint_requires_quadratic_budget
#print axioms linear_budget_obstruction

end QuantitativeEulerEndpointBarrier
