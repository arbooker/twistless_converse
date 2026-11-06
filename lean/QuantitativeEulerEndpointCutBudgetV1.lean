module

public import QuantitativeEulerEndpointPrimeChainV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared

/-- The prime-dependent cut pays at most one extra factor 2q in the
reciprocal threshold; this is a scalar cost, not a filter-degree bound. -/
theorem primeCut_lower (c : ℝ) (hc : 0<c) (q : ℕ) [Fact q.Prime] :
    c/(2*(q : ℝ))≤primeCut c q := by
  have hq : 1<(q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).one_lt
  have hden : 0<2*(q : ℝ)*((q : ℝ)-1) := by positivity
  have hcmp : 2*(q : ℝ)*((q : ℝ)-1)≤4*(q : ℝ)^2 := by nlinarith
  have hsq := div_le_div_of_nonneg_left (sq_nonneg c) hden hcmp
  have hleft : (c/(2*(q : ℝ)))^2=c^2/(4*(q : ℝ)^2) := by ring
  have hright : (primeCut c q)^2=c^2/(2*(q : ℝ)*((q : ℝ)-1)) := by
    rw [primeCut_sq,Nat.cast_sub (Fact.out : q.Prime).one_lt.le,Nat.cast_one]
    field_simp
  rw [←hleft,←hright] at hsq
  have hp := primeCut_pos c hc q
  nlinarith only [hsq,hp,div_nonneg hc.le (by positivity : (0 : ℝ)≤2*q)]

theorem primeCut_inverse_le (c : ℝ) (hc : 0<c) (q : ℕ) [Fact q.Prime] :
    (primeCut c q)⁻¹≤2*(q : ℝ)*c⁻¹ := by
  have hq : 0<(q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).pos
  have hh := (inv_le_inv₀ (primeCut_pos c hc q) (by positivity : 0<c/(2*(q : ℝ)))).mpr
    (primeCut_lower c hc q)
  simpa only [div_eq_mul_inv,mul_inv_rev,inv_inv] using hh

#print axioms primeCut_lower
#print axioms primeCut_inverse_le
end QuantitativeEulerEndpointPrepared
