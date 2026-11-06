module

public import QuantitativeSpectralDistributionV1

set_option autoImplicit false
@[expose] public section

namespace QuantitativeSpectralLogError

/-- Removing a positive regularization at twice its size costs only a
logarithmic error beyond the surviving trace. The formula retains boundary
mass and does not suppress the factor two introduced by translation. -/
theorem log_quotient_le_survivor {area p h eps K : ℝ}
    (hp : 0 ≤ p) (hpa : p ≤ area) (hh : 0 < h) (heps : 0 < eps)
    (hK : 0 < K) (hhK : h ≤ K) (hcut : 2*eps < K) :
    (area*Real.log K - (p*Real.log eps+(area-p)*Real.log h)) /
        Real.log (K/(2*eps)) ≤
      p + area*Real.log (2*K/h)/Real.log (K/(2*eps)) := by
  have hd : 0 < Real.log (K/(2*eps)) :=
    Real.log_pos ((one_lt_div (mul_pos (by norm_num) heps)).mpr hcut)
  have hklog : 0 ≤ Real.log (K/h) := Real.log_nonneg ((one_le_div hh).mpr hhK)
  have hlog2 : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have he : (area*Real.log K - (p*Real.log eps+(area-p)*Real.log h)) /
      Real.log (K/(2*eps)) =
      p + ((area-p)*Real.log (K/h)+p*Real.log 2)/Real.log (K/(2*eps)) := by
    apply (div_eq_iff hd.ne').mpr
    rw [add_mul, div_mul_cancel₀ _ hd.ne']
    rw [Real.log_div hK.ne' hh.ne', Real.log_div hK.ne' (mul_ne_zero (by norm_num) heps.ne'),
      Real.log_mul (by norm_num : (2:ℝ)≠0) heps.ne']
    ring
  have hn : (area-p)*Real.log (K/h)+p*Real.log 2 ≤ area*Real.log (2*K/h) := by
    have hleft := mul_le_mul_of_nonneg_right (show area-p ≤ area by linarith) hklog
    have hright := mul_le_mul_of_nonneg_right hpa hlog2
    have heq : Real.log (2*K/h) = Real.log (K/h)+Real.log 2 := by
      rw [Real.log_div (mul_ne_zero (by norm_num) hK.ne') hh.ne',
        Real.log_mul (by norm_num : (2:ℝ)≠0) hK.ne', Real.log_div hK.ne' hh.ne']
      ring
    rw [heq, mul_add]
    exact add_le_add hleft hright
  rw [he]
  exact add_le_add le_rfl (div_le_div_of_nonneg_right hn hd.le)

#print axioms log_quotient_le_survivor

end QuantitativeSpectralLogError
