module

public import QuantitativeMaassLowRankFilterV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Module

namespace QuantitativeMaass

/-- A nonnegative polynomial filter that equals one at zero always
majorizes the exact kernel dimension in trace. -/
theorem half_filter_trace_kernel_lower {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (S : E →ₗ[ℂ] E) (hS : S.IsSymmetric)
    (heig : ∀ i,hS.eigenvalues rfl i≤2) (m : ℕ) :
    (finrank ℂ S.ker:ℝ)≤(LinearMap.trace ℂ E ((1-(1/2:ℂ) • S)^m)).re := by
  classical
  have ht : (LinearMap.trace ℂ E ((1-(1/2:ℂ) • S)^m)).re=
      ∑ i : Fin (finrank ℂ E),(1-hS.eigenvalues rfl i/2)^m := by
    simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,div_mul_eq_mul_div,one_mul]
      using symmetric_affine_power_trace S hS (1/2) m
  have hk : (Finset.univ.filter (fun i : Fin (finrank ℂ E) => hS.eigenvalues rfl i=0)).card=
      finrank ℂ S.ker := by
    have hh := hS.card_filter_eigenvalues_eq rfl (0:ℂ)
    rw [Module.End.eigenspace_zero] at hh
    simpa using hh
  have hp (i : Fin (finrank ℂ E)) :
      (if hS.eigenvalues rfl i=0 then (1:ℝ) else 0)≤(1-hS.eigenvalues rfl i/2)^m := by
    by_cases hz : hS.eigenvalues rfl i=0
    · simp [hz]
    · simp only [hz,ite_false]
      exact pow_nonneg (by linarith only [heig i]) _
  have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hp i)
  rw [ht]
  simpa [hk] using hh

#print axioms half_filter_trace_kernel_lower

end QuantitativeMaass
