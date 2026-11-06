module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs

set_option autoImplicit false

public section

namespace FinitenessWeightedIndependence

variable {I K : Type*} [Field K]

theorem independent (f : I → ℕ → K) (w : ℕ → K)
    (hf : LinearIndependent K f) (hzero : ∀ i, f i 0=0)
    (hw : ∀ n, n ≠ 0 → w n ≠ 0) :
    LinearIndependent K (fun i n => f i n*w n) := by
  rw [linearIndependent_iff'] at hf ⊢
  intro s c hc
  apply hf s c
  funext n
  by_cases hn : n=0
  · subst n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hzero, mul_zero,
      Finset.sum_const_zero, Pi.zero_apply]
  · have hh := congrFun hc n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hh ⊢
    have he : (∑ i ∈ s, c i*f i n)*w n=0 := by
      simpa only [Finset.sum_mul, mul_assoc] using hh
    exact (mul_eq_zero.mp he).resolve_right (hw n hn)

#print axioms independent

end FinitenessWeightedIndependence
