module

public import QuantitativeEulerEndpointInitialActualV1
public import QuantitativeEulerEndpointSharpenCoefficientsV1
public import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointInitialPower
open Polynomial

theorem powerPolynomial_degree (n : ℕ) : (powerPolynomial n).natDegree≤n := by
  have hh : ((1:ℝ[X])-X).natDegree≤1 := by
    simpa only [natDegree_one,natDegree_X,Nat.zero_max] using natDegree_sub_le (1:ℝ[X]) X
  rw [powerPolynomial,natDegree_pow]
  simpa only [mul_one] using Nat.mul_le_mul_left n hh

theorem powerPolynomial_mass (n : ℕ) :
    (∑ i∈(powerPolynomial n).support, |(powerPolynomial n).coeff i|)≤((n:ℝ)+1)*2^n := by
  have hs : (powerPolynomial n).support⊆Finset.range (n+1) := by
    intro i hi
    have hh := (le_natDegree_of_ne_zero (mem_support_iff.mp hi)).trans (powerPolynomial_degree n)
    exact Finset.mem_range.mpr (by omega)
  apply (Finset.sum_le_sum_of_subset_of_nonneg hs (fun i _ _ => abs_nonneg _)).trans
  apply (Finset.sum_le_sum (fun i _ => QuantitativeEulerEndpointBernstein.one_sub_X_coeff_bound n i)).trans_eq
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]

end QuantitativeEulerEndpointInitialPower

namespace QuantitativeEulerEndpointInitialWeighted
variable {ι : Type*} [Fintype ι] (C a : ι → ℝ) (ha : ∀ i, 0<a i)

/-- Explicit finite initialization effort; all block detector caps are
combined before choosing this one degree. -/
def effort : ℕ := ⌈2*cap C a⌉₊

theorem effort_budget : 4*cap C a≤((2*effort C a:ℕ):ℝ)+1 := by
  have hh := Nat.le_ceil (2*cap C a)
  change 2*cap C a≤(effort C a:ℝ) at hh
  push_cast
  linarith

include ha in
theorem effort_degree : ((2*effort C a:ℕ):ℝ)≤4*cap C a+2 := by
  have hnonneg : (0:ℝ)≤2*cap C a := mul_nonneg (by norm_num) (cap_pos C a ha).le
  have hh := Nat.ceil_lt_add_one hnonneg
  change (effort C a:ℝ)<2*cap C a+1 at hh
  push_cast
  linarith

#print axioms QuantitativeEulerEndpointInitialPower.powerPolynomial_degree
#print axioms QuantitativeEulerEndpointInitialPower.powerPolynomial_mass
#print axioms effort_budget
#print axioms effort_degree
end QuantitativeEulerEndpointInitialWeighted
