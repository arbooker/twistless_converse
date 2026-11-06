module

public import QuantitativeEulerEndpointInitialEffortV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointInitialPower
open Polynomial

theorem composed_degree (z : ℝ[X]) (n : ℕ) :
    (z.comp (powerPolynomial n)).natDegree≤z.natDegree*n :=
  (natDegree_comp_le).trans (Nat.mul_le_mul_left _ (powerPolynomial_degree n))

theorem composed_coeff_bound (z : ℝ[X]) (n k : ℕ) :
    |(z.comp (powerPolynomial n)).coeff k|≤
      (∑ i∈z.support, |z.coeff i|)*2^(n*z.natDegree) := by
  rw [comp_eq_sum_left]
  change |(∑ i∈z.support, C (z.coeff i)*(powerPolynomial n)^i).coeff k|≤_
  rw [finsetSum_coeff]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hh (i : ℕ) (hi : i∈z.support) :
      |(C (z.coeff i)*(powerPolynomial n)^i).coeff k|≤|z.coeff i| *2^(n*z.natDegree) := by
    rw [coeff_C_mul,abs_mul,powerPolynomial,← pow_mul]
    have hp : (2:ℝ)^(n*i)≤2^(n*z.natDegree) :=
      pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left n (le_natDegree_of_ne_zero (mem_support_iff.mp hi)))
    exact mul_le_mul_of_nonneg_left
      ((QuantitativeEulerEndpointBernstein.one_sub_X_coeff_bound (n*i) k).trans hp) (abs_nonneg _)
  exact (Finset.sum_le_sum hh).trans_eq (Finset.sum_mul ..).symm

theorem composed_mass (z : ℝ[X]) (n : ℕ) :
    (∑ k∈(z.comp (powerPolynomial n)).support, |(z.comp (powerPolynomial n)).coeff k|)≤
      (((z.natDegree*n:ℕ):ℝ)+1)*(∑ i∈z.support, |z.coeff i|)*2^(n*z.natDegree) := by
  have hs : (z.comp (powerPolynomial n)).support⊆Finset.range (z.natDegree*n+1) := by
    intro k hk
    have hh := (le_natDegree_of_ne_zero (mem_support_iff.mp hk)).trans (composed_degree z n)
    exact Finset.mem_range.mpr (by omega)
  apply (Finset.sum_le_sum_of_subset_of_nonneg hs (fun k _ _ => abs_nonneg _)).trans
  apply (Finset.sum_le_sum (fun k _ => composed_coeff_bound z n k)).trans_eq
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  ring

#print axioms composed_degree
#print axioms composed_coeff_bound
#print axioms composed_mass
end QuantitativeEulerEndpointInitialPower
