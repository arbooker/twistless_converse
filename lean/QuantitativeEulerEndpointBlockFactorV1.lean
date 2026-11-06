module

public import QuantitativeEulerEndpointBlockArithmeticV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBlocks
open Finset QuantitativeEulerEndpointAP QuantitativeHolomorphic
attribute [local instance] Classical.propDecidable

/-- A block loses at most exp(exceptional reciprocal mass) relative to its
full-prime contraction. This is the multiplicative loss used in block iteration. -/
theorem detecting_block_product_le (P : ℕ → Prop) (s : Finset ℕ)
    (hp : ∀ p ∈ s, p.Prime) :
    (∏ p ∈ s.filter P, (1-(p : ℝ)⁻¹))≤
      (∏ p ∈ s, (1-(p : ℝ)⁻¹))*Real.exp (∑ p ∈ s, badPrimeLoss P p) := by
  let f : ℕ → ℝ := fun p => 1-(p : ℝ)⁻¹
  let bad := s.filter (fun p => ¬P p)
  have hf (p : ℕ) (h : p∈s) : 0<f p := by
    apply sub_pos.mpr
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (hp p h).one_lt)
  have hpos : 0<∏ p ∈ bad, (f p)⁻¹ :=
    prod_pos (fun p h => inv_pos.mpr (hf p (mem_filter.mp h).1))
  have he : (∑ p ∈ bad, 1/((p : ℝ)-1))=∑ p ∈ s, badPrimeLoss P p := by
    rw [show bad=s.filter (fun p => ¬P p) from rfl,sum_filter]
    apply sum_congr rfl
    intro p h
    simp only [badPrimeLoss,hp p h,true_and]
  have hb : (∏ p ∈ bad, (f p)⁻¹)≤Real.exp (∑ p ∈ s, badPrimeLoss P p) := by
    rw [← Real.exp_log hpos]
    apply Real.exp_le_exp.mpr
    exact (log_prime_euler_product_le_loss bad
      (fun p h => hp p (mem_filter.mp h).1)).trans_eq he
  have hcancel : (∏ p ∈ bad, f p)*(∏ p ∈ bad, (f p)⁻¹)=1 := by
    rw [← prod_mul_distrib]
    apply prod_eq_one
    intro p h
    exact mul_inv_cancel₀ (hf p (mem_filter.mp h).1).ne'
  have hsplit : (∏ p ∈ s, f p)=
      (∏ p ∈ s.filter P, f p)*(∏ p ∈ bad, f p) :=
    (prod_filter_mul_prod_filter_not s P f).symm
  change (∏ p ∈ s.filter P, f p)≤(∏ p ∈ s, f p)*_
  calc
    _ = (∏ p ∈ s, f p)*(∏ p ∈ bad, (f p)⁻¹) := by
      rw [hsplit,mul_assoc,hcancel,mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (prod_nonneg (fun p h => (hf p h).le))

/-- A full-prime block contracting by R^-1 still contracts by at most
exp(blockLoss)/R after non-detecting primes are omitted. -/
theorem detecting_block_contraction (P : ℕ → Prop) (blocks : ℕ → Finset ℕ) (j : ℕ)
    (hp : ∀ p ∈ blocks j, p.Prime) {R : ℝ}
    (hfull : (∏ p ∈ blocks j, (1-(p : ℝ)⁻¹))≤1/R) :
    (∏ p ∈ (blocks j).filter P, (1-(p : ℝ)⁻¹))≤Real.exp (blockLoss P blocks j)/R := by
  have h := detecting_block_product_le P (blocks j) hp
  have hm := mul_le_mul_of_nonneg_right hfull (Real.exp_pos (blockLoss P blocks j)).le
  exact h.trans (hm.trans_eq (by ring))

#print axioms detecting_block_product_le
#print axioms detecting_block_contraction
end QuantitativeEulerEndpointBlocks
