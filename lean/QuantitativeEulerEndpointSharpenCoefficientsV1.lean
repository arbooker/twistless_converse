module

public import QuantitativeEulerEndpointSharpenOperatorV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBernstein
open Polynomial

/-- Elementary coefficient bound for the binomial expansion. -/
theorem one_sub_X_coeff_bound (n k : ℕ) :
    |(((1:ℝ[X])-X)^n).coeff k|≤(2:ℝ)^n := by
  induction n generalizing k with
  | zero =>
    simp only [pow_zero,coeff_one]
    split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ,mul_sub,mul_one,coeff_sub]
    apply (abs_sub _ _).trans
    cases k with
    | zero => simpa only [coeff_mul_X_zero,abs_zero,add_zero] using
        (ih 0).trans (by rw [pow_succ]; nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤2) n] : (2:ℝ)^n≤2^(n+1))
    | succ k =>
      rw [coeff_mul_X]
      have h := add_le_add (ih (k+1)) (ih k)
      simpa only [pow_succ] using h.trans_eq (by ring : (2:ℝ)^n+2^n=2^n*2)

theorem bernstein_coeff_bound (n k d : ℕ) :
    |(bernsteinPolynomial ℝ n k).coeff d| ≤ (n.choose k:ℝ)*2^(n-k) := by
  rw [bernsteinPolynomial,mul_assoc,coeff_natCast_mul]
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _),coeff_X_pow_mul']
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  split_ifs
  · exact one_sub_X_coeff_bound _ _
  · simp

theorem tail_coeff_bound (n : ℕ) (b : ℝ) (d : ℕ) : |(tail n b).coeff d|≤(3:ℝ)^n := by
  rw [tail,finsetSum_coeff]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun (k : Fin (n+1)) _ => bernstein_coeff_bound n k d)).trans
  have he : (∑ k : Fin (n+1), (n.choose k : ℝ)*2^(n-k))=(3:ℝ)^n := by
    calc
      _ = ∑ k∈Finset.range (n+1), (n.choose k:ℝ)*2^(n-k) :=
        Fin.sum_univ_eq_sum_range (fun k : ℕ => (n.choose k:ℝ)*2^(n-k)) (n+1)
      _ = (3:ℝ)^n := by
        simpa only [one_pow,one_mul,mul_comm,
          show (1:ℝ)+2=3 by norm_num] using (add_pow (1:ℝ) 2 n).symm
  rw [← he]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun k _ _ => by positivity)

theorem sharpen_coeff_bound (n : ℕ) (b : ℝ) (d : ℕ) :
    |(sharpen n b).coeff d|≤(3:ℝ)^n := by
  cases d with
  | zero => simp [sharpen]
  | succ d => simpa only [sharpen,coeff_X_mul] using tail_coeff_bound n b d

/-- Absolute coefficient mass grows at most exponentially in the explicit
degree. This is the quantity needed for later finite-word expansion. -/
theorem sharpen_coefficient_mass (n : ℕ) (b : ℝ) :
    (∑ d∈(sharpen n b).support, |(sharpen n b).coeff d|) ≤ ((n:ℝ)+2)*3^n := by
  have hs : (sharpen n b).support ⊆ Finset.range (n+2) := by
    intro d hd
    apply Finset.mem_range.mpr
    have h := (le_natDegree_of_ne_zero (mem_support_iff.mp hd)).trans (sharpen_natDegree_le n b)
    omega
  apply (Finset.sum_le_sum_of_subset_of_nonneg hs (fun d _ _ => abs_nonneg _)).trans
  apply (Finset.sum_le_sum (fun d _ => sharpen_coeff_bound n b d)).trans_eq
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat]

#print axioms one_sub_X_coeff_bound
#print axioms bernstein_coeff_bound
#print axioms tail_coeff_bound
#print axioms sharpen_coeff_bound
#print axioms sharpen_coefficient_mass
end QuantitativeEulerEndpointBernstein
