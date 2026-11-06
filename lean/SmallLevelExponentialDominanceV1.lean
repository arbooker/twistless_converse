module

public import SmallLevelTwentyOneAugmentedLaurentRowsV1

set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelExponentialDominance

/-- A strict dominance check at one exponent persists at all later
exponents when every competing base is bounded by the dominant base. -/
theorem sum_pow_lt {ι : Type*} (s : Finset ι) (c b : ι → ℝ) (B : ℝ)
    (hB : 0 < B) (hc : ∀ i ∈ s, 0 ≤ c i) (hb : ∀ i ∈ s, 0 ≤ b i ∧ b i ≤ B)
    (k m : ℕ) (hm : k ≤ m) (hbase : ∑ i ∈ s, c i*b i^k < B^k) :
    ∑ i ∈ s, c i*b i^m < B^m := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hm
  calc
    (∑ i ∈ s, c i*b i^(k+t)) ≤ (∑ i ∈ s, c i*b i^k)*B^t := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      rw [pow_add,← mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hb i hi).1 (hb i hi).2 t)
        (mul_nonneg (hc i hi) (pow_nonneg (hb i hi).1 k))
    _  <  B^k*B^t := mul_lt_mul_of_pos_right hbase (pow_pos hB t)
    _ = B^(k+t) := (pow_add B k t).symm

theorem signed_sum_nonzero {ι : Type*} (s : Finset ι) (c b : ι → ℝ) (B : ℝ)
    (hB : 0 < B) (hb : ∀ i ∈ s, 0 ≤ b i ∧ b i ≤ B)
    (k m : ℕ) (hm : k ≤ m) (hbase : ∑ i ∈ s, |c i| *b i^k < B^k) :
    B^m+∑ i ∈ s, c i*b i^m ≠ 0 := by
  have hd := sum_pow_lt s (fun i => |c i|) b B hB (fun _ _ => abs_nonneg _) hb k m hm hbase
  have hl : -(∑ i ∈ s, |c i| *b i^m) ≤ ∑ i ∈ s, c i*b i^m := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i hi
    rw [← neg_mul]
    exact mul_le_mul_of_nonneg_right (neg_abs_le _) (pow_nonneg (hb i hi).1 m)
  linarith

theorem three_powers (a b c : ℂ) (i j k m : ℕ) :
    (a^m)^i*(b^m)^j*(c^m)^k=(a^i*b^j*c^k)^m := by
  simp only [mul_pow,← pow_mul,Nat.mul_comm m]

#print axioms sum_pow_lt
#print axioms signed_sum_nonzero
end SmallLevelExponentialDominance
