module

public import QuantitativeArithmeticShiftedSieveWeightsV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointSieve

open Finset Nat ArithmeticFunction QuantitativeArithmetic
open scoped ArithmeticFunction.Moebius

/-- The actual Selberg denominator for arbitrary local densities. In the
two-residue sieve the density is 1/p or 2/p, not always 1/p. -/
def denominator (s : BoundingSieve) (z : ℕ) : ℝ :=
  ∑ d ∈ s.prodPrimes.divisors, if d≤z then s.selbergTerms d else 0

def dualWeights (s : BoundingSieve) (z d : ℕ) : ℝ :=
  if d≤z then (μ d : ℝ)*s.selbergTerms d/denominator s z else 0

def weights (s : BoundingSieve) (z d : ℕ) : ℝ :=
  (s.nu d)⁻¹*reverseDivisorMobius s.prodPrimes (dualWeights s z) d

theorem denominator_nonneg (s : BoundingSieve) (z : ℕ) : 0≤denominator s z := by
  apply sum_nonneg
  intro d hd
  split_ifs
  · exact (s.selbergTerms_pos (mem_divisors.mp hd).1).le
  · exact le_rfl

theorem denominator_one_le (s : BoundingSieve) (z : ℕ) (hz : 1≤z) :
    1≤denominator s z := by
  have h1 : 1∈s.prodPrimes.divisors := mem_divisors.mpr ⟨one_dvd _,s.prodPrimes_ne_zero⟩
  have h := single_le_sum (s := s.prodPrimes.divisors)
    (f := fun d => if d≤z then s.selbergTerms d else 0)
    (fun d hd => by split_ifs; exact (s.selbergTerms_pos (mem_divisors.mp hd).1).le; exact le_rfl) h1
  simpa only [hz, ite_true, s.selbergTerms_isMultiplicative.map_one, denominator] using h

theorem weights_dual (s : BoundingSieve) (z l : ℕ) (hl : l∣s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors, if l∣d then s.nu d*weights s z d else 0) =
      dualWeights s z l := by
  rw [← sum_reverseDivisorMobius s.prodPrimes s.prodPrimes_ne_zero (dualWeights s z) l hl]
  apply sum_congr rfl
  intro d hd
  have hν := s.nu_ne_zero (mem_divisors.mp hd).1
  split_ifs
  · rw [weights, ← mul_assoc, mul_inv_cancel₀ hν, one_mul]
  · rfl

theorem abs_dualWeights (s : BoundingSieve) (z d : ℕ) (hd : d∣s.prodPrimes) :
    |dualWeights s z d| = if d≤z then s.selbergTerms d/denominator s z else 0 := by
  have hμ : |(μ d : ℝ)|=1 := by
    exact_mod_cast abs_moebius_eq_one_of_squarefree (s.squarefree_of_dvd_prodPrimes hd)
  simp only [dualWeights]
  split_ifs
  · rw [abs_div,abs_mul,hμ,one_mul,abs_of_pos (s.selbergTerms_pos hd),
      abs_of_nonneg (denominator_nonneg s z)]
  · simp

theorem sum_abs_dualWeights (s : BoundingSieve) (z : ℕ) (hz : 1≤z) :
    (∑ d ∈ s.prodPrimes.divisors, |dualWeights s z d|)=1 := by
  have hG : denominator s z≠0 := by have := denominator_one_le s z hz; linarith
  calc
    _ = ∑ d ∈ s.prodPrimes.divisors,
        (if d≤z then s.selbergTerms d else 0)/denominator s z := by
      apply sum_congr rfl
      intro d hd
      rw [abs_dualWeights s z d (mem_divisors.mp hd).1]
      split_ifs <;> simp
    _ = denominator s z/denominator s z := by rw [← sum_div]; rfl
    _ = 1 := div_self hG

theorem weights_one (s : BoundingSieve) (z : ℕ) (hz : 1≤z) : weights s z 1=1 := by
  rw [weights,s.nu_mult.map_one,inv_one,one_mul,reverseDivisorMobius,Nat.div_one,
    divisorMobiusTransform_eq,
    Nat.sum_div_divisors s.prodPrimes (fun d => (μ d : ℝ)*dualWeights s z d)]
  rw [← sum_abs_dualWeights s z hz]
  apply sum_congr rfl
  intro d hd
  have hdP := (mem_divisors.mp hd).1
  have hμ : (μ d : ℝ)^2=1 := by
    exact_mod_cast moebius_sq_eq_one_of_squarefree (s.squarefree_of_dvd_prodPrimes hdP)
  rw [abs_dualWeights s z d hdP]
  simp only [dualWeights]
  split_ifs
  · calc
      _ = (μ d : ℝ)^2*s.selbergTerms d/denominator s z := by ring
      _ = _ := by rw [hμ,one_mul]
  · simp

theorem weights_abs_le (s : BoundingSieve) (z d : ℕ) (hz : 1≤z)
    (hd : d∣s.prodPrimes) : |weights s z d|≤(s.nu d)⁻¹ := by
  rw [weights,abs_mul,abs_of_pos (inv_pos.mpr (s.nu_pos_of_dvd_prodPrimes hd))]
  have h := reverseDivisorMobius_abs_le s.prodPrimes d s.prodPrimes_ne_zero hd (dualWeights s z)
  rw [sum_abs_dualWeights s z hz] at h
  simpa using mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (s.nu_pos_of_dvd_prodPrimes hd).le)

theorem weights_zero_of_lt (s : BoundingSieve) (z d : ℕ)
    (hd : d∣s.prodPrimes) (hzd : z<d) : weights s z d=0 := by
  rw [weights,reverseDivisorMobius,divisorMobiusTransform_eq]
  suffices (∑ a ∈ (s.prodPrimes/d).divisors,
      (μ (s.prodPrimes/d/a) : ℝ)*dualWeights s z (s.prodPrimes/a))=0 by rw [this,mul_zero]
  apply sum_eq_zero
  intro a ha
  have haD := (mem_divisors.mp ha).1
  have haP := haD.trans (Nat.div_dvd_of_dvd hd)
  have hdPa : d∣s.prodPrimes/a := by
    apply (Nat.dvd_div_iff_mul_dvd haP).mpr
    simpa [mul_comm] using (Nat.dvd_div_iff_mul_dvd hd).mp haD
  have hPa : 0<s.prodPrimes/a := Nat.div_pos
    (Nat.le_of_dvd (Nat.pos_of_ne_zero s.prodPrimes_ne_zero) haP) (Nat.pos_of_mem_divisors ha)
  have hdle := Nat.le_of_dvd hPa hdPa
  simp [dualWeights, show ¬s.prodPrimes/a≤z by omega]

/-- The constructed weights achieve the exact optimal quadratic main term
for the genuine local densities, including the extra forbidden residue. -/
theorem weights_mainSum (s : BoundingSieve) (z : ℕ) (hz : 1≤z) :
    s.mainSum (BoundingSieve.lambdaSquared (weights s z))=1/denominator s z := by
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  have hG : denominator s z≠0 := by have := denominator_one_le s z hz; linarith
  calc
    _ = ∑ l ∈ s.prodPrimes.divisors,
        (if l≤z then s.selbergTerms l else 0)/(denominator s z)^2 := by
      apply sum_congr rfl
      intro l hl
      have hlP := (mem_divisors.mp hl).1
      rw [weights_dual s z l hlP]
      have hμ : (μ l : ℝ)^2=1 := by
        exact_mod_cast moebius_sq_eq_one_of_squarefree (s.squarefree_of_dvd_prodPrimes hlP)
      have hg : s.selbergTerms l≠0 := (s.selbergTerms_pos hlP).ne'
      simp only [dualWeights]
      split_ifs
      · rw [div_pow,mul_pow,hμ,one_mul]
        field_simp
      · simp
    _ = denominator s z/(denominator s z)^2 := by rw [← sum_div]; rfl
    _ = _ := by field_simp

/-- For local density at least 1/d the constructed weights have sum of
absolute values at most z^2, uniformly in the full sieve modulus. -/
theorem weights_sum_abs_le (s : BoundingSieve) (z : ℕ) (hz : 1≤z)
    (hν : ∀ d, d∣s.prodPrimes → (s.nu d)⁻¹≤(d : ℝ)) :
    (∑ d ∈ s.prodPrimes.divisors, |weights s z d|)≤(z : ℝ)^2 := by
  let T := s.prodPrimes.divisors.filter (fun d => d≤z)
  have hsub : T⊆Icc 1 z := by
    intro d hd
    obtain ⟨hdP,hdz⟩ := mem_filter.mp hd
    exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdP,hdz⟩
  have he : (∑ d ∈ s.prodPrimes.divisors, |weights s z d|)=
      ∑ d ∈ T, |weights s z d| := by
    symm
    apply sum_subset (filter_subset _ _)
    intro d hd hdT
    have hzd : z<d := by
      have hn : ¬d≤z := fun h => hdT (mem_filter.mpr ⟨hd,h⟩)
      omega
    rw [weights_zero_of_lt s z d (mem_divisors.mp hd).1 hzd,abs_zero]
  rw [he]
  calc
    _ ≤ ∑ d ∈ T, (d : ℝ) := sum_le_sum (fun d hd =>
      (weights_abs_le s z d hz (mem_divisors.mp (mem_filter.mp hd).1).1).trans
        (hν d (mem_divisors.mp (mem_filter.mp hd).1).1))
    _ ≤ ∑ d ∈ Icc 1 z, (d : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
    _ ≤ ∑ _d ∈ Icc 1 z, (z : ℝ) := sum_le_sum (fun d hd => by
      exact_mod_cast (mem_Icc.mp hd).2)
    _ = (z : ℝ)^2 := by simp [sq]

#print axioms weights_one
#print axioms weights_zero_of_lt
#print axioms weights_mainSum
#print axioms weights_sum_abs_le

end QuantitativeEulerEndpointSieve
