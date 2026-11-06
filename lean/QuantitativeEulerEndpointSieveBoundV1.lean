module

public import QuantitativeEulerEndpointSieveWeightsV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointSieve
open Finset Nat QuantitativeArithmetic

/-- The lcm coefficients of the constructed cutoff weights vanish above
z^2. This support fact keeps the remainder independent of the sieve modulus. -/
theorem weights_lambdaSquared_zero (s : BoundingSieve) (z d : ℕ)
    (hd : d∣s.prodPrimes) (hzd : z^2<d) :
    BoundingSieve.lambdaSquared (weights s z) d=0 := by
  unfold BoundingSieve.lambdaSquared
  apply sum_eq_zero
  intro a ha
  apply sum_eq_zero
  intro b hb
  split_ifs with he
  · have haP := (mem_divisors.mp ha).1.trans hd
    have hbP := (mem_divisors.mp hb).1.trans hd
    by_cases hza : z<a
    · rw [weights_zero_of_lt s z a haP hza,zero_mul]
    · have hzb : z<b := by
        by_contra hn
        have hab : a*b≤z*z := Nat.mul_le_mul (by omega) (by omega)
        have hle : Nat.lcm a b≤a*b := Nat.lcm_le_mul (Nat.pos_of_mem_divisors ha) (Nat.pos_of_mem_divisors hb)
        nlinarith
      rw [weights_zero_of_lt s z b hbP hzb,mul_zero]
  · rfl

/-- Uniform finite upper sieve for the extra-residue setting. The exact
optimal main term uses general local densities, and the explicit z^6
remainder is derived from the real cutoff weights, not postulated.
The residue-count estimate |rem d|<=d is retained as an explicit input. -/
theorem sifted_bound (s : BoundingSieve) (z : ℕ) (hz : 1≤z)
    (hν : ∀ d, d∣s.prodPrimes → (s.nu d)⁻¹≤(d : ℝ))
    (hrem : ∀ d∈s.prodPrimes.divisors, |s.rem d|≤(d : ℝ)) :
    s.siftedSum≤s.totalMass/denominator s z+(z : ℝ)^6 := by
  let w := weights s z
  have hbase := s.siftedSum_le_mainSum_errSum_of_upperMoebius
    (BoundingSieve.lambdaSquared w)
    (BoundingSieve.upperMoebius_lambdaSquared w (weights_one s z hz))
  rw [weights_mainSum s z hz] at hbase
  have herr : s.errSum (BoundingSieve.lambdaSquared w)≤(z : ℝ)^6 := by
    unfold BoundingSieve.errSum
    calc
      _ ≤ ∑ d ∈ s.prodPrimes.divisors,
          |BoundingSieve.lambdaSquared w d| *(z : ℝ)^2 := by
        apply sum_le_sum
        intro d hd
        by_cases hdz : d≤z^2
        · apply mul_le_mul_of_nonneg_left ((hrem d hd).trans ?_) (abs_nonneg _)
          exact_mod_cast hdz
        · have hzD := weights_lambdaSquared_zero s z d (mem_divisors.mp hd).1 (by omega)
          simp only [w,hzD,abs_zero,zero_mul,le_refl]
      _ = (∑ d ∈ s.prodPrimes.divisors, |BoundingSieve.lambdaSquared w d|)*(z : ℝ)^2 :=
        (sum_mul _ _ _).symm
      _ ≤ (∑ d ∈ s.prodPrimes.divisors,
          BoundingSieve.lambdaSquared (fun d => |w d|) d)*(z : ℝ)^2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact sum_le_sum (fun d _ => lambdaSquared_abs_le w d)
      _ = (∑ d ∈ s.prodPrimes.divisors, |w d|)^2*(z : ℝ)^2 := by
        rw [sum_divisors_lambdaSquared _ s.prodPrimes_ne_zero]
      _ ≤ ((z : ℝ)^2)^2*(z : ℝ)^2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact pow_le_pow_left₀ (sum_nonneg (fun _ _ => abs_nonneg _))
          (weights_sum_abs_le s z hz hν) 2
      _ = _ := by ring
  have h := hbase.trans (add_le_add le_rfl herr)
  simpa only [div_eq_mul_inv,one_mul] using h

#print axioms weights_lambdaSquared_zero
#print axioms sifted_bound
end QuantitativeEulerEndpointSieve
