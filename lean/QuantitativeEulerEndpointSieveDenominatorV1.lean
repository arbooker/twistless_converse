module

public import QuantitativeEulerEndpointSieveBoundV1
public import QuantitativeEulerEndpointSieveMomentV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointSieve
open Finset Nat

/-- On actual prime divisors the normalized Selberg Euler weight is exactly
the local forbidden-residue density. -/
theorem selberg_normalized_prime (s : BoundingSieve) {p : ℕ}
    (hp : p.Prime) (hd : p∣s.prodPrimes) :
    s.selbergTerms p/(1+s.selbergTerms p)=s.nu p := by
  have hν := s.nu_lt_one_of_prime p hp hd
  have hn : 1-s.nu p≠0 := by linarith
  rw [s.selbergTerms_apply,hp.primeFactors,prod_singleton]
  field_simp
  ring

/-- The true truncated Selberg denominator retains half of any Euler product
whose logarithmic first moment fits below half the log cutoff. Distinct
prime subsets are injected into actual divisors, so no formal Euler-product
or independent-probability model substitutes for the denominator. -/
theorem denominator_ge_half_product (s : BoundingSieve) (z : ℕ) (hz : 1<z)
    (S : Finset ℕ) (hS : S⊆s.prodPrimes.primeFactors)
    (hmoment : (∑ p ∈ S, s.nu p*Real.log p)≤Real.log (z : ℝ)/2) :
    (∏ p ∈ S, (1+s.selbergTerms p))/2≤denominator s z := by
  classical
  have hp (p : ℕ) (h : p∈S) : p.Prime := Nat.prime_of_mem_primeFactors (hS h)
  have hd (p : ℕ) (h : p∈S) : p∣s.prodPrimes := Nat.dvd_of_mem_primeFactors (hS h)
  have hg (p : ℕ) (h : p∈S) : 0≤s.selbergTerms p := (s.selbergTerms_pos (hd p h)).le
  have hmoment' : (∑ p ∈ S,
      s.selbergTerms p/(1+s.selbergTerms p)*Real.log p)≤Real.log (z : ℝ)/2 := by
    simpa only [show (∑ p ∈ S, s.selbergTerms p/(1+s.selbergTerms p)*Real.log p)=
      ∑ p ∈ S, s.nu p*Real.log p from sum_congr rfl (fun p h => by
        rw [selberg_normalized_prime s (hp p h) (hd p h)])] using hmoment
  have htrunc := truncated_squarefree_product_mass S (fun p => s.selbergTerms p)
    (fun p h => (hp p h).one_lt.le) hg (by exact_mod_cast hz) hmoment'
  apply htrunc.trans
  let value : ℕ → ℝ := fun d => if d≤z then s.selbergTerms d else 0
  have hterm (T : Finset ℕ) (hT : T∈S.powerset) :
      (if (∏ p ∈ T, (p : ℝ))≤(z : ℝ) then ∏ p ∈ T, s.selbergTerms p else 0)=
        value (∏ p ∈ T, p) := by
    have hTS := (mem_powerset.mp hT).trans hS
    have he := s.selbergTerms_isMultiplicative.map_prod_of_subset_primeFactors s.prodPrimes T hTS
    have hc : (∏ p ∈ T, (p : ℝ))=((∏ p ∈ T, p : ℕ) : ℝ) := by simp
    simp only [value,← he,hc,Nat.cast_le]
  rw [sum_congr rfl hterm]
  have hdiv (T : Finset ℕ) (hT : T∈S.powerset) : (∏ p ∈ T, p)∈s.prodPrimes.divisors := by
    apply Nat.mem_divisors.mpr
    refine ⟨?_,s.prodPrimes_ne_zero⟩
    rw [← Nat.prod_primeFactors_of_squarefree s.prodPrimes_squarefree]
    exact prod_dvd_prod_of_subset _ _ _ ((mem_powerset.mp hT).trans hS)
  have hinj : Set.InjOn (fun T : Finset ℕ => ∏ p ∈ T, p) (S.powerset : Set (Finset ℕ)) := by
    intro T hT U hU he
    have hT' := Nat.primeFactors_prod (fun p h => hp p ((mem_powerset.mp hT) h))
    have hU' := Nat.primeFactors_prod (fun p h => hp p ((mem_powerset.mp hU) h))
    exact hT'.symm.trans ((congrArg Nat.primeFactors he).trans hU')
  rw [← sum_image hinj]
  apply sum_le_sum_of_subset_of_nonneg
  · intro d hd'
    obtain ⟨T,hT,rfl⟩ := mem_image.mp hd'
    exact hdiv T hT
  · intro d hd' _
    dsimp [value]
    split_ifs
    · exact (s.selbergTerms_pos (mem_divisors.mp hd').1).le
    · exact le_rfl

#print axioms selberg_normalized_prime
#print axioms denominator_ge_half_product
end QuantitativeEulerEndpointSieve
