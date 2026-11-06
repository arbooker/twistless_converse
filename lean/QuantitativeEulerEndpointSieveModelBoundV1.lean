module

public import QuantitativeEulerEndpointSieveModelV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointSieve
open Finset Nat ArithmeticFunction

/-- CRT discrepancy for every squarefree divisor, with the actual product
of local residue cardinalities as its error. -/
theorem residue_count_error (d : ℕ) (hd : Squarefree d)
    (R : ∀ p : ℕ, Finset (ZMod p)) (x : ℕ) :
    |(Nat.count (fun n : ℕ => ∀ p∈d.primeFactors, (n : ZMod p)∈R p) x : ℝ)-
      (x : ℝ)*(∏ p∈d.primeFactors, ((R p).card : ℝ))/(d : ℝ)|≤
        ∏ p∈d.primeFactors, ((R p).card : ℝ) := by
  classical
  let ι := {p : ℕ // p∈d.primeFactors}
  let m : ι → ℕ := Subtype.val
  have hp (i : ι) : (m i).Prime := Nat.prime_of_mem_primeFactors i.property
  let (i : ι) : NeZero (m i) := ⟨(hp i).ne_zero⟩
  let : NeZero (∏ i, m i) := ⟨prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)⟩
  have hcop : Pairwise (fun i j : ι => Nat.Coprime (m i) (m j)) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i) (hp j)).mpr (fun he => hij (Subtype.ext he))
  have he : (∏ i : ι, (m i : ℝ))=(d : ℝ) := by
    change (∏ i : {p : ℕ // p∈d.primeFactors}, (i.val : ℝ))=(d : ℝ)
    rw [prod_coe_sort]
    rw [← Nat.cast_prod,Nat.prod_primeFactors_of_squarefree hd]
  have h := crt_count_error m hcop (fun i => R (m i)) x
  have hcard : (∏ i : ι, ((R (m i)).card : ℝ))=
      ∏ p∈d.primeFactors, ((R p).card : ℝ) := by
    change (∏ i : {p : ℕ // p∈d.primeFactors}, ((R i.val).card : ℝ))=_
    exact prod_coe_sort d.primeFactors (fun p => ((R p).card : ℝ))
  rw [he,hcard] at h
  simpa only [m,ι,Subtype.forall] using h

theorem residueDensity_squarefree (d : ℕ) (hd : Squarefree d)
    (R : ∀ p : ℕ, Finset (ZMod p)) :
    residueDensity R d=(∏ p∈d.primeFactors, ((R p).card : ℝ))/(d : ℝ) := by
  rw [residueDensity,ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero,prod_div_distrib]
  congr 1
  rw [← Nat.cast_prod,Nat.prod_primeFactors_of_squarefree hd]

theorem residueSieve_rem_bound (P : ℕ) (hP : Squarefree P)
    (R : ∀ p : ℕ, Finset (ZMod p))
    (hR : ∀ p∈P.primeFactors, 0<(R p).card ∧ (R p).card<p)
    (x d : ℕ) (hd : d∣P) : |(residueSieve P hP R hR x).rem d|≤(d : ℝ) := by
  have hdS := hP.squarefree_of_dvd hd
  have hc := residue_count_error d hdS R x
  have hprod : (∏ p∈d.primeFactors, ((R p).card : ℝ))≤(d : ℝ) := by
    calc
      _ ≤ ∏ p∈d.primeFactors, (p : ℝ) := by
        apply prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        intro p hp
        exact_mod_cast (hR p (Nat.primeFactors_mono hd hP.ne_zero hp)).2.le
      _ = _ := by rw [← Nat.cast_prod,Nat.prod_primeFactors_of_squarefree hdS]
  unfold BoundingSieve.rem
  rw [residueSieve_multSum P hP R hR x d hd]
  change |_-residueDensity R d*(x : ℝ)|≤_
  rw [residueDensity_squarefree d hdS R]
  have he : (∏ p∈d.primeFactors, ((R p).card : ℝ))/(d : ℝ)*(x : ℝ)=
      (x : ℝ)*(∏ p∈d.primeFactors, ((R p).card : ℝ))/(d : ℝ) := by ring
  rw [he]
  exact hc.trans hprod

theorem residueSieve_nu_inv_bound (P : ℕ) (hP : Squarefree P)
    (R : ∀ p : ℕ, Finset (ZMod p))
    (hR : ∀ p∈P.primeFactors, 0<(R p).card ∧ (R p).card<p)
    (x d : ℕ) (hd : d∣P) : ((residueSieve P hP R hR x).nu d)⁻¹≤(d : ℝ) := by
  change (residueDensity R d)⁻¹≤_
  rw [residueDensity_squarefree d (hP.squarefree_of_dvd hd) R,inv_div]
  have hprod : (1 : ℝ)≤∏ p∈d.primeFactors, ((R p).card : ℝ) := by
    apply one_le_prod₀
    intro p hp
    exact_mod_cast (Nat.succ_le_iff.mpr (hR p (Nat.primeFactors_mono hd hP.ne_zero hp)).1)
  exact div_le_self (Nat.cast_nonneg d) hprod

/-- A literal finite congruence-count bound. Both the local discrepancy and
the optimal Selberg-weight remainder are proved, rather than assumed. -/
theorem residue_count_le_sieve (P : ℕ) (hP : Squarefree P)
    (R : ∀ p : ℕ, Finset (ZMod p))
    (hR : ∀ p∈P.primeFactors, 0<(R p).card ∧ (R p).card<p)
    (x z : ℕ) (hz : 1≤z) :
    (Nat.count (fun n : ℕ => ∀ p∈P.primeFactors, (n : ZMod p)∉R p) x : ℝ)≤
      (x : ℝ)/denominator (residueSieve P hP R hR x) z+(z : ℝ)^6 := by
  rw [← residueSieve_siftedSum P hP R hR x]
  exact sifted_bound (residueSieve P hP R hR x) z hz
    (residueSieve_nu_inv_bound P hP R hR x)
    (fun d hd => residueSieve_rem_bound P hP R hR x d (Nat.mem_divisors.mp hd).1)

#print axioms residue_count_error
#print axioms residueSieve_rem_bound
#print axioms residue_count_le_sieve
end QuantitativeEulerEndpointSieve
