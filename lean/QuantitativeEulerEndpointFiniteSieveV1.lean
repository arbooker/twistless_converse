module

public import QuantitativeEulerEndpointSieveModelBoundV1
public import QuantitativeEulerEndpointPrimeMomentV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointSieve
open Finset Nat

theorem selberg_factor_inv (s : BoundingSieve) (p : ℕ) (hp : p.Prime)
    (hd : p∣s.prodPrimes) : (1+s.selbergTerms p)⁻¹=1-s.nu p := by
  have hn : 1-s.nu p≠0 := by have := s.nu_lt_one_of_prime p hp hd; linarith
  rw [s.selbergTerms_apply,hp.primeFactors,prod_singleton]
  field_simp
  ring

/-- The actual sieve bound with a fixed polynomial cutoff. Its main term
is the explicit product of complementary residue densities. -/
theorem residue_count_le_product (P : ℕ) (hP : Squarefree P)
    (R : ∀ p : ℕ, Finset (ZMod p))
    (hR : ∀ p∈P.primeFactors, 0<(R p).card ∧ (R p).card<p)
    (hR2 : ∀ p∈P.primeFactors, (R p).card≤2)
    (x z y : ℕ) (hy4 : 4≤y) (hyz : y^24≤z)
    (hy : ∀ p∈P.primeFactors, p≤y) :
    (Nat.count (fun n : ℕ => ∀ p∈P.primeFactors, (n : ZMod p)∉R p) x : ℝ)≤
      2*(x : ℝ)*(∏ p∈P.primeFactors, (1-((R p).card : ℝ)/(p : ℝ)))+(z : ℝ)^6 := by
  let s := residueSieve P hP R hR x
  let F : ℝ := ∏ p∈P.primeFactors, (1+s.selbergTerms p)
  have hF : 0<F := prod_pos (fun p hp => by
    have h := s.selbergTerms_pos (show p∣s.prodPrimes from Nat.dvd_of_mem_primeFactors hp)
    linarith)
  have hz : 1<z := lt_of_lt_of_le
    (one_lt_pow₀ (by omega : 1<y) (by norm_num : 24≠0)) hyz
  have hden : F/2≤denominator s z := by
    apply denominator_ge_half_product_of_pow s z y hy4 hyz P.primeFactors subset_rfl hy
    intro p hp
    change residueDensity R p≤2/(p : ℝ)
    rw [residueDensity_prime R p (Nat.prime_of_mem_primeFactors hp)]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hR2 p hp) (Nat.cast_nonneg p)
  have hbase := residue_count_le_sieve P hP R hR x z hz.le
  have hmain : (x : ℝ)/denominator s z≤2*(x : ℝ)/F := by
    calc
      _ ≤ (x : ℝ)/(F/2) := div_le_div_of_nonneg_left (Nat.cast_nonneg x) (by positivity) hden
      _ = _ := by ring
  have hprod : F⁻¹=∏ p∈P.primeFactors, (1-((R p).card : ℝ)/(p : ℝ)) := by
    dsimp only [F]
    rw [← prod_inv_distrib]
    apply prod_congr rfl
    intro p hp
    rw [selberg_factor_inv s p (Nat.prime_of_mem_primeFactors hp)
      (show p∣s.prodPrimes from Nat.dvd_of_mem_primeFactors hp)]
    change 1-residueDensity R p=_
    rw [residueDensity_prime R p (Nat.prime_of_mem_primeFactors hp)]
  have hmain' : (x : ℝ)/denominator s z≤
      2*(x : ℝ)*(∏ p∈P.primeFactors, (1-((R p).card : ℝ)/(p : ℝ))) := by
    simpa only [div_eq_mul_inv,hprod] using hmain
  exact hbase.trans (add_le_add hmain' le_rfl)

/-- Concrete one- and two-residue sieve. The auxiliary primes are >2 and the
shift is nonzero at every active prime, so the local densities really are
1/p and 2/p. There is no assumed remainder or moment estimate. -/
theorem two_residue_sifted_bound (P : ℕ) (hP : Squarefree P)
    (Q : ℕ) (active : ℕ → Prop) [DecidablePred active]
    (hp3 : ∀ p∈P.primeFactors, 2<p)
    (hQ : ∀ p∈P.primeFactors, active p → (Q : ZMod p)≠0)
    (x z y : ℕ) (hy4 : 4≤y) (hyz : y^24≤z)
    (hy : ∀ p∈P.primeFactors, p≤y) :
    (Nat.count (fun n : ℕ => ∀ p∈P.primeFactors,
      (n : ZMod p)≠0 ∧ (active p → (n : ZMod p)≠Q)) x : ℝ)≤
      2*(x : ℝ)*(∏ p∈P.primeFactors, (1-(if active p then (2 : ℝ) else 1)/(p : ℝ)))+
        (z : ℝ)^6 := by
  classical
  let R : ∀ p : ℕ, Finset (ZMod p) := fun p => twoResidues p Q (active p)
  have hc (p : ℕ) (hp : p∈P.primeFactors) : (R p).card=if active p then 2 else 1 :=
    twoResidues_card p Q (active p) (hQ p hp)
  have hR (p : ℕ) (hp : p∈P.primeFactors) : 0<(R p).card ∧ (R p).card<p := by
    rw [hc p hp]
    have h := hp3 p hp
    split_ifs <;> omega
  have hR2 (p : ℕ) (hp : p∈P.primeFactors) : (R p).card≤2 := by rw [hc p hp]; split_ifs <;> omega
  have he (p n : ℕ) : (n : ZMod p)∉R p ↔
      (n : ZMod p)≠0 ∧ (active p → (n : ZMod p)≠Q) := by
    by_cases ha : active p <;> simp [R,twoResidues,ha]
  have h := residue_count_le_product P hP R hR hR2 x z y hy4 hyz hy
  simp only [he] at h
  have hprod : (∏ p∈P.primeFactors, (1-((R p).card : ℝ)/(p : ℝ)))=
      ∏ p∈P.primeFactors, (1-(if active p then (2 : ℝ) else 1)/(p : ℝ)) := by
    apply prod_congr rfl
    intro p hp
    rw [hc p hp]
    split_ifs <;> norm_num
  rwa [hprod] at h

#print axioms residue_count_le_product
#print axioms two_residue_sifted_bound
end QuantitativeEulerEndpointSieve
