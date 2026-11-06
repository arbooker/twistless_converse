module

public import QuantitativeEulerEndpointSieveCRTV1
public import QuantitativeEulerEndpointSieveBoundV1
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Data.Nat.GCD.BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointSieve
open Finset Nat ArithmeticFunction

/-- A number is labelled by precisely the auxiliary primes at which it
lies in a forbidden residue. Multiplicity of labels is kept as a weight. -/
def residueLabel (P : ℕ) (R : ∀ p : ℕ, Finset (ZMod p)) (n : ℕ) : ℕ :=
  ∏ p ∈ P.primeFactors.filter (fun p => (n : ZMod p)∈R p), p

def residueDensity (R : ∀ p : ℕ, Finset (ZMod p)) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => ((R p).card : ℝ)/(p : ℝ))

theorem residueDensity_prime (R : ∀ p : ℕ, Finset (ZMod p)) (p : ℕ) (hp : p.Prime) :
    residueDensity R p=((R p).card : ℝ)/(p : ℝ) := by
  simp [residueDensity,ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero,hp.primeFactors]

theorem residueLabel_ne_zero (P : ℕ) (R : ∀ p : ℕ, Finset (ZMod p)) (n : ℕ) :
    residueLabel P R n≠0 :=
  prod_ne_zero_iff.mpr (fun _ hp => (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).ne_zero)

theorem residueLabel_primeFactors (P : ℕ) (R : ∀ p : ℕ, Finset (ZMod p)) (n : ℕ) :
    (residueLabel P R n).primeFactors=P.primeFactors.filter (fun p => (n : ZMod p)∈R p) :=
  Nat.primeFactors_prod (fun _ hp => Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)

theorem dvd_residueLabel_iff (P : ℕ) (hP : Squarefree P)
    (R : ∀ p : ℕ, Finset (ZMod p)) (d n : ℕ) (hd : d∣P) :
    d∣residueLabel P R n ↔ ∀ p∈d.primeFactors, (n : ZMod p)∈R p := by
  have hdS := hP.squarefree_of_dvd hd
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hdS]
  rw [Nat.prod_primeFactors_dvd_iff (residueLabel_ne_zero P R n),residueLabel_primeFactors]
  constructor
  · intro h p hp
    exact (mem_filter.mp (h hp)).2
  · intro h p hp
    exact mem_filter.mpr ⟨Nat.primeFactors_mono hd hP.ne_zero hp,h p hp⟩

theorem coprime_residueLabel_iff (P : ℕ) (hP : Squarefree P)
    (R : ∀ p : ℕ, Finset (ZMod p)) (n : ℕ) :
    P.Coprime (residueLabel P R n) ↔ ∀ p∈P.primeFactors, (n : ZMod p)∉R p := by
  have he (p : ℕ) (hp : p∈P.primeFactors) :
      p∣residueLabel P R n ↔ (n : ZMod p)∈R p := by
    rw [dvd_residueLabel_iff P hP R p n (Nat.dvd_of_mem_primeFactors hp),
      (Nat.prime_of_mem_primeFactors hp).primeFactors]
    simp
  conv_lhs => lhs; rw [← Nat.prod_primeFactors_of_squarefree hP]
  rw [Nat.coprime_prod_left_iff]
  exact forall₂_congr (fun p hp => by
    rw [(Nat.prime_of_mem_primeFactors hp).coprime_iff_not_dvd,he p hp])

/-- The actual finite residue sieve, as a Mathlib BoundingSieve. -/
def residueSieve (P : ℕ) (hP : Squarefree P) (R : ∀ p : ℕ, Finset (ZMod p))
    (hR : ∀ p∈P.primeFactors, 0<(R p).card ∧ (R p).card<p) (x : ℕ) : BoundingSieve where
  support := (range x).image (residueLabel P R)
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun d => (((range x).filter (fun n => residueLabel P R n=d)).card : ℝ)
  weights_nonneg := fun _ => Nat.cast_nonneg _
  totalMass := x
  nu := residueDensity R
  nu_mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  nu_pos_of_prime := by
    intro p hp hpd
    rw [residueDensity_prime R p hp]
    exact div_pos (by exact_mod_cast (hR p (Nat.mem_primeFactors.mpr ⟨hp,hpd,hP.ne_zero⟩)).1)
      (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := by
    intro p hp hpd
    rw [residueDensity_prime R p hp]
    apply (div_lt_one (by exact_mod_cast hp.pos)).mpr
    exact_mod_cast (hR p (Nat.mem_primeFactors.mpr ⟨hp,hpd,hP.ne_zero⟩)).2

/-- Pushforward weights retain each integer exactly once, including when
many integers have the same forbidden-prime label. -/
theorem residueLabel_weighted_sum (P : ℕ) (R : ∀ p : ℕ, Finset (ZMod p))
    (x : ℕ) (f : ℕ → ℝ) :
    (∑ d ∈ (range x).image (residueLabel P R),
      (((range x).filter (fun n => residueLabel P R n=d)).card : ℝ)*f d)=
        ∑ n ∈ range x, f (residueLabel P R n) := by
  simpa only [sum_const,nsmul_eq_mul] using
    sum_fiberwise_of_maps_to' (fun n hn => mem_image_of_mem (residueLabel P R) hn) f

theorem residueSieve_multSum (P : ℕ) (hP : Squarefree P)
    (R : ∀ p : ℕ, Finset (ZMod p))
    (hR : ∀ p∈P.primeFactors, 0<(R p).card ∧ (R p).card<p) (x d : ℕ) (hd : d∣P) :
    (residueSieve P hP R hR x).multSum d=
      (Nat.count (fun n : ℕ => ∀ p∈d.primeFactors, (n : ZMod p)∈R p) x : ℝ) := by
  classical
  unfold BoundingSieve.multSum
  change (∑ m ∈ (range x).image (residueLabel P R),
    if d∣m then (((range x).filter (fun n => residueLabel P R n=m)).card : ℝ) else 0)=_
  have hf := residueLabel_weighted_sum P R x (fun m => if d∣m then 1 else 0)
  simp only [mul_ite,mul_one,mul_zero] at hf
  rw [hf]
  simp_rw [dvd_residueLabel_iff P hP R d _ hd]
  rw [Nat.count_eq_card_filter_range]
  simp

theorem residueSieve_siftedSum (P : ℕ) (hP : Squarefree P)
    (R : ∀ p : ℕ, Finset (ZMod p))
    (hR : ∀ p∈P.primeFactors, 0<(R p).card ∧ (R p).card<p) (x : ℕ) :
    (residueSieve P hP R hR x).siftedSum=
      (Nat.count (fun n : ℕ => ∀ p∈P.primeFactors, (n : ZMod p)∉R p) x : ℝ) := by
  classical
  unfold BoundingSieve.siftedSum
  change (∑ m ∈ (range x).image (residueLabel P R),
    if P.Coprime m then (((range x).filter (fun n => residueLabel P R n=m)).card : ℝ) else 0)=_
  have hf := residueLabel_weighted_sum P R x (fun m => if P.Coprime m then 1 else 0)
  simp only [mul_ite,mul_one,mul_zero] at hf
  rw [hf]
  simp_rw [coprime_residueLabel_iff P hP R]
  rw [Nat.count_eq_card_filter_range]
  simp

#print axioms residueSieve_multSum
#print axioms residueSieve_siftedSum
end QuantitativeEulerEndpointSieve
