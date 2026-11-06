module

public import QuantitativeEulerEndpointAPProductV1
public import QuantitativeEulerEndpointPrimeSieveV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointAP
open Finset
attribute [local instance] Classical.propDecidable

private theorem count_eq_classical (A : ℕ → Prop) [d : DecidablePred A] (x : ℕ) :
    Nat.count A x=@Nat.count A (fun n => Classical.propDecidable (A n)) x := by
  exact congrArg (fun h : DecidablePred A => @Nat.count A h x) (Subsingleton.elim _ _)

def auxiliaryModulus (B : Finset ℕ) (Y : ℕ) : ℕ := ∏ p∈auxiliaryPrimes B Y, p

theorem auxiliaryModulus_squarefree (B : Finset ℕ) (Y : ℕ) : Squarefree (auxiliaryModulus B Y) := by
  have hp (p : ℕ) (h : p∈auxiliaryPrimes B Y) : p.Prime :=
    Nat.prime_of_mem_primesBelow (mem_filter.mp h).1
  apply Finset.squarefree_prod_of_pairwise_isCoprime
    (fun p hpS q hqS hpq => ?_) (fun p hpS => (hp p hpS).squarefree)
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (hp p hpS) (hp q hqS)).mpr hpq

theorem auxiliaryModulus_primeFactors (B : Finset ℕ) (Y : ℕ) :
    (auxiliaryModulus B Y).primeFactors=auxiliaryPrimes B Y :=
  Nat.primeFactors_prod (fun _ hp => Nat.prime_of_mem_primesBelow (mem_filter.mp hp).1)

/-- The literal positive shifted-divisor exceptional prime predicate. -/
def divisorException {M : ℕ} (a : ZMod M) (Q n : ℕ) : Prop :=
  n.Prime ∧ ¬∃ d : ℕ, d∣n-Q ∧ 0<d ∧ (d : ZMod M)=a

/-- Quantitative actual exceptional-prime count, with every arithmetic
product and local sieve estimate discharged. The cutoff can now be chosen
as a small power of x; no density or product-decay premise remains. -/
theorem divisorException_count_bound {M : ℕ} [NeZero M]
    (a : ZMod M) (ha : IsUnit a) (Q : ℕ) (hQ : 0<Q) :
    ∃ C : ℝ, 0<C ∧ ∀ x z Y : ℕ, 4≤Y → Y^24≤z →
      (Nat.count (divisorException a Q) x : ℝ)≤
        C*(x : ℝ)/(Real.log (Y : ℝ))^(1+apExponent M)+(z : ℝ)^6+(Y+1 : ℕ)+(Q : ℝ) := by
  let B := insert 2 Q.primeFactors
  obtain ⟨C,hC,hprod⟩ := two_residue_AP_product_bound a ha B
  refine ⟨2*C,by positivity,fun x z Y hY hcut => ?_⟩
  let P := auxiliaryModulus B Y
  let active : ℕ → Prop := fun p => 0<p ∧ (p : ZMod M)=a
  have hpf : P.primeFactors=auxiliaryPrimes B Y := auxiliaryModulus_primeFactors B Y
  have hp (p : ℕ) (h : p∈P.primeFactors) : p.Prime := by
    rw [hpf] at h
    exact Nat.prime_of_mem_primesBelow (mem_filter.mp h).1
  have hp3 (p : ℕ) (h : p∈P.primeFactors) : 2<p := by
    have hh := h
    rw [hpf] at hh
    have hnB := (mem_filter.mp hh).2
    have hn2 : p≠2 := by intro he; apply hnB; simp [B,he]
    have htwo := (hp p h).two_le
    omega
  have hnQ (p : ℕ) (h : p∈P.primeFactors) (_ : active p) : (Q : ZMod p)≠0 := by
    intro he
    have hd := (ZMod.natCast_eq_zero_iff Q p).mp he
    have hmem : p∈Q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp p h,hd,hQ.ne'⟩
    rw [hpf] at h
    exact (mem_filter.mp h).2 (mem_insert_of_mem hmem)
  have hy (p : ℕ) (h : p∈P.primeFactors) : p≤Y := by
    rw [hpf] at h
    exact (Nat.mem_primesBelow.mp (mem_filter.mp h).1).1.le
  have hbase := QuantitativeEulerEndpointSieve.divisor_exception_count_le_product
    P (auxiliaryModulus_squarefree B Y) Q active hp3 hnQ x z Y hY hcut hy
  have heprod : (∏ p∈P.primeFactors, (1-(if active p then (2 : ℝ) else 1)/(p : ℝ)))=
      ∏ p∈auxiliaryPrimes B Y, (1-(if (p : ZMod M)=a then (2 : ℝ) else 1)/(p : ℝ)) := by
    rw [← hpf]
    apply prod_congr rfl
    intro p h
    simp only [active,(hp p h).pos,true_and]
  rw [heprod] at hbase
  have hbase' : (Nat.count (divisorException a Q) x : ℝ)≤
      2*(x : ℝ)*(∏ p∈auxiliaryPrimes B Y, (1-(if (p : ZMod M)=a then (2 : ℝ) else 1)/(p : ℝ)))+
        (z : ℝ)^6+(Y+1 : ℕ)+(Q : ℝ) := by
    rw [count_eq_classical] at hbase
    unfold divisorException
    simpa only [active] using hbase
  have hm := mul_le_mul_of_nonneg_left (hprod Y hY) (by positivity : (0 : ℝ)≤2*(x : ℝ))
  calc
    _ ≤ 2*(x : ℝ)*(C/(Real.log (Y : ℝ))^(1+apExponent M))+(z : ℝ)^6+(Y+1 : ℕ)+(Q : ℝ) := by
      linarith
    _ = _ := by ring

#print axioms divisorException_count_bound
end QuantitativeEulerEndpointAP
