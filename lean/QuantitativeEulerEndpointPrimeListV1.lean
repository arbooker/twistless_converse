module

public import QuantitativeEulerEndpointPrimeChainV1
public import QuantitativeEulerEndpointPreparedV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open QuantitativeEulerDensityGenerators QuantitativeEulerEndpointProduct
open scoped Classical

variable {N : ℕ} [NeZero N] {excluded : Finset ℕ} {threshold : ℕ}

def goodPrimeFinset (P : Prepared N excluded threshold) (n : ℕ) : Finset ℕ :=
  (n+1).primesBelow.filter P.Good

def goodPrimeAt (P : Prepared N excluded threshold) (n : ℕ)
    (p : {q // q∈goodPrimeFinset P n}) : EligiblePrime N :=
  ⟨p.val,Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp p.property).1,
    (P.prime_data p.val (Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp p.property).1)
      (Finset.mem_filter.mp p.property).2).2.1⟩

def goodPrimeList (P : Prepared N excluded threshold) (n : ℕ) : List (EligiblePrime N) :=
  (goodPrimeFinset P n).attach.toList.map (goodPrimeAt P n)

theorem goodPrimeList_nodup (P : Prepared N excluded threshold) (n : ℕ) :
    (goodPrimeList P n).Nodup := by
  apply List.Nodup.map _ (Finset.nodup_toList _)
  intro p q h
  exact Subtype.ext (congrArg (fun r : EligiblePrime N => r.val) h)

theorem goodPrimeList_mem (P : Prepared N excluded threshold) (n : ℕ)
    (p : EligiblePrime N) (hp : p∈goodPrimeList P n) : P.Good p.val ∧ p.val≤n := by
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hp
  refine ⟨(Finset.mem_filter.mp r.property).2,?_⟩
  have hr := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp r.property).1).1
  exact Nat.lt_succ_iff.mp hr

theorem goodPrimeList_product (P : Prepared N excluded threshold) (n : ℕ) :
    ((goodPrimeList P n).map primeFactor).prod=
      ∏ p∈(n+1).primesBelow.filter P.Good, (1-(1-1/(p : ℝ))/((p : ℝ)-1)) := by
  rw [goodPrimeList,List.map_map,Finset.prod_map_toList]
  change (∏ p∈(goodPrimeFinset P n).attach, (1-(p.val : ℝ)⁻¹))=_
  rw [Finset.prod_attach (goodPrimeFinset P n) (fun p : ℕ => 1-(p : ℝ)⁻¹)]
  apply Finset.prod_congr rfl
  intro p hp
  simpa only [one_div] using
    (variable_tolerance_factor (Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hp).1)).symm

theorem goodPrimeList_prepared_product (N : ℕ) [NeZero N] (hN : 2≤N)
    (excluded : Finset ℕ) (threshold : ℕ) :
    ∃ A : ℝ, 0<A ∧ ∀ n : ℕ, 0<n →
      ((goodPrimeList (prepared N hN excluded threshold) n).map primeFactor).prod≤A/Real.log (n+1 : ℝ) := by
  obtain ⟨A,hA,ha⟩ := prepared_endpoint_product N hN excluded threshold
  refine ⟨A,hA,?_⟩
  intro n hn
  rw [goodPrimeList_product]
  exact ha n hn

#print axioms goodPrimeList_nodup
#print axioms goodPrimeList_mem
#print axioms goodPrimeList_product
#print axioms goodPrimeList_prepared_product
end QuantitativeEulerEndpointPrepared
