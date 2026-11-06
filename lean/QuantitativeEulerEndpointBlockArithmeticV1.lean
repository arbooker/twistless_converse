module

public import QuantitativeEulerEndpointPreparedV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBlocks
open Finset QuantitativeEulerEndpointAP QuantitativeEulerEndpointPrepared
attribute [local instance] Classical.propDecidable

/-- Reciprocal mass of the non-detecting primes in one block. -/
def blockLoss (P : ℕ → Prop) (blocks : ℕ → Finset ℕ) (j : ℕ) : ℝ :=
  ∑ p ∈ blocks j, badPrimeLoss P p

theorem blockLoss_nonneg (P : ℕ → Prop) (blocks : ℕ → Finset ℕ) (j : ℕ) :
    0≤blockLoss P blocks j :=
  sum_nonneg (fun p _ => badPrimeLoss_nonneg P p)

/-- Disjoint grouping spends the exceptional reciprocal budget only once,
regardless of the block endpoints or their sizes. -/
theorem blockLoss_sum_le (P : ℕ → Prop) (hs : Summable (badPrimeLoss P))
    (blocks : ℕ → Finset ℕ) (hd : Pairwise (fun i j => Disjoint (blocks i) (blocks j))) (J : Finset ℕ) :
    (∑ j ∈ J, blockLoss P blocks j)≤∑' p, badPrimeLoss P p := by
  have hdis : Set.PairwiseDisjoint (↑J) blocks := fun i _ j _ hij => hd hij
  change (∑ j ∈ J, ∑ p ∈ blocks j, badPrimeLoss P p)≤_
  rw [← sum_biUnion hdis]
  exact hs.sum_le_tsum _ (fun p _ => badPrimeLoss_nonneg P p)

theorem blockLoss_summable (P : ℕ → Prop) (hs : Summable (badPrimeLoss P))
    (blocks : ℕ → Finset ℕ) (hd : Pairwise (fun i j => Disjoint (blocks i) (blocks j))) :
    Summable (blockLoss P blocks) :=
  summable_of_sum_le (blockLoss_nonneg P blocks) (blockLoss_sum_le P hs blocks hd)

/-- This applies to the actual prepared detection certificates, with the
arithmetic summability premise discharged. -/
theorem prepared_blockLoss_summable (N : ℕ) [NeZero N] (hN : 2≤N)
    (excluded : Finset ℕ) (threshold : ℕ)
    (blocks : ℕ → Finset ℕ) (hd : Pairwise (fun i j => Disjoint (blocks i) (blocks j))) :
    Summable (blockLoss (prepared N hN excluded threshold).Good blocks) :=
  blockLoss_summable _ (prepared_exception_summable N hN excluded threshold) blocks hd

/-- Regrouping any finite initial prime interval into disjoint blocks
preserves the endpoint Euler product, with one constant for ALL partitions.
This is a product theorem, not a finite Euler-count transfer theorem. -/
theorem prepared_block_product (N : ℕ) [NeZero N] (hN : 2≤N)
    (excluded : Finset ℕ) (threshold : ℕ) :
    let P := prepared N hN excluded threshold
    ∃ C : ℝ, 0<C ∧ ∀ (n : ℕ), 0<n → ∀ (J : Finset ℕ) (blocks : ℕ → Finset ℕ),
      Set.PairwiseDisjoint (↑J) blocks → J.biUnion blocks=(n+1).primesBelow →
      (∏ j ∈ J, ∏ p ∈ (blocks j).filter P.Good,
        (1-(1-1/(p : ℝ))/((p : ℝ)-1)))≤C/Real.log (n+1 : ℝ) := by
  intro P
  obtain ⟨C,hC,hprod⟩ := prepared_endpoint_product N hN excluded threshold
  refine ⟨C,hC,?_⟩
  intro n hn J blocks hd hcover
  let f : ℕ → ℝ := fun p => if P.Good p then
    (1-(1-1/(p : ℝ))/((p : ℝ)-1)) else 1
  have he : (∏ j ∈ J, ∏ p ∈ (blocks j).filter P.Good,
      (1-(1-1/(p : ℝ))/((p : ℝ)-1)))=
      ∏ p ∈ (n+1).primesBelow.filter P.Good,
        (1-(1-1/(p : ℝ))/((p : ℝ)-1)) := by
    simp_rw [Finset.prod_filter]
    change (∏ j ∈ J, ∏ p ∈ blocks j, f p)=∏ p ∈ (n+1).primesBelow, f p
    rw [← prod_biUnion hd,hcover]
  rw [he]
  exact hprod n hn

#print axioms prepared_blockLoss_summable
#print axioms prepared_block_product
end QuantitativeEulerEndpointBlocks
