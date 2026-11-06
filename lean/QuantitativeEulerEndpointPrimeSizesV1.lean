module

public import QuantitativeEulerEndpointPrimeBlocksV1

set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrimeBlocks
open Finset QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointSparsePrefix
open QuantitativeEulerDensityGenerators
attribute [local instance] Classical.propDecidable

variable {N : ℕ} [NeZero N] {excluded : Finset ℕ} {threshold : ℕ}

theorem blockList_length (P : Prepared N excluded threshold) (a b : ℕ) :
    (blockList P a b).length≤b := by
  simp only [blockList,List.length_map,Finset.length_toList,Finset.card_attach]
  have hh : (blockSet P a b).card≤(b+2)-(a+2) := by
    exact (card_filter_le _ _).trans_eq (Nat.card_Ico _ _)
  omega

variable (N : ℕ) [NeZero N] (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)

theorem bound_ge_three (j : ℕ) : 3≤bound N hN excluded threshold j := by
  have he : 1≤Real.exp ((preparedPrefix N hN excluded threshold).constant*(4:ℝ)^(j+1)) :=
    Real.one_le_exp_iff.mpr (mul_nonneg (preparedPrefix N hN excluded threshold).constant_pos.le (by positivity))
  unfold bound
  linarith

theorem primes_length (j : ℕ) :
    ((primes N hN excluded threshold j).length:ℝ)≤bound N hN excluded threshold j := by
  have hh : ((primes N hN excluded threshold j).length:ℝ)≤
      (cutoff N hN excluded threshold (j+1):ℝ) := by
    exact_mod_cast blockList_length
      (QuantitativeEulerEndpointPrepared.prepared N hN excluded threshold)
      (cutoff N hN excluded threshold j) (cutoff N hN excluded threshold (j+1))
  have hc := (preparedPrefix N hN excluded threshold).cutoff_size (j+1)
  change (cutoff N hN excluded threshold (j+1):ℝ)+1≤bound N hN excluded threshold j at hc
  linarith

#print axioms primes_length
end QuantitativeEulerEndpointPrimeBlocks
