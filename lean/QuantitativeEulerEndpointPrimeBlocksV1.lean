module

public import QuantitativeEulerEndpointSparsePrefixV1
public import QuantitativeEulerEndpointPrimeListV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrimeBlocks
open Finset QuantitativeEulerEndpointThresholdBlocks QuantitativeEulerEndpointSparsePrefix
open QuantitativeEulerEndpointPrepared QuantitativeEulerDensityGenerators
attribute [local instance] Classical.propDecidable

variable {N : ℕ} [NeZero N] {excluded : Finset ℕ} {threshold : ℕ}

def blockSet (P : Prepared N excluded threshold) (a b : ℕ) : Finset ℕ :=
  (Ico (a+2) (b+2)).filter (fun p => p.Prime ∧ P.Good p)

def blockAt (P : Prepared N excluded threshold) (a b : ℕ)
    (p : {q // q∈blockSet P a b}) : EligiblePrime N :=
  ⟨p.val,(mem_filter.mp p.property).2.1,
    (P.prime_data p.val (mem_filter.mp p.property).2.1 (mem_filter.mp p.property).2.2).2.1⟩

def blockList (P : Prepared N excluded threshold) (a b : ℕ) : List (EligiblePrime N) :=
  (blockSet P a b).attach.toList.map (blockAt P a b)

theorem blockList_nodup (P : Prepared N excluded threshold) (a b : ℕ) :
    (blockList P a b).Nodup := by
  apply List.Nodup.map _ (Finset.nodup_toList _)
  intro p q h
  exact Subtype.ext (congrArg (fun r : EligiblePrime N => r.val) h)

theorem blockList_mem (P : Prepared N excluded threshold) (a b : ℕ)
    (p : EligiblePrime N) (hp : p∈blockList P a b) :
    P.Good p.val ∧ a+2≤p.val ∧ p.val<b+2 := by
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hp
  exact ⟨(mem_filter.mp r.property).2.2,mem_Ico.mp (mem_filter.mp r.property).1⟩

theorem blockList_product (P : Prepared N excluded threshold) (a b : ℕ) :
    ((blockList P a b).map primeFactor).prod=∏ p∈Ico (a+2) (b+2),weight P.Good p := by
  rw [blockList,List.map_map,Finset.prod_map_toList]
  change (∏ p∈(blockSet P a b).attach, (1-(p.val:ℝ)⁻¹))=_
  rw [Finset.prod_attach (blockSet P a b) (fun p : ℕ => 1-(p:ℝ)⁻¹)]
  simp only [blockSet,weight,prod_filter,one_div]

theorem blockList_ratio (P : Prepared N excluded threshold) (a b : ℕ) (hab : a≤b) :
    ((blockList P a b).map primeFactor).prod=value P.Good b/value P.Good a := by
  apply (eq_div_iff (value_pos P.Good a).ne').mpr
  rw [blockList_product,value_eq_range,value_eq_range,mul_comm]
  exact prod_range_mul_prod_Ico (weight P.Good) (by omega)

variable (N : ℕ) [NeZero N] (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)

def cutoff (j : ℕ) : ℕ := (preparedPrefix N hN excluded threshold).cutoff j

def primes (j : ℕ) : List (EligiblePrime N) :=
  blockList (QuantitativeEulerEndpointPrepared.prepared N hN excluded threshold) (cutoff N hN excluded threshold j)
    (cutoff N hN excluded threshold (j+1))

def bound (j : ℕ) : ℝ :=
  3*Real.exp ((preparedPrefix N hN excluded threshold).constant*(4:ℝ)^(j+1))

theorem primes_nodup (j : ℕ) : (primes N hN excluded threshold j).Nodup :=
  blockList_nodup _ _ _

theorem primes_good_bound (j : ℕ) (p : EligiblePrime N)
    (hp : p∈primes N hN excluded threshold j) :
    (QuantitativeEulerEndpointPrepared.prepared N hN excluded threshold).Good p.val ∧ (p.val:ℝ)≤bound N hN excluded threshold j := by
  obtain ⟨hg,_,hb⟩ := blockList_mem _ _ _ p hp
  refine ⟨hg,?_⟩
  have hh : p.val≤cutoff N hN excluded threshold (j+1)+1 := by omega
  have hc : (p.val:ℝ)≤(cutoff N hN excluded threshold (j+1):ℝ)+1 := by exact_mod_cast hh
  exact hc.trans ((preparedPrefix N hN excluded threshold).cutoff_size (j+1))

theorem primes_disjoint (i j : ℕ) (hij : i<j) (p : EligiblePrime N)
    (hp : p∈primes N hN excluded threshold j) : p∉primes N hN excluded threshold i := by
  intro hi
  have h1 := (blockList_mem _ _ _ p hp).2.1
  have h2 := (blockList_mem _ _ _ p hi).2.2
  have hm : cutoff N hN excluded threshold (i+1)≤cutoff N hN excluded threshold j :=
    (preparedPrefix N hN excluded threshold).cutoff_mono hij
  omega

theorem primes_contraction (j : ℕ) :
    ((primes N hN excluded threshold j).map primeFactor).prod≤Real.exp (2/(4:ℝ)^j)/4 := by
  rw [primes,cutoff,cutoff,blockList_ratio _ _ _ ((preparedPrefix N hN excluded threshold).cutoff_mono (Nat.le_succ j))]
  exact (preparedPrefix N hN excluded threshold).block_ratio j

theorem bound_log (j : ℕ) :
    Real.log (bound N hN excluded threshold j)≤
      (Real.log 3+4*(preparedPrefix N hN excluded threshold).constant)*(4:ℝ)^j := by
  rw [bound,Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp,pow_succ]
  have hh := mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1:ℝ)≤4) (n:=j))
    (Real.log_nonneg (by norm_num : (1:ℝ)≤3))
  nlinarith only [hh]

/-- Total threshold-crossing loss, independent of the number of blocks. -/
theorem crossing_loss_sum (n : ℕ) : (∑ j∈range n, 2/(4:ℝ)^j)≤8/3 := by
  have he : (∑ j∈range n, 2/(4:ℝ)^j)=(8/3)*(1-1/(4:ℝ)^n) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [sum_range_succ,ih,pow_succ]
      field_simp
      ring
  rw [he]
  have hh : 0≤1/(4:ℝ)^n := by positivity
  linarith

#print axioms blockList_ratio
#print axioms primes_nodup
#print axioms primes_good_bound
#print axioms primes_disjoint
#print axioms primes_contraction
#print axioms bound_log
#print axioms crossing_loss_sum
end QuantitativeEulerEndpointPrimeBlocks
