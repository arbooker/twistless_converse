module

public import SpanningAdditionSelectionV1

@[expose] public section

namespace SpanningTwoAdditionSelection

open scoped BigOperators
open Module SpanningTraceAlgebra SpanningSlicedAddition

variable {K K':Type*} [Field K] [Field K'] {B L:ℕ} {ζ:K'}

theorem exists_injective_from_many {I:Type*} [Fintype I] [DecidableEq I]
    (σ:K→+*K') (hB:0<B) (hζ:IsPrimitiveRoot ζ B)
    (V:Submodule K (ℤ→K)) [FiniteDimensional K V]
    (hdim:finrank K V≤Fintype.card I) (hpos:0<finrank K V)
    (hcyc:∀v∈V,Cyclic B v) (hzero:∀v∈V,∀n:ℕ,n<L→v n=0)
    (c:I→ℕ) (hcpos:∀i,0<c i) (hcB:∀i,Nat.Coprime (c i) B)
    (hcp:Pairwise (fun i j => Nat.Coprime (c i) (c j)))
    (hsize:finrank K V*(∏i,c i)≤L) :
    ∃i,AdditionInjective (c i) B (V:Set (ℤ→K)) := by
  classical
  obtain ⟨s,_,hs⟩ := Finset.exists_subset_card_eq
    (show finrank K V≤(Finset.univ:Finset I).card by simpa using hdim)
  have hprod : (∏i:s,c i.val)≤∏i,c i := by
    change (∏i∈s.attach,c i.val)≤∏i,c i
    rw [Finset.prod_attach]
    exact Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ s)
      (fun i _ _ => Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (hcpos i)))
  obtain ⟨i,hi⟩ := SpanningAdditionSelection.exists_addition_injective σ hB hζ V
    (show finrank K V=Fintype.card s by simpa using hs.symm) hpos hcyc hzero
    (fun i:s => c i.val) (fun i => hcpos i.val) (fun i => hcB i.val)
    (fun i j hij => hcp (fun he => hij (Subtype.ext he)))
    (show Fintype.card s*(∏i:s,c i.val)≤L by
      rw [Fintype.card_coe,hs]
      exact (Nat.mul_le_mul_left _ hprod).trans hsize)
  exact ⟨i.val,hi⟩

theorem exists_two_injective {I:Type*} [Fintype I] [DecidableEq I]
    (σ:K→+*K') (hB:0<B) (hζ:IsPrimitiveRoot ζ B)
    (V:Submodule K (ℤ→K)) [FiniteDimensional K V]
    (hdim:finrank K V<Fintype.card I) (hpos:0<finrank K V)
    (hcyc:∀v∈V,Cyclic B v) (hzero:∀v∈V,∀n:ℕ,n<L→v n=0)
    (c:I→ℕ) (hcpos:∀i,0<c i) (hcB:∀i,Nat.Coprime (c i) B)
    (hcp:Pairwise (fun i j => Nat.Coprime (c i) (c j)))
    (hsize:finrank K V*(∏i,c i)≤L) :
    ∃i j,i≠j ∧ AdditionInjective (c i) B (V:Set (ℤ→K)) ∧
      AdditionInjective (c j) B (V:Set (ℤ→K)) := by
  classical
  obtain ⟨i,hi⟩ := exists_injective_from_many σ hB hζ V hdim.le hpos hcyc hzero
    c hcpos hcB hcp hsize
  let s := (Finset.univ:Finset I).erase i
  have hcard : finrank K V≤Fintype.card s := by
    simp only [Fintype.card_coe,s,Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ]
    omega
  have hprod : (∏j:s,c j.val)≤∏j,c j := by
    change (∏j∈s.attach,c j.val)≤∏j,c j
    rw [Finset.prod_attach]
    exact Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ s)
      (fun j _ _ => Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (hcpos j)))
  obtain ⟨j,hj⟩ := exists_injective_from_many σ hB hζ V hcard hpos hcyc hzero
    (fun j:s => c j.val) (fun j => hcpos j.val) (fun j => hcB j.val)
    (fun j k hjk => hcp (fun he => hjk (Subtype.ext he)))
    ((Nat.mul_le_mul_left _ hprod).trans hsize)
  exact ⟨i,j.val,(Finset.mem_erase.mp j.property).1.symm,hi,hj⟩

#print axioms exists_two_injective

end SpanningTwoAdditionSelection
