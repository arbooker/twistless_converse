module

public import SpanningFailureDimensionDropV1

@[expose] public section

namespace SpanningAdditionSelection

open scoped BigOperators
open Module SpanningTraceAlgebra SpanningAdditionFailure SpanningSlicedAddition

variable {K K':Type*} [Field K] [Field K'] {B L:ℕ} {ζ:K'}

theorem no_shift_failures (I:Type*) [Fintype I] [DecidableEq I]
    (σ:K→+*K') (hB:0<B) (hζ:IsPrimitiveRoot ζ B)
    (V:Submodule K (ℤ→K)) [FiniteDimensional K V]
    (hdim:finrank K V=Fintype.card I) (hpos:0<finrank K V)
    (hcyc:∀v∈V,Cyclic B v) (hzero:∀v∈V,∀n:ℕ,n<L→v n=0)
    (c:I→ℕ) (hcpos:∀i,0<c i) (hcB:∀i,Nat.Coprime (c i) B)
    (hcp:Pairwise (fun i j => Nat.Coprime (c i) (c j)))
    (hsize:Fintype.card I*(∏i,c i)≤L) : ¬∀i,ShiftFailure B (c i) V := by
  classical
  intro hfail
  obtain ⟨W,hWV,hWp,hWlt,s,hs,hfailW⟩ := SpanningFailureDimensionDrop.dimension_drop
    σ hB hζ V hdim hpos hcyc hzero c hcpos hcB hcp hsize hfail
  let : FiniteDimensional K W := Module.Finite.of_injective
    (Submodule.inclusion hWV) (Submodule.inclusion_injective hWV)
  obtain ⟨s',hsub,hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_lt hs)
  let c' : s'→ℕ := fun i => c i.val
  have hdim' : finrank K W=Fintype.card s' := by simpa using hcard.symm
  have hp' : Pairwise (fun i j:s' => Nat.Coprime (c' i) (c' j)) := by
    intro i j hij
    exact hcp (fun he => hij (Subtype.ext he))
  have hprod : (∏i:s',c' i)≤∏i,c i := by
    change (∏i∈s'.attach,c i.val)≤∏i,c i
    rw [Finset.prod_attach]
    exact Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ s')
      (fun i _ _ => Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (hcpos i)))
  have hsize' : Fintype.card s'*(∏i:s',c' i)≤L := by
    apply le_trans (Nat.mul_le_mul ?_ hprod) hsize
    simpa using Finset.card_le_univ s'
  exact no_shift_failures s' σ hB hζ W hdim' hWp
    (fun v hv => hcyc v (hWV hv)) (fun v hv => hzero v (hWV hv))
    c' (fun i => hcpos i.val) (fun i => hcB i.val) hp' hsize'
    (fun i => hfailW i.val (hsub i.property))
termination_by finrank K V
decreasing_by exact hWlt

theorem exists_addition_injective {I:Type*} [Fintype I] [DecidableEq I]
    (σ:K→+*K') (hB:0<B) (hζ:IsPrimitiveRoot ζ B)
    (V:Submodule K (ℤ→K)) [FiniteDimensional K V]
    (hdim:finrank K V=Fintype.card I) (hpos:0<finrank K V)
    (hcyc:∀v∈V,Cyclic B v) (hzero:∀v∈V,∀n:ℕ,n<L→v n=0)
    (c:I→ℕ) (hcpos:∀i,0<c i) (hcB:∀i,Nat.Coprime (c i) B)
    (hcp:Pairwise (fun i j => Nat.Coprime (c i) (c j)))
    (hsize:Fintype.card I*(∏i,c i)≤L) :
    ∃i,AdditionInjective (c i) B (V:Set (ℤ→K)) := by
  classical
  by_contra he
  push Not at he
  exact no_shift_failures I σ hB hζ V hdim hpos hcyc hzero c hcpos hcB hcp hsize
    (fun i => failure_of_not_injective (hcpos i) (hcB i) V hcyc (he i))

#print axioms exists_addition_injective

end SpanningAdditionSelection
