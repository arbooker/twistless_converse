module

public import GridCarrierV1

@[expose] public section

namespace GridRestrictedRows

open CompleteRowCosets GridCarrier SpanningTraceAlgebra

noncomputable def restrictedSum {I K : Type*} [Fintype I] [AddCommMonoid K]
    (p : I → Prop) (f : I → K) : K := by
  classical
  exact ∑i,if p i then f i else 0

theorem cosetSum_eq_restricted {K : Type*} [AddCommMonoid K]
    (Q D : ℕ) (u : ℤ) (v : ℤ → K) :
    cosetSum Q D u v=restrictedSum (fun j:Fin Q => Int.ModEq D j.val u) (fun j => v j.val) := by
  classical
  unfold cosetSum restrictedSum
  exact Fintype.sum_of_injective Subtype.val Subtype.val_injective _ _
    (by intro j hj; simp only [Set.mem_range,Subtype.exists,exists_prop,exists_eq_right] at hj
        simp [hj])
    (by intro j; simp [j.property])

theorem restrictedSum_on_carrier {I A K : Type*} [Fintype I] [Fintype A] [AddCommMonoid K]
    (e : A → I) (he : Function.Injective e) (p : I → Prop) (f : I → K)
    (hf : ∀i,i∉Set.range e → f i=0) :
    restrictedSum p f=restrictedSum (fun a => p (e a)) (fun a => f (e a)) := by
  classical
  unfold restrictedSum
  symm
  exact Fintype.sum_of_injective e he _ _
    (by intro i hi; simp [hf i hi]) (by intro a; rfl)

theorem grid_coset_sum {K : Type*} [AddCommMonoid K] {G v J D : ℕ}
    (hG : 0<G) (hv : 0<v) (hJ : 2*J<v) (u : ℤ) (f : ℤ → K)
    (hf : ∀j:Fin (G*v),j∉Set.range (gridIndex hG hv J) → f j.val=0) :
    cosetSum (G*v) D u f=
      restrictedSum (fun x:Fin G × Offsets J => Int.ModEq D (gridIndex hG hv J x).val u)
        (fun x => f (gridIndex hG hv J x).val) := by
  rw [cosetSum_eq_restricted]
  exact restrictedSum_on_carrier _ (gridIndex_injective hG hv hJ) _ _ hf

#print axioms grid_coset_sum

end GridRestrictedRows
