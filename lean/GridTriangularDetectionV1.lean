module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Max

@[expose] public section

namespace GridTriangularDetection

variable {I K : Type*} [Fintype I] [AddCommMonoid K]

/-- Unit triangular incidence rows detect a supported vector in every
characteristic; no determinant or division is needed. -/
theorem triangular_detect (rank : I → ℕ) (hit : I → Finset I)
    (hdiag : ∀i,i∈hit i)
    (hupper : ∀i j,j∈hit i → j≠i → rank i<rank j)
    (v : I → K) (hz : ∀i,∑j∈hit i,v j=0) : v=0 := by
  classical
  by_contra hn
  have hex : ∃i,v i≠0 := by
    by_contra! he
    exact hn (funext he)
  obtain ⟨i₀,hi₀⟩ := hex
  have hs : ((Finset.univ : Finset I).filter (fun i => v i≠0)).Nonempty :=
    ⟨i₀,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi₀⟩⟩
  obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image _ rank hs
  have hi0 : v i≠0 := (Finset.mem_filter.mp hi).2
  have hsum : ∑j∈hit i,v j=v i := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      by_contra hj0
      have hjmem : j∈(Finset.univ.filter (fun i => v i≠0)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ j,hj0⟩
      exact (not_lt_of_ge (hmax j hjmem)) (hupper i j hj hji)
    · exact fun h => False.elim (h (hdiag i))
  exact hi0 (hsum.symm.trans (hz i))

/-- The same argument above a threshold leaves low-order labels for
separate special rows. -/
theorem triangular_detect_above (rank : I → ℕ) (T : ℕ) (hit : I → Finset I)
    (hdiag : ∀i,T<rank i → i∈hit i)
    (hupper : ∀i,T<rank i → ∀j,j∈hit i → j≠i → rank i<rank j)
    (v : I → K) (hz : ∀i,T<rank i → ∑j∈hit i,v j=0) :
    ∀i,T<rank i → v i=0 := by
  classical
  by_contra! hn
  obtain ⟨i,hi,hiv⟩ := hn
  let S := (Finset.univ : Finset I).filter (fun i => T<rank i ∧ v i≠0)
  have hs : S.Nonempty := ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,hiv⟩⟩
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image S rank hs
  have hj0 := (Finset.mem_filter.mp hj).2
  have hsum : ∑i∈hit j,v i=v j := by
    apply Finset.sum_eq_single j
    · intro k hk hkj
      by_contra hk0
      have hjk := hupper j hj0.1 k hk hkj
      have hkmem : k∈S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj0.1.trans hjk,hk0⟩
      exact (not_lt_of_ge (hmax k hkmem)) hjk
    · exact fun h => False.elim (h (hdiag j hj0.1))
  exact hj0.2 (hsum.symm.trans (hz j hj0.1))

#print axioms triangular_detect
#print axioms triangular_detect_above

end GridTriangularDetection
