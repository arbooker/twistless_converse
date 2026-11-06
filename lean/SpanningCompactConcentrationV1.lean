module

public import SpanningClassicalExceptionalV1

set_option autoImplicit false

@[expose] public section

namespace SpanningCompactConcentration

open Set
open scoped BigOperators

/-- Compactness turns local eventual exclusion of defects into uniform
concentration near a finite rational set. The domain is [0,1], so no choice
of a discontinuous circle representative is involved. -/
theorem concentration_of_local_exclusion (D : ℕ → Set ℝ) (F : Finset ℚ)
    (hbound : ∀ a, D a ⊆ Icc 0 1)
    (hlocal : ∀ x ∈ Icc (0:ℝ) 1, (∀ r ∈ F, (r:ℝ)≠x) →
      ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ ∃ n : ℕ, ∀ a ≥ n, Disjoint U (D a)) :
    ∀ ε : ℝ, 0<ε → ∃ n : ℕ, ∀ a ≥ n, ∀ x ∈ D a,
      ∃ r ∈ F, |x-(r:ℝ)|<ε := by
  classical
  intro ε hε
  let V : Set ℝ := ⋃ r ∈ F, Ioo ((r:ℝ)-ε) ((r:ℝ)+ε)
  let C := Icc (0:ℝ) 1 ∩ Vᶜ
  have hV : IsOpen V := isOpen_iUnion (fun _ => isOpen_iUnion (fun _ => isOpen_Ioo))
  have hC : IsCompact C := isCompact_Icc.inter_right hV.isClosed_compl
  have havoid : ∀ x ∈ C, ∀ r ∈ F, (r:ℝ)≠x := by
    intro x hx r hr he
    apply hx.2
    exact mem_iUnion.mpr ⟨r,mem_iUnion.mpr ⟨hr,by rw [← he]; constructor <;> linarith⟩⟩
  have hall : ∀ x : C, ∃ U : Set ℝ, IsOpen U ∧ x.val ∈ U ∧
      ∃ n : ℕ, ∀ a ≥ n, Disjoint U (D a) := fun x =>
    hlocal x.val x.property.1 (havoid x.val x.property)
  choose U hU hxU n hn using hall
  have hcover : C ⊆ ⋃ x : C, U x := fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hxU ⟨x,hx⟩⟩
  obtain ⟨s,hs⟩ := hC.elim_finite_subcover U hU hcover
  refine ⟨∑ x ∈ s,n x,?_⟩
  intro a ha x hx
  by_contra hnot
  have hxV : x ∉ V := by
    intro hxV
    obtain ⟨r,hr⟩ := mem_iUnion.mp hxV
    obtain ⟨hr,hxr⟩ := mem_iUnion.mp hr
    apply hnot
    exact ⟨r,hr,abs_lt.mpr ⟨by linarith [hxr.1],by linarith [hxr.2]⟩⟩
  have hxC : x ∈ C := ⟨hbound a hx,hxV⟩
  obtain ⟨y,hy⟩ := mem_iUnion.mp (hs hxC)
  obtain ⟨hy,hxy⟩ := mem_iUnion.mp hy
  have hna : n y ≤ a := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hy).trans ha
  exact Set.disjoint_left.mp (hn y a hna) hxy hx

#print axioms concentration_of_local_exclusion

end SpanningCompactConcentration
