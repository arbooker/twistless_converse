module

public import QuantitativeMaassBandDensityV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace QuantitativeMaass.LogBands

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (l : α → ℝ) (hl : Measurable l)

theorem projection_of_mem_space (n m : ℤ) (f : Lp ℂ 2 μ) (hf : f∈space μ l hl m) :
    projection μ l hl n f=if n=m then f else 0 := by
  classical
  by_cases hnm : n=m
  · subst n
    simpa only [ite_true,projection] using! (AsymptoticRegionL2.mem_space μ _ _ f).mp hf
  · rw [ite_eq_right hnm]
    apply (AsymptoticRegionL2.projection_eq_zero_iff μ _ _ f).mpr
    have hf0 := (AsymptoticRegionL2.projection_eq_self_iff μ _ _ f).mp
      ((AsymptoticRegionL2.mem_space μ _ _ f).mp hf)
    filter_upwards [hf0] with x hx hxn
    exact hx (fun hxm => Set.disjoint_left.mp (region_disjoint l hnm) hxn hxm)

theorem projection_projection (n m : ℤ) (f : Lp ℂ 2 μ) :
    projection μ l hl n (projection μ l hl m f)=if n=m then projection μ l hl m f else 0 :=
  projection_of_mem_space μ l hl n m _ ((AsymptoticRegionL2.mem_space μ _ _ _).mpr
    (AsymptoticRegionL2.projection_idempotent μ _ _ f))

/-- A vector with finitely many nonzero actual band projections is the sum
of those projections. -/
theorem eq_sum_projections (S : Finset ℤ) (f : Lp ℂ 2 μ)
    (hf : ∀ n∉S,projection μ l hl n f=0) : f=∑ n∈S,projection μ l hl n f := by
  classical
  apply sub_eq_zero.mp
  apply projection_separates μ l hl
  intro n
  rw [map_sub,map_sum]
  simp only [projection_projection,Finset.sum_ite_eq]
  by_cases hn : n∈S
  · simp only [hn,ite_true,sub_self]
  · simp only [hn,ite_false,hf n hn,sub_self]

abbrev finiteBandSpace : Submodule ℂ (Lp ℂ 2 μ) := ⨆ n : ℤ,space μ l hl n

/-- Every vector in the algebraic band space has a finite band support. -/
theorem finiteBandSpace_support (f : finiteBandSpace μ l hl) :
    ∃ S : Finset ℤ,∀ n∉S,projection μ l hl n f.val=0 := by
  classical
  refine Submodule.iSup_induction (space μ l hl)
    (motive:=fun g => ∃ S : Finset ℤ,∀ n∉S,projection μ l hl n g=0) f.property ?_ ?_ ?_
  · intro m g hg
    refine ⟨{m},?_⟩
    intro n hn
    have hnm : n≠m := by simpa only [Finset.mem_singleton] using hn
    rw [projection_of_mem_space μ l hl n m g hg,ite_eq_right hnm]
  · exact ⟨∅,fun _ _ => map_zero _⟩
  · intro g h hg hh
    obtain ⟨S,hS⟩ := hg
    obtain ⟨U,hU⟩ := hh
    refine ⟨S∪U,?_⟩
    intro n hn
    have hs : n∉S := fun h => hn (Finset.mem_union_left U h)
    have hu : n∉U := fun h => hn (Finset.mem_union_right S h)
    rw [map_add,hS n hs,hU n hu,add_zero]

theorem mem_finiteBandSpace_of_support (S : Finset ℤ) (f : Lp ℂ 2 μ)
    (hf : ∀ n∉S,projection μ l hl n f=0) : f∈finiteBandSpace μ l hl := by
  rw [eq_sum_projections μ l hl S f hf]
  apply Submodule.sum_mem
  intro n _
  apply (le_iSup (space μ l hl) n)
  exact (AsymptoticRegionL2.mem_space μ _ _ _).mpr
    (AsymptoticRegionL2.projection_idempotent μ _ _ f)

#print axioms projection_of_mem_space
#print axioms projection_projection
#print axioms eq_sum_projections
#print axioms finiteBandSpace_support
#print axioms mem_finiteBandSpace_of_support

end QuantitativeMaass.LogBands
