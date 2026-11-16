module

public import QuantitativeMaassAutomorphicL2V1

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QuantitativeMaass.AutomorphicL2

/-- Restricting the acting group to a subgroup and then taking its whole
invariant space gives the same actual subspace of L² as invariance under
that subgroup of the original ambient group. -/
theorem space_subgroup_top {G A : Type*} [Group G] [MulAction G A]
    [MeasurableSpace A] (H : Subgroup G) (ν : Measure A) :
    space (⊤ : Subgroup H) ν=space H ν := by
  unfold space
  congr 1
  apply Submodule.ext
  intro v
  constructor
  · rintro ⟨f,hf⟩
    let f' : representatives H ν := ⟨f.val,f.property.1,
      (fun g x => f.property.2.1 ⟨g,Subgroup.mem_top g⟩ x),f.property.2.2⟩
    exact ⟨f',hf⟩
  · rintro ⟨f,hf⟩
    let f' : representatives (⊤ : Subgroup H) ν := ⟨f.val,f.property.1,
      (fun g x => f.property.2.1 g.val x),f.property.2.2⟩
    exact ⟨f',hf⟩

#print axioms space_subgroup_top

end QuantitativeMaass.AutomorphicL2
