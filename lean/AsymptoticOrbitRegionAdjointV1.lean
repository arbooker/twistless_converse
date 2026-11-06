module

public import AsymptoticOrbitRegionV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticOrbitRegion

open AsymptoticOrbitDiagonal ContinuousLinearMap InnerProductSpace
open scoped lp

variable {G α : Type*} [Group G] [MulAction G α]

theorem restrict_eq_adjoint (s : Set α) (x : α) :
    restrict (G:=G) s x=(Space s x).subtypeL.adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  change ⟪corner s x f,(g:ℓ²(G,ℂ))⟫_ℂ=⟪f,(g:ℓ²(G,ℂ))⟫_ℂ
  have hg := (mem_space s x (g:ℓ²(G,ℂ))).mp g.property
  calc
    _ = ⟪f,(corner s x).adjoint (g:ℓ²(G,ℂ))⟫_ℂ := (adjoint_inner_right _ _ _).symm
    _ = _ := by rw [corner_adjoint,hg]

theorem subtype_comp_adjoint (s : Set α) (x : α) :
    (Space (G:=G) s x).subtypeL.comp (Space s x).subtypeL.adjoint=corner s x :=
  congrArg (fun T : ℓ²(G,ℂ) →L[ℂ] Space s x => (Space s x).subtypeL.comp T)
    (restrict_eq_adjoint s x).symm

theorem adjoint_comp_subtype (s : Set α) (x : α) :
    (Space (G:=G) s x).subtypeL.adjoint.comp (Space s x).subtypeL=1 :=
  ((Space s x).subtypeL.norm_map_iff_adjoint_comp_self).mp (fun _ => rfl)

#print axioms restrict_eq_adjoint
#print axioms subtype_comp_adjoint
#print axioms adjoint_comp_subtype

end AsymptoticOrbitRegion
