module

public import AsymptoticOrbitDiagonalV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticOrbitRegion

open AsymptoticOrbitDiagonal ContinuousLinearMap
open scoped lp

variable {G α : Type*} [Group G] [MulAction G α]

theorem corner_norm_le (s : Set α) (x : α) : ‖corner (G:=G) s x‖≤1 :=
  operator_norm_le _ _ _

theorem corner_eq_zero_iff (s : Set α) (x : α) (f : ℓ²(G,ℂ)) :
    corner s x f=0 ↔ ∀ g : G,g • x∈s → f g=0 := by
  classical
  constructor
  · intro he g hg
    have hh := congrArg (fun v : ℓ²(G,ℂ) => v g) he
    simpa only [corner_apply,ite_eq_left hg,lp.coeFn_zero,Pi.zero_apply] using hh
  · intro hf
    apply lp.ext
    funext g
    change corner s x f g=0
    rw [corner_apply]
    by_cases hg : g • x∈s
    · rw [ite_eq_left hg,hf g hg]
    · rw [ite_eq_right hg]

/-- The closed space of terminal counting data for a fixed orbit root. -/
noncomputable def Space (s : Set α) (x : α) : Submodule ℂ ℓ²(G,ℂ) :=
  (corner s x-ContinuousLinearMap.id ℂ _).ker

theorem mem_space (s : Set α) (x : α) (f : ℓ²(G,ℂ)) :
    f∈Space s x ↔ corner s x f=f := by
  change corner s x f-f=0 ↔ _
  exact sub_eq_zero

instance space_complete (s : Set α) (x : α) : CompleteSpace (Space (G:=G) s x) :=
  (corner s x-ContinuousLinearMap.id ℂ _).isClosed_ker.completeSpace_coe

noncomputable def restrict (s : Set α) (x : α) : ℓ²(G,ℂ) →L[ℂ] Space (G:=G) s x :=
  (corner s x).codRestrict (Space s x) (fun f =>
    (mem_space s x _).mpr (congrArg (fun T : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ) => T f) (corner_idempotent s x)))

theorem restrict_coe (s : Set α) (x : α) (f : ℓ²(G,ℂ)) :
    ((restrict s x f : Space s x):ℓ²(G,ℂ))=corner s x f := rfl

#print axioms corner_eq_zero_iff
#print axioms restrict

end AsymptoticOrbitRegion
