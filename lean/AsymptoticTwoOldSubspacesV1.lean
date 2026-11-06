module

public import AsymptoticRegularIntersectionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticTwoOldSubspaces

open ContinuousLinearMap AsymptoticCornerKernel AsymptoticSubspaceIntersection
open AsymptoticPolarIsometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def relativeComplement (S U : Submodule ℂ H) [CompleteSpace U] : Submodule ℂ H :=
  remaining S U.starProjection

noncomputable instance relativeComplement_complete (S U : Submodule ℂ H)
    [CompleteSpace S] [CompleteSpace U] : CompleteSpace (relativeComplement S U) :=
  inferInstanceAs (CompleteSpace (remaining S U.starProjection))

noncomputable def newSpace (S U V : Submodule ℂ H) [CompleteSpace U] [CompleteSpace V] :
    Submodule ℂ H := remaining (relativeComplement S U) V.starProjection

noncomputable instance newSpace_complete (S U V : Submodule ℂ H)
    [CompleteSpace S] [CompleteSpace U] [CompleteSpace V] : CompleteSpace (newSpace S U V) :=
  inferInstanceAs (CompleteSpace (remaining (relativeComplement S U) V.starProjection))

theorem relativeComplement_projection (S U : Submodule ℂ H)
    [CompleteSpace S] [CompleteSpace U] (hU : U≤S) :
    (relativeComplement S U).starProjection=S.starProjection-U.starProjection := by
  have he := remaining_projection S U.starProjection
    (Submodule.starProjection_comp_starProjection_of_le hU)
  have hk : U.starProjection.kerᗮ=U := by
    rw [Submodule.ker_starProjection,Submodule.orthogonal_orthogonal]
  rw [starProjection_congr _ _ hk] at he
  exact he

theorem remaining_complement_eq_inter (S U V : Submodule ℂ H)
    [CompleteSpace S] [CompleteSpace U] [CompleteSpace V] (hU : U≤S) (hV : V≤S) :
    remaining V ((relativeComplement S U).starProjection.comp V.starProjection)=inter V U := by
  rw [remaining_restricted]
  ext v
  rw [inter_mem]
  change (v∈V ∧ (relativeComplement S U).starProjection v=0) ↔ v∈V ∧ v∈U
  constructor
  · rintro ⟨hv,hz⟩
    rw [relativeComplement_projection S U hU,sub_apply,S.starProjection_eq_self_iff.mpr (hV hv)] at hz
    exact ⟨hv,U.starProjection_eq_self_iff.mp (sub_eq_zero.mp hz).symm⟩
  · rintro ⟨hv,hu⟩
    refine ⟨hv,?_⟩
    rw [relativeComplement_projection S U hU,sub_apply,S.starProjection_eq_self_iff.mpr (hV hv),
      U.starProjection_eq_self_iff.mpr hu,sub_self]

theorem adjoint_complement (S U V : Submodule ℂ H)
    [CompleteSpace S] [CompleteSpace U] [CompleteSpace V] :
    ((relativeComplement S U).starProjection.comp V.starProjection).adjoint=
      V.starProjection.comp (relativeComplement S U).starProjection := by
  have hV : V.starProjection.adjoint=V.starProjection := isSelfAdjoint_starProjection V
  have hL : (relativeComplement S U).starProjection.adjoint=(relativeComplement S U).starProjection :=
    isSelfAdjoint_starProjection (relativeComplement S U)
  rw [adjoint_comp,hV,hL]

theorem remaining_adjoint_eq_new (S U V : Submodule ℂ H)
    [CompleteSpace S] [CompleteSpace U] [CompleteSpace V] :
    remaining (relativeComplement S U)
      ((relativeComplement S U).starProjection.comp V.starProjection).adjoint=newSpace S U V := by
  rw [adjoint_complement,remaining_restricted]
  rfl

#print axioms relativeComplement_projection
#print axioms remaining_complement_eq_inter
#print axioms adjoint_complement
#print axioms remaining_adjoint_eq_new

end AsymptoticTwoOldSubspaces
