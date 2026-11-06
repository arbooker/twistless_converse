module

public import AsymptoticRegularIntersectionV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open InnerProductSpace AsymptoticSubspaceIntersection
open scoped InnerProductSpace

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local instance jointTop_complete : CompleteSpace (⊤ : Submodule ℂ E) := by
  change CompleteSpace (Set.univ : Set E)
  exact completeSpace_coe_iff_isComplete.mpr isComplete_univ

/-- Exact intersection projection for two commuting actual projections. -/
theorem inter_projection_of_commute (U V : Submodule ℂ E)
    [CompleteSpace U] [CompleteSpace V] (hc : Commute U.starProjection V.starProjection) :
    (inter U V).starProjection=U.starProjection.comp V.starProjection := by
  apply ContinuousLinearMap.ext
  intro w
  change (inter U V).starProjection w=U.starProjection (V.starProjection w)
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [inter_mem]
    refine ⟨U.starProjection_apply_mem _,?_⟩
    have he := congrArg (fun T : E →L[ℂ] E => T w) hc.eq
    change U.starProjection (V.starProjection w)=V.starProjection (U.starProjection w) at he
    rw [he]
    exact V.starProjection_apply_mem _
  · intro z hz
    obtain ⟨hzU,hzV⟩ := (inter_mem U V z).mp hz
    change ⟪w-U.starProjection (V.starProjection w),z⟫_ℂ=0
    rw [show w-U.starProjection (V.starProjection w)=
      (w-V.starProjection w)+(V.starProjection w-U.starProjection (V.starProjection w)) by abel,
      inner_add_left,V.starProjection_inner_eq_zero w z hzV,
      U.starProjection_inner_eq_zero _ z hzU,add_zero]

theorem inter_projection_distance (U V : Submodule ℂ E)
    [CompleteSpace U] [CompleteSpace V] (hc : Commute U.starProjection V.starProjection) (w : E) :
    ‖w-(inter U V).starProjection w‖^2≤
      ‖w-U.starProjection w‖^2+‖w-V.starProjection w‖^2 := by
  rw [inter_projection_of_commute U V hc]
  have he : w-U.starProjection (V.starProjection w)=
      (w-U.starProjection w)+U.starProjection (w-V.starProjection w) := by
    rw [map_sub]
    abel
  change ‖w-U.starProjection (V.starProjection w)‖^2≤_
  rw [he,norm_add_sq (𝕜:=ℂ),U.starProjection_inner_eq_zero w _ (U.starProjection_apply_mem _)]
  simp only [map_zero,mul_zero,add_zero]
  exact add_le_add_right (pow_le_pow_left₀ (norm_nonneg _)
    (U.norm_starProjection_apply_le _) 2) _

def jointListSpace (V : ι → Submodule ℂ E) (l : List ι) : Submodule ℂ E :=
  ⨅ i∈l,V i

instance jointListSpace_complete (V : ι → Submodule ℂ E) [∀ i,CompleteSpace (V i)]
    (l : List ι) : CompleteSpace (jointListSpace V l) := by
  have hc : IsClosed (jointListSpace V l : Set E) := by
    simp only [jointListSpace,Submodule.coe_iInf]
    exact isClosed_iInter (fun i => isClosed_iInter (fun _ =>
      (completeSpace_coe_iff_isComplete.mp (inferInstance : CompleteSpace (V i))).isClosed))
  exact hc.completeSpace_coe

omit [CompleteSpace E] in
theorem jointListSpace_mem (V : ι → Submodule ℂ E)
    (l : List ι) (w : E) : w∈jointListSpace V l ↔ ∀ i∈l,w∈V i := by
  simp only [jointListSpace,Submodule.mem_iInf]

omit [CompleteSpace E] in
theorem jointListSpace_nil (V : ι → Submodule ℂ E) : jointListSpace V []=⊤ := by
  simp [jointListSpace]

theorem jointListSpace_cons (V : ι → Submodule ℂ E) [∀ i,CompleteSpace (V i)]
    (i : ι) (l : List ι) : jointListSpace V (i::l)=inter (V i) (jointListSpace V l) := by
  ext w
  simp only [jointListSpace_mem,inter_mem,List.mem_cons,forall_eq_or_imp]

theorem jointListSpace_projection (V : ι → Submodule ℂ E) [∀ i,CompleteSpace (V i)]
    (hc : ∀ i j,Commute (V i).starProjection (V j).starProjection) (l : List ι) :
    (jointListSpace V l).starProjection=(l.map fun i => (V i).starProjection).prod := by
  induction l with
  | nil =>
    rw [AsymptoticPolarIsometry.starProjection_congr _ _ (jointListSpace_nil V),Submodule.starProjection_top]
    rfl
  | cons i l ih =>
    have hcomm : Commute (V i).starProjection (jointListSpace V l).starProjection := by
      rw [ih]
      apply Commute.list_prod_right
      intro T hT
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hT
      exact hc i j
    rw [AsymptoticPolarIsometry.starProjection_congr _ _ (jointListSpace_cons V i l),
      inter_projection_of_commute _ _ hcomm,ih]
    rfl

/-- Commuting local constraints give an additive distance estimate for
their literal finite intersection, without a joint-gap assumption. -/
theorem jointListSpace_distance (V : ι → Submodule ℂ E) [∀ i,CompleteSpace (V i)]
    (hc : ∀ i j,Commute (V i).starProjection (V j).starProjection) (l : List ι) (w : E) :
    ‖w-(jointListSpace V l).starProjection w‖^2≤
      (l.map fun i => ‖w-(V i).starProjection w‖^2).sum := by
  induction l with
  | nil =>
    rw [AsymptoticPolarIsometry.starProjection_congr _ _ (jointListSpace_nil V),Submodule.starProjection_top]
    simp
  | cons i l ih =>
    have hcomm : Commute (V i).starProjection (jointListSpace V l).starProjection := by
      rw [jointListSpace_projection V hc]
      apply Commute.list_prod_right
      intro T hT
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hT
      exact hc i j
    rw [AsymptoticPolarIsometry.starProjection_congr _ _ (jointListSpace_cons V i l)]
    exact (inter_projection_distance (V i) (jointListSpace V l) hcomm w).trans
      (add_le_add_right ih _)

#print axioms inter_projection_of_commute
#print axioms inter_projection_distance
#print axioms jointListSpace_projection
#print axioms jointListSpace_distance

end QuantitativeNewGap
