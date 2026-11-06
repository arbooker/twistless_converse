module

public import AsymptoticRegularCutDimensionV1
public import AsymptoticOrbitRegionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCoordinateCut

open MeasureTheory ContinuousLinearMap InnerProductSpace AsymptoticRegularTrace
open AsymptoticCornerKernel AsymptoticOrbitDiagonal
open scoped lp InnerProduct

variable {G α : Type*} [Group G] [MulAction G α]

noncomputable def cutSpace (U : Submodule ℂ ℓ²(G,ℂ)) (s : Set α) (x : α) :
    Submodule ℂ ℓ²(G,ℂ) := remaining U (1-corner s x)

noncomputable instance cutSpace_complete (U : Submodule ℂ ℓ²(G,ℂ)) [CompleteSpace U]
    (s : Set α) (x : α) : CompleteSpace (cutSpace U s x) :=
  inferInstanceAs (CompleteSpace (remaining U (1-corner s x)))

theorem cutSpace_mem (U : Submodule ℂ ℓ²(G,ℂ)) (s : Set α) (x : α) (v : ℓ²(G,ℂ)) :
    v∈cutSpace U s x ↔ v∈U ∧ corner s x v=v := by
  change (v∈U ∧ v-corner s x v=0) ↔ _
  constructor
  · rintro ⟨hu,hv⟩
    exact ⟨hu,(sub_eq_zero.mp hv).symm⟩
  · rintro ⟨hu,hv⟩
    exact ⟨hu,sub_eq_zero.mpr hv.symm⟩

theorem complement_norm_le (s : Set α) (x : α) :
    ‖(1:ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))-corner s x‖≤2 := by
  have he := AsymptoticOrbitRegion.corner_norm_le (G:=G) s x
  have h1 : ‖(1:ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))‖≤1 := by
    apply opNorm_le_bound _ zero_le_one
    intro v
    simp
  exact (norm_sub_le _ _).trans (by linarith)

/-- On a subspace preserved by a coordinate cut, the cut projection
is the coordinate multiplier composed with the original projection. -/
theorem cutSpace_projection (U : Submodule ℂ ℓ²(G,ℂ)) [CompleteSpace U]
    (s : Set α) (x : α) (hU : ∀ v∈U,corner s x v∈U) :
    (cutSpace U s x).starProjection=(corner s x).comp U.starProjection := by
  apply ContinuousLinearMap.ext
  intro v
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · apply (cutSpace_mem U s x _).mpr
    refine ⟨hU _ (U.starProjection_apply_mem v),?_⟩
    exact congrArg (fun B : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ) => B (U.starProjection v))
      (corner_idempotent s x)
  · intro w hw
    obtain ⟨hw,hew⟩ := (cutSpace_mem U s x w).mp hw
    change ⟪v-corner s x (U.starProjection v),w⟫_ℂ=0
    rw [inner_sub_left,← (corner s x).adjoint_inner_right,corner_adjoint,hew,
      Submodule.inner_starProjection_left_eq_right,U.starProjection_eq_self_iff.mpr hw,sub_self]

theorem cutSpace_root (U : Submodule ℂ ℓ²(G,ℂ)) [CompleteSpace U]
    (s : Set α) (x : α) (hU : ∀ v∈U,corner s x v∈U) :
    matrix (cutSpace U s x).starProjection 1 1=
      s.indicator (fun _ => matrix U.starProjection 1 1) x := by
  classical
  rw [cutSpace_projection U s x hU]
  simp only [matrix,comp_apply,corner_apply,one_smul,Set.indicator_apply]

variable [Countable G] [MeasurableSpace α]

theorem cutSpace_regular (hact : ∀ g : G,Measurable (fun x : α => g • x))
    (U : α → Submodule ℂ ℓ²(G,ℂ)) [∀ x,CompleteSpace (U x)]
    (hmU : ∀ g h,Measurable (fun x => matrix (U x).starProjection g h))
    (hcU : Covariant (fun x => (U x).starProjection))
    (s : Set α) (hs : MeasurableSet s) :
    (∀ g h,Measurable (fun x => matrix (cutSpace (U x) s x).starProjection g h)) ∧
      Covariant (fun x => (cutSpace (U x) s x).starProjection) :=
  remaining_regular U hmU hcU (fun x => 1-corner s x)
    (matrix_sub_measurable _ _ (fun _ _ => measurable_const) (corner_matrix_measurable hact hs))
    (covariant_sub _ _ covariant_one (corner_covariant s)) 2 (complement_norm_le s)

#print axioms cutSpace_mem
#print axioms complement_norm_le
#print axioms cutSpace_projection
#print axioms cutSpace_root
#print axioms cutSpace_regular

end AsymptoticCoordinateCut
