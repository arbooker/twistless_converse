module

public import AsymptoticCongruenceOldTraceV1
public import AsymptoticCongruenceOldMeetV1
public import AsymptoticRegularTwoOldTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public section

namespace AsymptoticCongruenceOldSpace

open UpperHalfPlane MeasureTheory AsymptoticCongruenceStrip AsymptoticCongruenceQuotient
open AsymptoticRegularTrace AsymptoticSubspaceIntersection AsymptoticPolarIsometry
open scoped lp ENNReal

variable (N : ℕ) (J K : Subgroup AsymptoticRationalGroup.Group)
variable (hJ : gamma N≤J) (hK : gamma N≤K)
variable [Finite (J ⧸ (gamma N).subgroupOf J)] [Finite (K ⧸ (gamma N).subgroupOf K)]
variable {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)

/-- The actual quotient corner orthogonal to both specified old ranges. -/
noncomputable def newSpace (z : ℍ) : Submodule ℂ ℓ²(AsymptoticRationalGroup.Group,ℂ) :=
  AsymptoticTwoOldSubspaces.newSpace (quotientSpace N hε ht z)
    (space N J hJ hε ht z) (space N K hK hε ht z)

noncomputable instance newSpace_complete (z : ℍ) : CompleteSpace (newSpace N J K hJ hK hε ht z) :=
  inferInstanceAs (CompleteSpace (AsymptoticTwoOldSubspaces.newSpace (quotientSpace N hε ht z)
    (space N J hJ hε ht z) (space N K hK hε ht z)))

theorem new_trace_with_intersection (hN : 0<N) :
    (trace volume (fun z => (newSpace N J K hJ hK hε ht z).starProjection)).toReal=
      (trace volume (projection N hε ht)).toReal-
      (trace volume (projection N hε ht)).toReal/(((gamma N).subgroupOf J).index:ℝ)-
      (trace volume (projection N hε ht)).toReal/(((gamma N).subgroupOf K).index:ℝ)+
      (trace volume (fun z => (inter (space N K hK hε ht z) (space N J hJ hε ht z)).starProjection)).toReal := by
  have he := two_old_trace volume AsymptoticRationalGroup.measurePreserving
    (quotientSpace N hε ht) (space N J hJ hε ht) (space N K hK hε ht)
    (space_le_quotient N J hJ hε ht) (space_le_quotient N K hK hε ht)
    (AsymptoticCongruenceQuotient.projection_matrix_measurable N hε ht)
    (projection_matrix_measurable N J hJ hε ht) (projection_matrix_measurable N K hK hε ht)
    (AsymptoticCongruenceQuotient.projection_covariant N hε ht)
    (projection_covariant N J hJ hε ht) (projection_covariant N K hK hε ht)
    (AsymptoticCongruenceQuotient.projection_trace_finite N hN hε ht)
  have hQ : trace volume (fun x => (quotientSpace N hε ht x).starProjection)=
      trace volume (projection N hε ht) := rfl
  rw [hQ] at he
  simpa only [projection_trace_toReal,newSpace] using he

/-- Finite generated overgroup: inclusion-exclusion for the two old
directions, including the precise reciprocal-index correction. -/
theorem new_trace_finite_join [Finite (↥(J⊔K) ⧸ (gamma N).subgroupOf (J⊔K))] (hN : 0<N) :
    (trace volume (fun z => (newSpace N J K hJ hK hε ht z).starProjection)).toReal=
      (trace volume (projection N hε ht)).toReal*
        (1-(((gamma N).subgroupOf J).index:ℝ)⁻¹-(((gamma N).subgroupOf K).index:ℝ)⁻¹+
          (((gamma N).subgroupOf (J⊔K)).index:ℝ)⁻¹) := by
  have hi (z : ℍ) : inter (space N K hK hε ht z) (space N J hJ hε ht z)=
      space N (J⊔K) (hJ.trans le_sup_left) hε ht z := by
    rw [space_sup N J K hJ hK hε ht z]
    ext v
    rw [inter_mem,Submodule.mem_inf]
    exact and_comm
  rw [new_trace_with_intersection N J K hJ hK hε ht hN]
  simp only [starProjection_congr _ _ (hi _),projection_trace_toReal,div_eq_mul_inv]
  ring

/-- Infinite generated overgroup: the intersection correction vanishes. -/
theorem new_trace_infinite_join [Infinite (↥(J⊔K) ⧸ (gamma N).subgroupOf (J⊔K))] (hN : 0<N) :
    (trace volume (fun z => (newSpace N J K hJ hK hε ht z).starProjection)).toReal=
      (trace volume (projection N hε ht)).toReal*
        (1-(((gamma N).subgroupOf J).index:ℝ)⁻¹-(((gamma N).subgroupOf K).index:ℝ)⁻¹) := by
  have hi (z : ℍ) : inter (space N K hK hε ht z) (space N J hJ hε ht z)=⊥ := by
    have he : inter (space N K hK hε ht z) (space N J hJ hε ht z)=
        space N J hJ hε ht z⊓space N K hK hε ht z := by
      ext v
      rw [inter_mem,Submodule.mem_inf]
      exact and_comm
    exact he.trans (space_inf_eq_bot N J K hJ hK hε ht z)
  rw [new_trace_with_intersection N J K hJ hK hε ht hN]
  have hz : trace volume (fun z =>
      (inter (space N K hK hε ht z) (space N J hJ hε ht z)).starProjection)=0 := by
    simp only [starProjection_congr _ _ (hi _),Submodule.starProjection_bot]
    simp [trace,matrix]
  rw [hz,ENNReal.toReal_zero,add_zero]
  simp only [div_eq_mul_inv]
  ring

#print axioms new_trace_with_intersection
#print axioms new_trace_finite_join
#print axioms new_trace_infinite_join

end AsymptoticCongruenceOldSpace
