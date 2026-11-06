module

public import AsymptoticOvergroupIsometryV1
public import AsymptoticFiniteFiberAverageV1
public import AsymptoticCongruenceOldSpaceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticNestedQuotients

open scoped lp

variable {G : Type*} [Group G]
variable {H J : Subgroup G} (h : H≤J) [Finite (J ⧸ H.subgroupOf J)]

theorem projection_eq_fibre : (space h).starProjection=
    AsymptoticFiniteFiberInduction.projection (forget h) (H.subgroupOf J).index
      index_pos (fibre_card h) :=
  (AsymptoticFiberIsometry.operator_cogram (forget h)
    (fun _ => AsymptoticFiniteFiberInduction.coefficient (H.subgroupOf J).index)
    (AsymptoticFiniteFiberInduction.fibre_hasSum (forget h) (H.subgroupOf J).index
      index_pos (fibre_card h))).symm

theorem projection_apply (f : ℓ²(Classes H,ℂ)) (q : Classes H) :
    (space h).starProjection f q=(((H.subgroupOf J).index:ℂ)⁻¹)*
      (∑' r : {r // forget h r=forget h q},f r.val) := by
  rw [projection_eq_fibre,AsymptoticFiniteFiberInduction.projection_apply]

theorem projection_eq_zero_iff (f : ℓ²(Classes H,ℂ)) :
    (space h).starProjection f=0 ↔ ∀ y,(∑' q : {q // forget h q=y},f q.val)=0 := by
  rw [projection_eq_fibre,AsymptoticFiniteFiberInduction.projection_eq_zero_iff]

#print axioms projection_eq_fibre
#print axioms projection_apply
#print axioms projection_eq_zero_iff

end AsymptoticNestedQuotients

namespace AsymptoticCongruenceOldSpace

open UpperHalfPlane ContinuousLinearMap AsymptoticCongruenceStrip
open scoped lp

variable (N : ℕ) (J : Subgroup AsymptoticRationalGroup.Group) (hJ : gamma N≤J)
variable [Finite (J ⧸ (gamma N).subgroupOf J)]
variable {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)

theorem projection_induction (z : ℍ) (f : ℓ²(AsymptoticCongruenceQuotient.Classes N,ℂ)) :
    (space N J hJ hε ht z).starProjection (AsymptoticCongruenceQuotient.induction N hε ht z f)=
      AsymptoticCongruenceQuotient.induction N hε ht z ((AsymptoticNestedQuotients.space hJ).starProjection f) := by
  have he := AsymptoticIsometryRange.cogram_comp
    (AsymptoticCongruenceQuotient.induction N hε ht z) (AsymptoticNestedQuotients.isometry hJ)
  change (space N J hJ hε ht z).starProjection=_ at he
  rw [he]
  change AsymptoticCongruenceQuotient.induction N hε ht z
    ((AsymptoticNestedQuotients.space hJ).starProjection
      ((AsymptoticCongruenceQuotient.induction N hε ht z).toContinuousLinearMap.adjoint
        (AsymptoticCongruenceQuotient.induction N hε ht z f)))=_
  have ha := congrArg (fun T : ℓ²(AsymptoticCongruenceQuotient.Classes N,ℂ) →L[ℂ]
      ℓ²(AsymptoticCongruenceQuotient.Classes N,ℂ) => T f)
    (AsymptoticCongruenceQuotient.induction N hε ht z).adjoint_comp_self
  change (AsymptoticCongruenceQuotient.induction N hε ht z).toContinuousLinearMap.adjoint
    (AsymptoticCongruenceQuotient.induction N hε ht z f)=f at ha
  rw [ha]

/-- Old-trace annihilation in the weighted strip model is exactly the
vanishing of the finite, unweighted coset sums. -/
theorem projection_induction_eq_zero_iff (z : ℍ)
    (f : ℓ²(AsymptoticCongruenceQuotient.Classes N,ℂ)) :
    (space N J hJ hε ht z).starProjection (AsymptoticCongruenceQuotient.induction N hε ht z f)=0 ↔
      ∀ y,(∑' q : {q // AsymptoticNestedQuotients.forget hJ q=y},f q.val)=0 := by
  rw [projection_induction]
  have he : AsymptoticCongruenceQuotient.induction N hε ht z
      ((AsymptoticNestedQuotients.space hJ).starProjection f)=0 ↔
      (AsymptoticNestedQuotients.space hJ).starProjection f=0 := by
    rw [← (AsymptoticCongruenceQuotient.induction N hε ht z).map_zero]
    exact (AsymptoticCongruenceQuotient.induction N hε ht z).injective.eq_iff
  rw [he,AsymptoticNestedQuotients.projection_eq_zero_iff]

#print axioms projection_induction
#print axioms projection_induction_eq_zero_iff

end AsymptoticCongruenceOldSpace
