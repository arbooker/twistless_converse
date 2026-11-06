module

public import AsymptoticCongruenceOldSpaceV1
public import AsymptoticQuotientInvariantsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCongruenceOldSpace

open UpperHalfPlane AsymptoticCongruenceStrip AsymptoticCongruenceQuotient
open scoped lp

variable (N : ℕ) (J K : Subgroup AsymptoticRationalGroup.Group)
variable (hJ : gamma N≤J) (hK : gamma N≤K)
variable [Finite (J ⧸ (gamma N).subgroupOf J)] [Finite (K ⧸ (gamma N).subgroupOf K)]
variable {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)

/-- Intersection of the old ranges is invariance under the generated
overgroup. This is an exact subspace identity, not just a trace bound. -/
theorem space_sup [Finite (↥(J⊔K) ⧸ (gamma N).subgroupOf (J⊔K))] (z : ℍ) :
    space N (J⊔K) (hJ.trans le_sup_left) hε ht z=
      space N J hJ hε ht z⊓space N K hK hε ht z := by
  ext v
  rw [Submodule.mem_inf,space_mem,space_mem,space_mem]
  have he := AsymptoticNestedQuotients.invariant_sup_iff (fun g => coordinate N ε t z g v) J K
  rw [he]
  exact ⟨fun h => ⟨⟨h.1,h.2.1⟩,⟨h.1,h.2.2⟩⟩,
    fun h => ⟨h.1.1,h.1.2,h.2.2⟩⟩

/-- The two old directions have zero intersection if the generated
overgroup has infinite relative index, as occurs at exponent one. -/
theorem space_inf_eq_bot [Infinite (↥(J⊔K) ⧸ (gamma N).subgroupOf (J⊔K))] (z : ℍ) :
    space N J hJ hε ht z⊓space N K hK hε ht z=⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  have hj := (space_mem N J hJ hε ht z v).mp hv.1
  have hk := (space_mem N K hK hε ht z v).mp hv.2
  have hi := (AsymptoticNestedQuotients.invariant_sup_iff
    (fun g => coordinate N ε t z g v) J K).mpr ⟨hj.2,hk.2⟩
  obtain ⟨u,hu⟩ := hj.1
  change AsymptoticCongruenceQuotient.induction N hε ht z u=v at hu
  rw [← hu] at hi
  simp only [coordinate_induction] at hi
  have hz := AsymptoticNestedQuotients.invariant_zero_of_infinite
    (hJ.trans (le_sup_left : J≤J⊔K)) u hi
  change v=0
  rw [← hu,hz,map_zero]

#print axioms space_sup
#print axioms space_inf_eq_bot

end AsymptoticCongruenceOldSpace
