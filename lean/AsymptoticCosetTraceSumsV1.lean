module

public import AsymptoticOvergroupAverageV1
public import AsymptoticTranslatedCosetFiberV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticNestedQuotients

open scoped lp

variable {G : Type*} [Group G] {H J : Subgroup G} (h : H≤J)
variable {ι : Type*} [Fintype ι] (r : ι → J)
variable (e : ι ≃ (J ⧸ H.subgroupOf J)) (he : ∀ i,e i=QuotientGroup.mk (r i))

include e he

theorem fibre_sum_eq_coset_sum (f : Classes H → ℂ) (g : G) :
    (∑' q : {q // forget h q=classOf J g},f q.val)=
      ∑ i,f (classOf H ((r i).val⁻¹*g)) := by
  have hh := (e.trans (leftTranslatedFibreEquiv h g)).tsum_eq (fun q => f q.val)
  change (∑' i,f (leftTranslatedFibreEquiv h g (e i)).val)=_ at hh
  simp_rw [he,leftTranslatedFibreEquiv_mk] at hh
  rw [← hh,tsum_fintype]

variable [Finite (J ⧸ H.subgroupOf J)]

/-- Coset representatives turn the orthogonality equation into the
literal finite old trace, with the inverse dictated by right cosets. -/
theorem projection_eq_zero_iff_coset_sums (f : ℓ²(Classes H,ℂ)) :
    (space h).starProjection f=0 ↔ ∀ g,∑ i,f (classOf H ((r i).val⁻¹*g))=0 := by
  rw [projection_eq_zero_iff]
  constructor
  · intro hf g
    rw [← fibre_sum_eq_coset_sum h r e he]
    exact hf (classOf J g)
  · intro hf y
    induction y using Quotient.inductionOn with
    | h g =>
      exact (fibre_sum_eq_coset_sum h r e he (fun q => f q) g).trans (hf g)

#print axioms fibre_sum_eq_coset_sum
#print axioms projection_eq_zero_iff_coset_sums

end AsymptoticNestedQuotients
