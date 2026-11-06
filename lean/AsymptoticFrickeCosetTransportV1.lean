module

public import AsymptoticFrickeCosetsV1
public import AsymptoticRamifiedTwistedLawV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticCongruenceStrip

open AsymptoticCongruenceLabels AsymptoticFreshMatrices

noncomputable def frickeSubgroupMap (N d : ℕ) (hN : 0<N) : gamma d →* frickeOldGroup N d hN where
  toFun a := ⟨frickeLabel N hN*a.val*(frickeLabel N hN)⁻¹,⟨a.val,a.property,rfl⟩⟩
  map_one' := by apply Subtype.ext; change frickeLabel N hN*1*(frickeLabel N hN)⁻¹=1; group
  map_mul' a b := by
    apply Subtype.ext
    change frickeLabel N hN*(a.val*b.val)*(frickeLabel N hN)⁻¹=
      (frickeLabel N hN*a.val*(frickeLabel N hN)⁻¹)*(frickeLabel N hN*b.val*(frickeLabel N hN)⁻¹)
    group

theorem frickeSubgroupMap_inv_mul (N d : ℕ) (hN : 0<N) (a b : gamma d) :
    (frickeSubgroupMap N d hN a).val⁻¹*(frickeSubgroupMap N d hN b).val=
      frickeLabel N hN*(a.val⁻¹*b.val)*(frickeLabel N hN)⁻¹ := by
  change (frickeLabel N hN*a.val*(frickeLabel N hN)⁻¹)⁻¹*
    (frickeLabel N hN*b.val*(frickeLabel N hN)⁻¹)=_
  group

noncomputable def frickeRelativeMap (N d : ℕ) (hN : 0<N) :
    (gamma d ⧸ (gamma N).subgroupOf (gamma d)) →
      (frickeOldGroup N d hN ⧸ (gamma N).subgroupOf (frickeOldGroup N d hN)) :=
  Quotient.map (frickeSubgroupMap N d hN) (by
    intro a b hab
    have hh := QuotientGroup.leftRel_apply.mp hab
    apply QuotientGroup.leftRel_apply.mpr
    change (frickeSubgroupMap N d hN a).val⁻¹*(frickeSubgroupMap N d hN b).val∈gamma N
    rw [frickeSubgroupMap_inv_mul,fricke_conj_mem_iff]
    exact hh)

theorem frickeRelativeMap_injective (N d : ℕ) (hN : 0<N) :
    Function.Injective (frickeRelativeMap N d hN) := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      have hh := QuotientGroup.eq.mp hab
      change (frickeSubgroupMap N d hN a).val⁻¹*(frickeSubgroupMap N d hN b).val∈gamma N at hh
      rw [frickeSubgroupMap_inv_mul,fricke_conj_mem_iff] at hh
      exact QuotientGroup.eq.mpr hh

theorem frickeRelativeMap_surjective (N d : ℕ) (hN : 0<N) :
    Function.Surjective (frickeRelativeMap N d hN) := by
  intro y
  induction y using Quotient.inductionOn with
  | h a =>
    obtain ⟨g,hg,hga⟩ := a.property
    refine ⟨QuotientGroup.mk ⟨g,hg⟩,?_⟩
    change QuotientGroup.mk (frickeSubgroupMap N d hN ⟨g,hg⟩)=QuotientGroup.mk a
    congr 1
    exact Subtype.ext hga

noncomputable def frickeRelativeEquiv (N d : ℕ) (hN : 0<N) :
    (gamma d ⧸ (gamma N).subgroupOf (gamma d)) ≃
      (frickeOldGroup N d hN ⧸ (gamma N).subgroupOf (frickeOldGroup N d hN)) :=
  Equiv.ofBijective (frickeRelativeMap N d hN)
    ⟨frickeRelativeMap_injective N d hN,frickeRelativeMap_surjective N d hN⟩

#print axioms frickeSubgroupMap_inv_mul
#print axioms frickeRelativeMap_injective
#print axioms frickeRelativeMap_surjective

end AsymptoticCongruenceStrip

namespace AsymptoticNestedQuotients

open AsymptoticCongruenceLabels AsymptoticCongruenceStrip AsymptoticFreshMatrices
open AsymptoticRamifiedTwistedLaw
open scoped lp

/-- The global Fricke equation carries zero trace to a divisor level
into zero trace along its second degeneracy direction. -/
theorem fricke_projection_zero_of_lower (N d : ℕ) (hN : 0<N) (hd : d∣N)
    (f : ℓ²(Classes (gamma N),ℂ)) (w : ℂ)
    (hW : ∀ g,w*f (classOf (gamma N) (frickeLabel N hN*g))=f (classOf (gamma N) g)) :
    letI : NeZero N := ⟨hN.ne'⟩
    (space (gamma_le_of_dvd hd)).starProjection f=0 →
      (space (gamma_le_frickeOldGroup hN hd)).starProjection f=0 := by
  let : NeZero N := ⟨hN.ne'⟩
  let I := gamma d ⧸ (gamma N).subgroupOf (gamma d)
  let : Fintype I := Fintype.ofFinite I
  let r : I → gamma d := Quotient.out
  let r' : I → frickeOldGroup N d hN := fun i => frickeSubgroupMap N d hN (r i)
  have he : ∀ i,(Equiv.refl I) i=QuotientGroup.mk (r i) := fun i => i.out_eq.symm
  have he' : ∀ i,frickeRelativeEquiv N d hN i=QuotientGroup.mk (r' i) := by
    intro i
    have hi := congrArg (frickeRelativeEquiv N d hN) i.out_eq
    exact hi.symm
  intro hf
  have hs := (projection_eq_zero_iff_coset_sums (gamma_le_of_dvd hd) r (Equiv.refl I) he f).mp hf
  apply (projection_eq_zero_iff_coset_sums (gamma_le_frickeOldGroup hN hd) r'
    (frickeRelativeEquiv N d hN) he' f).mpr
  intro g
  have hi (i : I) : (r' i).val⁻¹*g=frickeLabel N hN*((r i).val⁻¹*((frickeLabel N hN)⁻¹*g)) := by
    change (frickeLabel N hN*(r i).val*(frickeLabel N hN)⁻¹)⁻¹*g=_
    group
  simp_rw [hi,reverse_fricke_equation N hN (fun a => f (classOf (gamma N) a)) w hW]
  rw [← Finset.mul_sum,hs,mul_zero]

#print axioms fricke_projection_zero_of_lower

end AsymptoticNestedQuotients
