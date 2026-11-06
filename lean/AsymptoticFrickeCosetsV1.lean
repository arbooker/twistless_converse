module

public import AsymptoticDegeneracyGroupV1
public import AsymptoticCosetTraceSumsV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticCongruenceLabels

open AsymptoticCongruenceStrip
open scoped MatrixGroups

theorem integralLabel_mem_gamma_iff (N : ℕ) (A : SL(2,ℤ)) :
    integralLabel A∈gamma N ↔ A∈CongruenceSubgroup.Gamma0 N := by
  change A∈((CongruenceSubgroup.Gamma0 N).map integralLabel).comap integralLabel ↔ _
  rw [Subgroup.comap_map_eq,sup_eq_left.mpr (integralLabel_ker_le N)]

#print axioms integralLabel_mem_gamma_iff

end AsymptoticCongruenceLabels

namespace AsymptoticCongruenceStrip

open AsymptoticCongruenceLabels AsymptoticFreshMatrices

theorem fricke_conj_mem_iff (N : ℕ) (hN : 0<N) (g : AsymptoticRationalGroup.Group) :
    frickeLabel N hN*g*(frickeLabel N hN)⁻¹∈gamma N ↔ g∈gamma N := by
  constructor
  · intro hg
    have hh := fricke_conj_mem N hN hg
    rw [frickeLabel_inv] at hh
    simp only [← mul_assoc,frickeLabel_mul_self,one_mul] at hh
    simpa only [mul_assoc,frickeLabel_mul_self,mul_one] using hh
  · exact fricke_conj_mem N hN

#print axioms fricke_conj_mem_iff

end AsymptoticCongruenceStrip

namespace AsymptoticRamifiedCosets

open AsymptoticCongruenceLabels AsymptoticCongruenceStrip AsymptoticFreshMatrices

noncomputable def frickeRepresentative (M q : ℕ) (hM : 0<M) (hq : 0<q) (j : Fin q) :
    frickeOldGroup (q*M) M (Nat.mul_pos hq hM) :=
  ⟨frickeLabel (q*M) (Nat.mul_pos hq hM)*integralLabel (lowerSL M (j.val:ℤ))*
      (frickeLabel (q*M) (Nat.mul_pos hq hM))⁻¹,
    ⟨integralLabel (lowerSL M (j.val:ℤ)),⟨lowerSL M (j.val:ℤ),lowerSL_mem M (j.val:ℤ),rfl⟩,rfl⟩⟩

noncomputable def frickeCoset (M q : ℕ) (hM : 0<M) (hq : 0<q) (j : Fin q) :
    frickeOldGroup (q*M) M (Nat.mul_pos hq hM) ⧸
      (gamma (q*M)).subgroupOf (frickeOldGroup (q*M) M (Nat.mul_pos hq hM)) :=
  QuotientGroup.mk (frickeRepresentative M q hM hq j)

theorem frickeCoset_injective (M q : ℕ) (hM : 0<M) (hq : 0<q) :
    Function.Injective (frickeCoset M q hM hq) := by
  intro i j hij
  have hh := QuotientGroup.eq.mp hij
  change (frickeRepresentative M q hM hq i).val⁻¹*(frickeRepresentative M q hM hq j).val∈gamma (q*M) at hh
  have he : (frickeRepresentative M q hM hq i).val⁻¹*(frickeRepresentative M q hM hq j).val=
      frickeLabel (q*M) (Nat.mul_pos hq hM)*
        integralLabel ((lowerSL M (i.val:ℤ))⁻¹*lowerSL M (j.val:ℤ))*
          (frickeLabel (q*M) (Nat.mul_pos hq hM))⁻¹ := by
    simp only [frickeRepresentative,map_mul,map_inv]
    group
  rw [he,fricke_conj_mem_iff,integralLabel_mem_gamma_iff] at hh
  exact representatives_distinct M q hM hq i j hh

theorem frickeCoset_surjective (M q : ℕ) (hM : 0<M) (hq : 0<q) (hqM : q∣M) :
    Function.Surjective (frickeCoset M q hM hq) := by
  intro y
  induction y using Quotient.inductionOn with
  | h a =>
    obtain ⟨g,hg,hga⟩ := a.property
    obtain ⟨A,hA,hAg⟩ := hg
    obtain ⟨j,hj⟩ := reduce_to_finer M q hq hqM A hA
    refine ⟨j,QuotientGroup.eq.mpr ?_⟩
    change (frickeRepresentative M q hM hq j).val⁻¹*a.val∈gamma (q*M)
    have ha : a.val=frickeLabel (q*M) (Nat.mul_pos hq hM)*integralLabel A*
        (frickeLabel (q*M) (Nat.mul_pos hq hM))⁻¹ := by
      rw [← hga,← hAg]
      rfl
    rw [ha]
    have he : (frickeRepresentative M q hM hq j).val⁻¹*
        (frickeLabel (q*M) (Nat.mul_pos hq hM)*integralLabel A*
          (frickeLabel (q*M) (Nat.mul_pos hq hM))⁻¹)=
        frickeLabel (q*M) (Nat.mul_pos hq hM)*integralLabel ((lowerSL M (j.val:ℤ))⁻¹*A)*
          (frickeLabel (q*M) (Nat.mul_pos hq hM))⁻¹ := by
      simp only [frickeRepresentative,map_mul,map_inv]
      group
    rw [he,fricke_conj_mem_iff,integralLabel_mem_gamma_iff]
    exact hj

noncomputable def frickeCosetEquiv (M q : ℕ) (hM : 0<M) (hq : 0<q) (hqM : q∣M) :
    Fin q ≃ (frickeOldGroup (q*M) M (Nat.mul_pos hq hM) ⧸
      (gamma (q*M)).subgroupOf (frickeOldGroup (q*M) M (Nat.mul_pos hq hM))) :=
  Equiv.ofBijective (frickeCoset M q hM hq)
    ⟨frickeCoset_injective M q hM hq,frickeCoset_surjective M q hM hq hqM⟩

#print axioms frickeCoset_injective
#print axioms frickeCoset_surjective

end AsymptoticRamifiedCosets
