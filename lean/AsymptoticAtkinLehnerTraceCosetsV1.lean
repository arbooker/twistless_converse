module

public import AsymptoticAtkinLehnerOldTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticAtkinLehner

open Matrix AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open scoped MatrixGroups

theorem traceSL_mul_inv_bottom (M p : ℕ) (A B : ℤ)
    (hAB : (p:ℤ)*A+(M:ℤ)*B=1) (a b : ℤ) :
    (traceSL M p A B hAB a*(traceSL M p A B hAB b)⁻¹) 1 0=(M:ℤ)^2*(b-a) := by
  change ((traceSL M p A B hAB a).val*(traceSL M p A B hAB b)⁻¹.val) 1 0=_
  rw [SpecialLinearGroup.SL2_inv_expl]
  change ((traceSL M p A B hAB a).val*!![(p:ℤ)*A-(M:ℤ)*b,-(b+B);-(-(M:ℤ)),1]) 1 0=_
  simp [traceSL,Matrix.mul_apply,Fin.sum_univ_two]
  ring

theorem traceSL_not_mem (M p : ℕ) (hM : 0<M) (hp : p.Prime) (A B : ℤ)
    (hAB : (p:ℤ)*A+(M:ℤ)*B=1) (a : ℤ) :
    traceSL M p A B hAB a∉CongruenceSubgroup.Gamma0 (p*M) := by
  intro h
  rw [gamma0_mem_dvd] at h
  change ((p*M:ℕ):ℤ)∣-(M:ℤ) at h
  have hm : (M:ℤ)≠0 := by exact_mod_cast hM.ne'
  rw [show -(M:ℤ)=(M:ℤ)*(-1) by ring,Nat.cast_mul,mul_comm (p:ℤ) (M:ℤ)] at h
  have hd : (p:ℤ)∣-1 := (mul_dvd_mul_iff_left hm).mp h
  have hd' : (p:ℤ)∣1 := dvd_neg.mp hd
  exact hp.not_dvd_one (by exact_mod_cast hd')

theorem traceSL_distinct (M p : ℕ) [Fact p.Prime] (hM : 0<M) (hpM : ¬p∣M) (A B : ℤ)
    (hAB : (p:ℤ)*A+(M:ℤ)*B=1) (a b : Fin p)
    (h : traceSL M p A B hAB a.val*(traceSL M p A B hAB b.val)⁻¹∈CongruenceSubgroup.Gamma0 (p*M)) : a=b := by
  rw [gamma0_mem_dvd,traceSL_mul_inv_bottom] at h
  have hm : (M:ℤ)≠0 := by exact_mod_cast hM.ne'
  rw [show (M:ℤ)^2*((b.val:ℤ)-(a.val:ℤ))=(M:ℤ)*((M:ℤ)*((b.val:ℤ)-(a.val:ℤ))) by ring,
    Nat.cast_mul,mul_comm (p:ℤ) (M:ℤ)] at h
  have hd : (p:ℤ)∣(M:ℤ)*((b.val:ℤ)-(a.val:ℤ)) := (mul_dvd_mul_iff_left hm).mp h
  have hz : (M:ZMod p)*((b.val:ZMod p)-(a.val:ZMod p))=0 := by
    have he := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd
    simpa only [Int.cast_mul,Int.cast_sub,Int.cast_natCast] using he
  have hn : (M:ZMod p)≠0 := (AsymptoticFreshResidues.levelUnit p M hpM).ne_zero
  have he : (b.val:ZMod p)=(a.val:ZMod p) := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hn)
  have hv := congrArg ZMod.val he
  simp only [ZMod.val_natCast,Nat.mod_eq_of_lt a.isLt,Nat.mod_eq_of_lt b.isLt] at hv
  exact Fin.ext hv.symm

noncomputable def traceRepresentative (M p : ℕ) (A B : ℤ)
    (hAB : (p:ℤ)*A+(M:ℤ)*B=1) : Option (Fin p) → gamma M
  | none => 1
  | some a => ⟨(integralLabel (traceSL M p A B hAB a.val))⁻¹,
      (gamma M).inv_mem ⟨traceSL M p A B hAB a.val,traceSL_mem M p A B hAB a.val,rfl⟩⟩

noncomputable def traceCoset (M p : ℕ) (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1)
    (a : Option (Fin p)) : gamma M ⧸ (gamma (p*M)).subgroupOf (gamma M) :=
  QuotientGroup.mk (traceRepresentative M p A B hAB a)

theorem traceCoset_injective (M p : ℕ) [Fact p.Prime] (hM : 0<M) (hpM : ¬p∣M) (A B : ℤ)
    (hAB : (p:ℤ)*A+(M:ℤ)*B=1) : Function.Injective (traceCoset M p A B hAB) := by
  intro a b hab
  have hn : ∀ a : Fin p,traceCoset M p A B hAB none≠traceCoset M p A B hAB (some a) := by
    intro a he
    have hh := QuotientGroup.eq.mp he
    change 1⁻¹*(integralLabel (traceSL M p A B hAB a.val))⁻¹∈gamma (p*M) at hh
    simp only [inv_one,one_mul] at hh
    have hi := (gamma (p*M)).inv_mem hh
    rw [inv_inv,integralLabel_mem_gamma_iff] at hi
    exact traceSL_not_mem M p hM (Fact.out : p.Prime) A B hAB a.val hi
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => exact (hn b hab).elim
  | some a =>
    cases b with
    | none => exact (hn a hab.symm).elim
    | some b =>
      have hh := QuotientGroup.eq.mp hab
      change ((integralLabel (traceSL M p A B hAB a.val))⁻¹)⁻¹*
        (integralLabel (traceSL M p A B hAB b.val))⁻¹∈gamma (p*M) at hh
      rw [inv_inv,← map_inv,← map_mul,integralLabel_mem_gamma_iff] at hh
      exact congrArg some (traceSL_distinct M p hM hpM A B hAB a b hh)

theorem traceCoset_surjective (M p : ℕ) [Fact p.Prime] (hM : 0<M) (hpM : ¬p∣M) (A B : ℤ)
    (hAB : (p:ℤ)*A+(M:ℤ)*B=1) : Function.Surjective (traceCoset M p A B hAB) := by
  let : NeZero (p*M) := ⟨(Nat.mul_pos (Fact.out : p.Prime).pos hM).ne'⟩
  have hc : Nat.card (gamma M ⧸ (gamma (p*M)).subgroupOf (gamma M))≤Nat.card (Option (Fin p)) := by
    change (gamma (p*M)).relIndex (gamma M)≤_
    rw [AsymptoticRamifiedCosets.projective_index_coprime M p hM (Fact.out : p.Prime)
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpM)]
    simp [Nat.card_eq_fintype_card]
  exact ((traceCoset_injective M p hM hpM A B hAB).bijective_of_nat_card_le hc).2

noncomputable def traceCosetEquiv (M p : ℕ) [Fact p.Prime] (hM : 0<M) (hpM : ¬p∣M) (A B : ℤ)
    (hAB : (p:ℤ)*A+(M:ℤ)*B=1) : Option (Fin p) ≃ (gamma M ⧸ (gamma (p*M)).subgroupOf (gamma M)) :=
  Equiv.ofBijective (traceCoset M p A B hAB)
    ⟨traceCoset_injective M p hM hpM A B hAB,traceCoset_surjective M p hM hpM A B hAB⟩

#print axioms traceSL_mul_inv_bottom
#print axioms traceSL_not_mem
#print axioms traceSL_distinct
#print axioms traceCoset_injective
#print axioms traceCoset_surjective

end AsymptoticAtkinLehner
