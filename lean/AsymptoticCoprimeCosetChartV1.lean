module

public import AsymptoticRamifiedCosetReductionV1
public import Mathlib.Data.Int.GCD

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticRamifiedCosets

open Matrix AsymptoticCongruenceLabels
open scoped MatrixGroups

/-- The additional projective-line chart at a new prime factor, built
over the integers by Bezout rather than supplied as a coset hypothesis. -/
def exceptional (M p : ℕ) (hc : p.Coprime M) : SL(2,ℤ) :=
  ⟨!![(p:ℤ),-Nat.gcdB p M;(M:ℤ),Nat.gcdA p M],by
    rw [Matrix.det_fin_two]
    change (p:ℤ)*Nat.gcdA p M - (-Nat.gcdB p M)*(M:ℤ)=1
    have he := Nat.gcd_eq_gcd_ab p M
    rw [hc.gcd_eq_one,Nat.cast_one] at he
    simpa only [neg_mul,sub_neg_eq_add,mul_comm (Nat.gcdB p M) (M:ℤ)] using he.symm⟩

theorem exceptional_mem (M p : ℕ) (hc : p.Coprime M) :
    exceptional M p hc∈CongruenceSubgroup.Gamma0 M := by
  rw [gamma0_mem_dvd]
  exact dvd_refl _

theorem exceptional_inv_mul_bottom (M p : ℕ) (hc : p.Coprime M) (A : SL(2,ℤ)) :
    ((exceptional M p hc)⁻¹*A) 1 0=(p:ℤ)*A 1 0-(M:ℤ)*A 0 0 := by
  change ((exceptional M p hc)⁻¹.val*A.val) 1 0=_
  rw [SpecialLinearGroup.SL2_inv_expl]
  change (!![Nat.gcdA p M,Nat.gcdB p M;-(M:ℤ),(p:ℤ)]*A.val) 1 0=_
  simp [Matrix.mul_apply,Fin.sum_univ_two]
  ring

theorem reduce_to_exceptional (M p : ℕ) (hc : p.Coprime M) (A : SL(2,ℤ))
    (hA : A∈CongruenceSubgroup.Gamma0 M) (ha : (A 0 0:ZMod p)=0) :
    (exceptional M p hc)⁻¹*A∈CongruenceSubgroup.Gamma0 (p*M) := by
  obtain ⟨c,hc'⟩ := (gamma0_mem_dvd M A).mp hA
  obtain ⟨a,ha'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ha
  rw [gamma0_mem_dvd,exceptional_inv_mul_bottom,hc',ha']
  refine ⟨c-a,?_⟩
  rw [Nat.cast_mul]
  ring

theorem exceptional_distinct (M p : ℕ) (hM : 0<M) (hp : p.Prime) (hc : p.Coprime M)
    (j : Fin p) : (exceptional M p hc)⁻¹*lowerSL M (j.val:ℤ)∉CongruenceSubgroup.Gamma0 (p*M) := by
  intro h
  rw [gamma0_mem_dvd,exceptional_inv_mul_bottom] at h
  change ((p*M:ℕ):ℤ)∣(p:ℤ)*((M:ℤ)*(j.val:ℤ))-(M:ℤ)*1 at h
  have he : (p:ℤ)*((M:ℤ)*(j.val:ℤ))-(M:ℤ)*1=(M:ℤ)*((p:ℤ)*(j.val:ℤ)-1) := by ring
  rw [he,Nat.cast_mul,mul_comm (p:ℤ) (M:ℤ)] at h
  have hM0 : (M:ℤ)≠0 := by exact_mod_cast hM.ne'
  have hd : (p:ℤ)∣(p:ℤ)*(j.val:ℤ)-1 := (mul_dvd_mul_iff_left hM0).mp h
  have hd1 : (p:ℤ)∣1 := by
    convert dvd_sub (dvd_mul_right (p:ℤ) (j.val:ℤ)) hd using 1
    ring
  have hp1 : p∣1 := by exact_mod_cast hd1
  exact hp.not_dvd_one hp1

#print axioms exceptional_mem
#print axioms exceptional_inv_mul_bottom
#print axioms reduce_to_exceptional
#print axioms exceptional_distinct

end AsymptoticRamifiedCosets
