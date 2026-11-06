module

public import AsymptoticRepeatedJoinIndexV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

namespace QuantitativeArithmeticRepeatedJoin

open Matrix AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open AsymptoticFreshMatrices AsymptoticFreshCRT AsymptoticRationalGroup
open scoped MatrixGroups

/-- Two integral upper translations make the upper-right entry divisible
by p. This works for every prime; no primality of p+1 is needed. -/
theorem upper_reduce (p : ℕ) [Fact p.Prime] (A : SL(2,ℤ)) :
    ∃ v u : ℤ,(p:ℤ)∣(upperSL v*A*upperSL u) 0 1 := by
  have hd : (A 0 0:ZMod p)*(A 1 1:ZMod p)-(A 0 1:ZMod p)*(A 1 0:ZMod p)=1 := by
    have h := congrArg (fun n : ℤ => (n:ZMod p)) A.property
    simpa only [Matrix.det_fin_two,Int.cast_sub,Int.cast_mul,Int.cast_one] using h
  have hl (v : ℤ) : (upperSL v*A) 0 0=A 0 0+v*A 1 0 := by
    change (upper v*A.val) 0 0=_
    simp [upper,Matrix.mul_apply,Fin.sum_univ_two]
  have hv : ∃ v : ℤ,((upperSL v*A) 0 0:ZMod p)≠0 := by
    by_cases ha : (A 0 0:ZMod p)=0
    · have hc : (A 1 0:ZMod p)≠0 := by intro hc; simp [ha,hc] at hd
      refine ⟨1,?_⟩
      rw [hl]
      simpa [ha] using hc
    · refine ⟨0,?_⟩
      rw [hl]
      simpa using ha
  obtain ⟨v,hv⟩ := hv
  let B := upperSL v*A
  let r : ZMod p := -(B 0 1:ZMod p)/(B 0 0:ZMod p)
  let u : ℤ := r.val
  refine ⟨v,u,(ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_⟩
  have hu : (u:ZMod p)=r := by simp [u]
  have hB : (B 0 0:ZMod p)≠0 := hv
  change ((B*upperSL u) 0 1:ZMod p)=0
  have hr : (B*upperSL u) 0 1=B 0 0*u+B 0 1 := by
    change (B.val*upper u) 0 1=_
    simp [upper,Matrix.mul_apply,Fin.sum_univ_two]
  rw [hr]
  push_cast
  rw [hu]
  dsimp only [r]
  field_simp [hB]
  ring

/-- Conjugation by D_p is integral once p divides the upper-right entry. -/
def conjugate (p : ℕ) (A : SL(2,ℤ)) (b : ℤ) (hb : A 0 1=(p:ℤ)*b) : SL(2,ℤ) :=
  ⟨!![A 0 0,b;(p:ℤ)*A 1 0,A 1 1],by
    rw [Matrix.det_fin_two]
    change A 0 0*A 1 1-b*((p:ℤ)*A 1 0)=1
    have hd := A.property
    rw [Matrix.det_fin_two] at hd
    change A 0 0*A 1 1-A 0 1*A 1 0=1 at hd
    rw [hb] at hd
    nlinarith [hd]⟩

theorem conjugate_mem (L p : ℕ) (A : SL(2,ℤ)) (hA : A∈CongruenceSubgroup.Gamma0 L)
    (b : ℤ) (hb : A 0 1=(p:ℤ)*b) : conjugate p A b hb∈CongruenceSubgroup.Gamma0 (p*L) := by
  rw [gamma0_mem_dvd] at hA ⊢
  obtain ⟨c,hc⟩ := hA
  refine ⟨c,?_⟩
  change (p:ℤ)*A 1 0=((p*L:ℕ):ℤ)*c
  rw [hc,Nat.cast_mul]
  ring

theorem conjugate_label (p : ℕ) (hp : 0<p) (A : SL(2,ℤ))
    (b : ℤ) (hb : A 0 1=(p:ℤ)*b) :
    integralLabel A*dilationLabel p hp=dilationLabel p hp*integralLabel (conjugate p A b hb) := by
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (rationalGL A)*rationalMap (dilationGL p hp)=
    rationalMap (dilationGL p hp)*rationalMap (rationalGL (conjugate p A b hb))
  rw [← map_mul,← map_mul]
  congr 1
  apply Units.ext
  change A.val.map (fun z : ℤ => (z:ℚ))*(dilationGL p hp).val=
    (dilationGL p hp).val*(conjugate p A b hb).val.map (fun z : ℤ => (z:ℚ))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dilationGL,GeneralLinearGroup.mkOfDetNeZero,conjugate,
      Matrix.mul_apply,Fin.sum_univ_two,hb]
  all_goals ring

theorem upper_mem (L : ℕ) (u : ℤ) : upperSL u∈CongruenceSubgroup.Gamma0 L := by
  rw [CongruenceSubgroup.Gamma0_mem]
  simp [upperSL,upper]

/-- Exact generated overgroup at every repeated prime, including odd
prime-square factors where the prime-index shortcut does not apply. -/
theorem repeated_join_eq (L p : ℕ) [Fact p.Prime] (hL : 0<L) :
    gamma (p*L)⊔degeneracyGroup (p*L) p (Fact.out : p.Prime).pos=
      degeneracyGroup L p (Fact.out : p.Prime).pos := by
  have hp := (Fact.out : p.Prime).pos
  apply le_antisymm
  · exact sup_le (gamma_le_degeneracyGroup L p hL hp)
      (degeneracyGroup_mono hp (Nat.dvd_mul_left L p))
  · rintro g ⟨a,⟨A,hA,rfl⟩,rfl⟩
    let J := gamma (p*L)⊔degeneracyGroup (p*L) p hp
    let φ : SL(2,ℤ) →* AsymptoticRationalGroup.Group :=
      (MulAut.conj (dilationLabel p hp)⁻¹).toMonoidHom.comp integralLabel
    have ht (u : ℤ) : φ (upperSL u)∈J := by
      apply (show degeneracyGroup (p*L) p hp≤J from le_sup_right)
      exact ⟨integralLabel (upperSL u),⟨upperSL u,upper_mem (p*L) u,rfl⟩,rfl⟩
    have hz (B : SL(2,ℤ)) (hB : B∈CongruenceSubgroup.Gamma0 L) (hb : (p:ℤ)∣B 0 1) : φ B∈J := by
      obtain ⟨b,hb⟩ := hb
      have he : φ B=integralLabel (conjugate p B b hb) := by
        change (dilationLabel p hp)⁻¹*integralLabel B*dilationLabel p hp=_
        rw [mul_assoc,conjugate_label p hp B b hb,← mul_assoc,inv_mul_cancel,one_mul]
      rw [he]
      apply (show gamma (p*L)≤J from le_sup_left)
      exact ⟨conjugate p B b hb,conjugate_mem L p B hB b hb,rfl⟩
    obtain ⟨v,u,hvu⟩ := upper_reduce p A
    have hB := hz (upperSL v*A*upperSL u)
      ((CongruenceSubgroup.Gamma0 L).mul_mem
        ((CongruenceSubgroup.Gamma0 L).mul_mem (upper_mem L v) hA) (upper_mem L u)) hvu
    rw [map_mul,map_mul] at hB
    exact (J.mul_mem_cancel_left (ht v)).mp ((J.mul_mem_cancel_right (ht u)).mp hB)

/-- The full local join index, without a prime-relative-index hypothesis. -/
theorem repeated_join_index (L p : ℕ) [Fact p.Prime] (hL : 0<L) :
    (gamma (p*(p*L))).relIndex
      (gamma (p*L)⊔degeneracyGroup (p*L) p (Fact.out : p.Prime).pos)=
        p*(gamma (p*L)).relIndex (gamma L) := by
  rw [repeated_join_eq L p hL,double_degeneracy_index L p hL (Fact.out : p.Prime).pos]

#print axioms upper_reduce
#print axioms conjugate_label
#print axioms repeated_join_eq
#print axioms repeated_join_index

end QuantitativeArithmeticRepeatedJoin
