module

public import SmallLevelEightGeneratorsV1
public import SmallLevelEvenDescentV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace SmallLevelEightCharacter

open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups

def paritySign (x : ℤ) : ℤ := if x%2=0 then 1 else -1

def sign (g : SL(2,ℤ)) : ℤ := paritySign (g 0 1+g 1 0/8)

theorem paritySign_flip {x y : ℤ} (h : (y-x)%2=1) : paritySign y= -paritySign x := by
  unfold paritySign
  split_ifs <;> omega

theorem paritySign_same {x y : ℤ} (h : (y-x)%2=0) : paritySign y=paritySign x := by
  unfold paritySign
  split_ifs <;> omega

theorem divisible (g : SL(2,ℤ)) (hg : g∈CongruenceSubgroup.Gamma0 8) :
    (8:ℤ)∣g 1 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp (CongruenceSubgroup.Gamma0_mem.mp hg)

theorem diagonal_odd (g : SL(2,ℤ)) (hg : g∈CongruenceSubgroup.Gamma0 8) :
    g 0 0%2=1 ∧ g 1 1%2=1 := by
  have hc : (g 1 0:ZMod 2)=0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr (dvd_trans (by decide : (2:ℤ)∣8) (divisible g hg))
  have hd := (reduction 2 g).det_coe
  rw [det_fin_two] at hd
  change (g 0 0:ZMod 2)*(g 1 1:ZMod 2)-(g 0 1:ZMod 2)*(g 1 0:ZMod 2)=1 at hd
  rw [hc, mul_zero, sub_zero] at hd
  have hcheck : ∀ a d : ZMod 2, a*d=1 → a=1 ∧ d=1 := by decide
  have hh := hcheck _ _ hd
  constructor
  · simpa using (ZMod.intCast_eq_intCast_iff' (g 0 0) 1 2).mp hh.1
  · simpa using (ZMod.intCast_eq_intCast_iff' (g 1 1) 1 2).mp hh.2

theorem sign_one : sign 1=1 := by decide

theorem sign_T (g : SL(2,ℤ)) (hg : g∈CongruenceSubgroup.Gamma0 8) :
    sign (g*T)= -sign g := by
  have ho := diagonal_odd g hg
  unfold sign
  apply paritySign_flip
  change (((g.1*!![1,1;0,1] : Matrix (Fin 2) (Fin 2) ℤ) 0 1+(g.1*!![1,1;0,1] : Matrix (Fin 2) (Fin 2) ℤ) 1 0/8)-
    (g 0 1+g 1 0/8))%2=1
  norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  omega

theorem sign_U (g : SL(2,ℤ)) (hg : g∈CongruenceSubgroup.Gamma0 8) :
    sign (g*lower 8)= -sign g := by
  have ho := diagonal_odd g hg
  obtain ⟨c,hc⟩ := divisible g hg
  unfold sign
  apply paritySign_flip
  change (((g.1*!![1,0;8,1] : Matrix (Fin 2) (Fin 2) ℤ) 0 1+(g.1*!![1,0;8,1] : Matrix (Fin 2) (Fin 2) ℤ) 1 0/8)-
    (g 0 1+g 1 0/8))%2=1
  norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hc]
  omega

theorem sign_Z (g : SL(2,ℤ)) (hg : g∈CongruenceSubgroup.Gamma0 8) :
    sign (g*(-1))=sign g := by
  obtain ⟨c,hc⟩ := divisible g hg
  unfold sign
  apply paritySign_same
  have hb : (g*(-1 : SL(2,ℤ))) 0 1= -(g 0 1) := by simp
  have hd : (g*(-1 : SL(2,ℤ))) 1 0= -(g 1 0) := by simp
  rw [hb, hd, hc]
  omega

theorem sign_C (g : SL(2,ℤ)) (hg : g∈CongruenceSubgroup.Gamma0 8) :
    sign (g*halfConjugate 2)= -sign g := by
  have hC : halfConjugate 2=(⟨!![5,-2;8,-3],by decide⟩ : SL(2,ℤ)) := by decide
  rw [hC]
  have ho := diagonal_odd g hg
  obtain ⟨c,hc⟩ := divisible g hg
  unfold sign
  apply paritySign_flip
  change (((g.1*!![5,-2;8,-3] : Matrix (Fin 2) (Fin 2) ℤ) 0 1+(g.1*!![5,-2;8,-3] : Matrix (Fin 2) (Fin 2) ℤ) 1 0/8)-
    (g 0 1+g 1 0/8))%2=1
  norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hc]
  omega

theorem rescaled_sign (γ : SL(2,ℤ)) (c : ℤ) (hc : γ 1 0=4*(8:ℤ)*c) :
    sign (SmallLevelEvenScale.rescaledMatrix 8 γ c hc)=1 := by
  simp only [sign, SmallLevelEvenScale.rescaledMatrix, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Nat.cast_ofNat]
  unfold paritySign
  have h : (2*γ 0 1+2*8*c/8)%2=0 := by omega
  rw [h]
  rfl

#print axioms diagonal_odd
#print axioms sign_T
#print axioms sign_U
#print axioms sign_Z
#print axioms sign_C
#print axioms rescaled_sign

end SmallLevelEightCharacter
