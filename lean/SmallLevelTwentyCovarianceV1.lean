module

public import SmallLevelTwentyRigidityV1
public import SmallLevelFiveGeneratorsV1
public import SmallLevelEvenDescentV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelTwenty

open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelEvenScale
open scoped MatrixGroups ModularForm

theorem sign_U : ∀ g : SL(2,ZMod 2), signTwo (g*reduction 2 (lower 5))= -signTwo g := by decide

theorem sign_A : ∀ g : SL(2,ZMod 2), signTwo (g*reduction 2 A)=signTwo g := by decide

theorem five_signed (m : ℕ) (g : ℍ → ℂ)
    (hT : g ∣[((2*m:ℕ):ℤ)] T= -g)
    (hU : g ∣[((2*m:ℕ):ℤ)] lower 5= -g)
    (hA : g ∣[((2*m:ℕ):ℤ)] A=g)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 5) :
    g ∣[((2*m:ℕ):ℤ)] γ=(signTwo (reduction 2 γ):ℂ) • g := by
  let w : SL(2,ℤ) → ℍ → ℂ := fun M => (signTwo (reduction 2 M):ℂ) • g
  have ht (M : SL(2,ℤ)) (_hM : M∈CongruenceSubgroup.Gamma0 5) :
      w M ∣[((2*m:ℕ):ℤ)] T=w (M*T) := by
    simp only [w, ModularForm.SL_smul_slash, hT, map_mul, signTwo_T,
      Int.cast_neg, _root_.neg_smul, smul_neg]
  have hu (M : SL(2,ℤ)) (_hM : M∈CongruenceSubgroup.Gamma0 5) :
      w M ∣[((2*m:ℕ):ℤ)] lower 5=w (M*lower 5) := by
    simp only [w, ModularForm.SL_smul_slash, hU, map_mul, sign_U,
      Int.cast_neg, _root_.neg_smul, smul_neg]
  have hz (M : SL(2,ℤ)) (_hM : M∈CongruenceSubgroup.Gamma0 5) :
      w M ∣[((2*m:ℕ):ℤ)] (-1:SL(2,ℤ))=w (M*(-1)) := by
    simp only [w, ModularForm.SL_smul_slash, SmallLevelThirtySix.slash_neg_one_even,
      map_mul, signTwo_Z]
  have ha (M : SL(2,ℤ)) (_hM : M∈CongruenceSubgroup.Gamma0 5) :
      w M ∣[((2*m:ℕ):ℤ)] A=w (M*A) := by
    simp only [w, ModularForm.SL_smul_slash, hA, map_mul, sign_A]
  have hh := (gamma0_5_mem (orbitSubgroup (CongruenceSubgroup.Gamma0 5) ((2*m:ℕ):ℤ) w)
    ⟨by apply CongruenceSubgroup.Gamma0_mem.mpr; decide,ht⟩
    ⟨by apply CongruenceSubgroup.Gamma0_mem.mpr; decide,hu⟩
    ⟨by apply CongruenceSubgroup.Gamma0_mem.mpr; decide,hz⟩
    ⟨by apply CongruenceSubgroup.Gamma0_mem.mpr; decide,ha⟩ γ hγ).2 1 (Subgroup.one_mem _)
  simpa only [w, map_one, signTwo_one, Int.cast_one, one_smul, one_mul] using hh

theorem rescaled_sign (γ : SL(2,ℤ)) (c : ℤ) (hc : γ 1 0=4*(5:ℤ)*c) :
    signTwo (reduction 2 (rescaledMatrix 5 γ c hc))=1 := by
  apply signTwo_diagonal
  · change ((2*γ 0 1:ℤ):ZMod 2)=0
    push_cast
    rw [show (2:ZMod 2)=0 by decide, zero_mul]
  · change ((10*c:ℤ):ZMod 2)=0
    push_cast
    rw [show (10:ZMod 2)=0 by decide, zero_mul]

#print axioms five_signed
#print axioms rescaled_sign

end SmallLevelTwenty
