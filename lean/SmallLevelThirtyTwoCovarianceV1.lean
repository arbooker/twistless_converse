module

public import SmallLevelThirtyTwoRigidityV1
public import SmallLevelEightCharacterV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelThirtyTwo

open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelEvenScale
open scoped MatrixGroups ModularForm

theorem C_relation : halfConjugate 2=(-1)*T*A⁻¹ := by decide

theorem actual_C (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 32 (2*m) f) :
    scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] halfConjugate 2= -scaledFunction (2*m) f := by
  have ha := original_A (by omega : 0<2*m) hf
  have hi := congrArg (fun F : ℍ → ℂ => F ∣[((2*m:ℕ):ℤ)] A⁻¹) ha
  simp only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] at hi
  rw [C_relation]
  simp only [SlashAction.slash_mul, SmallLevelThirtySix.slash_neg_one_even,
    scaled_T (L:=8) hf.toEulerData, SlashAction.neg_slash, ← hi]

/-- Covariance under every level-eight matrix, with the exact finite sign.
The group-generation step uses the already checked full transversal. -/
theorem eight_signed (m : ℕ) (g : ℍ → ℂ)
    (hT : g ∣[((2*m:ℕ):ℤ)] T= -g)
    (hU : g ∣[((2*m:ℕ):ℤ)] lower 8= -g)
    (hC : g ∣[((2*m:ℕ):ℤ)] halfConjugate 2= -g)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 8) :
    g ∣[((2*m:ℕ):ℤ)] γ=(SmallLevelEightCharacter.sign γ:ℂ) • g := by
  let w : SL(2,ℤ) → ℍ → ℂ := fun M => (SmallLevelEightCharacter.sign M:ℂ) • g
  have ht (M : SL(2,ℤ)) (hM : M∈CongruenceSubgroup.Gamma0 8) :
      w M ∣[((2*m:ℕ):ℤ)] T=w (M*T) := by
    simp only [w, ModularForm.SL_smul_slash, hT, SmallLevelEightCharacter.sign_T M hM,
      Int.cast_neg, _root_.neg_smul, smul_neg]
  have hu (M : SL(2,ℤ)) (hM : M∈CongruenceSubgroup.Gamma0 8) :
      w M ∣[((2*m:ℕ):ℤ)] lower 8=w (M*lower 8) := by
    simp only [w, ModularForm.SL_smul_slash, hU, SmallLevelEightCharacter.sign_U M hM,
      Int.cast_neg, _root_.neg_smul, smul_neg]
  have hz (M : SL(2,ℤ)) (hM : M∈CongruenceSubgroup.Gamma0 8) :
      w M ∣[((2*m:ℕ):ℤ)] (-1 : SL(2,ℤ))=w (M*(-1)) := by
    simp only [w, ModularForm.SL_smul_slash, SmallLevelThirtySix.slash_neg_one_even,
      SmallLevelEightCharacter.sign_Z M hM]
  have hc (M : SL(2,ℤ)) (hM : M∈CongruenceSubgroup.Gamma0 8) :
      w M ∣[((2*m:ℕ):ℤ)] halfConjugate 2=w (M*halfConjugate 2) := by
    simp only [w, ModularForm.SL_smul_slash, hC, SmallLevelEightCharacter.sign_C M hM,
      Int.cast_neg, _root_.neg_smul, smul_neg]
  have hh := (gamma0_8_mem (orbitSubgroup (CongruenceSubgroup.Gamma0 8) ((2*m:ℕ):ℤ) w)
    ⟨by apply CongruenceSubgroup.Gamma0_mem.mpr; decide,ht⟩
    ⟨by apply CongruenceSubgroup.Gamma0_mem.mpr; decide,hu⟩
    ⟨by apply CongruenceSubgroup.Gamma0_mem.mpr; decide,hz⟩
    ⟨by apply CongruenceSubgroup.Gamma0_mem.mpr; decide,hc⟩ γ hγ).2 1 (Subgroup.one_mem _)
  simpa only [w, SmallLevelEightCharacter.sign_one, Int.cast_one, one_smul, one_mul] using hh

#print axioms actual_C
#print axioms eight_signed

end SmallLevelThirtyTwo
