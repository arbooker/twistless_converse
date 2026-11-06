module

public import SmallLevelTwentyFourRigidityV1
public import SmallLevelSixCharacterV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace SmallLevelTwentyFour

open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelEvenScale SmallLevelNormalized
open scoped MatrixGroups ModularForm

def square : SL(2,ℤ) := ⟨!![5,2;12,5],by decide⟩

theorem square_matrix : A*A=SpecialLinearGroup.mapGL ℝ square := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A, matrix, square, GeneralLinearGroup.mkOfDetNeZero, SpecialLinearGroup.toGL,
      SpecialLinearGroup.map_apply_coe, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [sqrt_three_ne] <;> nlinarith

theorem C_relation : halfConjugate 3=(-1)*T*square⁻¹ := by decide

theorem actual_square (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 24 (2*m) f) :
    scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] square=scaledFunction (2*m) f := by
  obtain ⟨δ,hδ,hA⟩ := original_A m hm hf
  change scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ square= _
  rw [← square_matrix, SlashAction.slash_mul, hA, det_one_smul _ A_det, hA, smul_smul]
  rcases hδ with rfl | rfl <;> simp

theorem actual_C (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 24 (2*m) f) :
    scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] halfConjugate 3= -scaledFunction (2*m) f := by
  have hi := congrArg (fun F : ℍ → ℂ => F ∣[((2*m:ℕ):ℤ)] square⁻¹) (actual_square m hm hf)
  simp only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] at hi
  rw [C_relation]
  simp only [SlashAction.slash_mul, SmallLevelThirtySix.slash_neg_one_even,
    scaled_T (L:=6) hf.toEulerData, SlashAction.neg_slash, ← hi]

/-- Covariance under every level-six matrix, with the exact finite sign.
The group-generation step uses the already checked full transversal. -/
theorem six_signed (m : ℕ) (g : ℍ → ℂ)
    (hT : g ∣[((2*m:ℕ):ℤ)] T= -g)
    (hU : g ∣[((2*m:ℕ):ℤ)] lower 6= -g)
    (hC : g ∣[((2*m:ℕ):ℤ)] halfConjugate 3= -g)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 6) :
    g ∣[((2*m:ℕ):ℤ)] γ=(SmallLevelSixCharacter.sign γ:ℂ) • g := by
  let w : SL(2,ℤ) → ℍ → ℂ := fun M => (SmallLevelSixCharacter.sign M:ℂ) • g
  have ht (M : SL(2,ℤ)) (hM : M∈CongruenceSubgroup.Gamma0 6) :
      w M ∣[((2*m:ℕ):ℤ)] T=w (M*T) := by
    simp only [w, ModularForm.SL_smul_slash, hT, SmallLevelSixCharacter.sign_T M hM,
      Int.cast_neg, _root_.neg_smul, smul_neg]
  have hu (M : SL(2,ℤ)) (hM : M∈CongruenceSubgroup.Gamma0 6) :
      w M ∣[((2*m:ℕ):ℤ)] lower 6=w (M*lower 6) := by
    simp only [w, ModularForm.SL_smul_slash, hU, SmallLevelSixCharacter.sign_U M hM,
      Int.cast_neg, _root_.neg_smul, smul_neg]
  have hz (M : SL(2,ℤ)) (hM : M∈CongruenceSubgroup.Gamma0 6) :
      w M ∣[((2*m:ℕ):ℤ)] (-1 : SL(2,ℤ))=w (M*(-1)) := by
    simp only [w, ModularForm.SL_smul_slash, SmallLevelThirtySix.slash_neg_one_even,
      SmallLevelSixCharacter.sign_Z M hM]
  have hc (M : SL(2,ℤ)) (hM : M∈CongruenceSubgroup.Gamma0 6) :
      w M ∣[((2*m:ℕ):ℤ)] halfConjugate 3=w (M*halfConjugate 3) := by
    simp only [w, ModularForm.SL_smul_slash, hC, SmallLevelSixCharacter.sign_C M hM,
      Int.cast_neg, _root_.neg_smul, smul_neg]
  have hh := (gamma0_6_mem (orbitSubgroup (CongruenceSubgroup.Gamma0 6) ((2*m:ℕ):ℤ) w)
    ⟨by apply CongruenceSubgroup.Gamma0_mem.mpr; decide,ht⟩
    ⟨by apply CongruenceSubgroup.Gamma0_mem.mpr; decide,hu⟩
    ⟨by apply CongruenceSubgroup.Gamma0_mem.mpr; decide,hz⟩
    ⟨by apply CongruenceSubgroup.Gamma0_mem.mpr; decide,hc⟩ γ hγ).2 1 (Subgroup.one_mem _)
  simpa only [w, SmallLevelSixCharacter.sign_one, Int.cast_one, one_smul, one_mul] using hh

#print axioms square_matrix
#print axioms actual_square
#print axioms actual_C
#print axioms six_signed

end SmallLevelTwentyFour
