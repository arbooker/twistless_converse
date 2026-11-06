module

public import SmallLevelThirtyCBranchesV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace SmallLevelThirtyC

open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

theorem actual_defect_square (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 30 (2*m) f) :
    ((SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] C)-
      FinitenessNormalizedTwistProduct.root 30 f 4 • SmallLevelOriginal.fourierFunction (2*m) f)
      ∣[((2*m:ℕ):ℤ)] (E*E)=
    (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] C)-
      FinitenessNormalizedTwistProduct.root 30 f 4 • SmallLevelOriginal.fourierFunction (2*m) f := by
  obtain ⟨χ,hχ,hW⟩ := original_fricke_sign (by decide : 0<30) m hf
  obtain ⟨β,hβ,hB⟩ := SmallLevelThirtyB.original_A m hm hf
  have hi := congrArg (fun g : ℍ → ℂ => g ∣[((2*m:ℕ):ℤ)] SmallLevelThirtyB.B) hB
  rw [SmallLevelThirtyB.B_inverse,det_one_smul _ (det_one_inv _ SmallLevelThirtyB.A_det),
    ← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one] at hi
  have hBi : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] SmallLevelThirtyB.B=
      β • SmallLevelOriginal.fourierFunction (2*m) f := by
    rw [SmallLevelThirtyB.B_inverse]
    rcases hβ with h|h
    · rw [h] at hi ⊢; simpa using hi.symm
    · rw [h] at hi ⊢; simpa only [neg_one_smul,neg_neg] using congrArg Neg.neg hi.symm
  have hρ : χ*β=1 ∨ χ*β= -1 := by
    rcases hχ with rfl|rfl <;> rcases hβ with rfl|rfl <;> simp
  have hL : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] L=
      (χ*β) • SmallLevelOriginal.fourierFunction (2*m) f := by
    rw [L_relation,SlashAction.slash_mul,SlashAction.slash_mul,central_even,hW,
      det_one_smul _ SmallLevelThirtyB.B_det,hBi,smul_smul]
  have hR : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] R=
      (χ*β) • SmallLevelOriginal.fourierFunction (2*m) f := by
    rw [R_relation,SlashAction.slash_mul,hW,det_one_smul _ SmallLevelThirtyB.A_det,hB,smul_smul]
  exact double_coset_defect _ _ C Cp L R E R_det C_det E_det (χ*β)
    (FinitenessNormalizedTwistProduct.root 30 f 4) hρ
    (FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 4)
    hL hR double_coset (1/4) E_branch (original_pair hf)

#print axioms actual_defect_square

end SmallLevelThirtyC
