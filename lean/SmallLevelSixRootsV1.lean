module

public import SmallLevelThirtyThreeTheoryV4
public import SmallLevelThirtyFourTheoryV4
public import SmallLevelThirtyFiveTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelSixEigen

open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

theorem primeFactors_six : (6:ℕ).primeFactors={2,3} := by
  rw [show (6:ℕ)=2*3 by norm_num,Nat.primeFactors_mul (by decide) (by decide)]
  norm_num

theorem factorization_six_two : (6:ℕ).factorization 2=1 := by
  rw [show (6:ℕ)=2*3 by norm_num,Nat.factorization_mul (by decide) (by decide)]
  simp [Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2∣3)]

theorem factorization_six_three : (6:ℕ).factorization 3=1 := by
  rw [show (6:ℕ)=2*3 by norm_num,Nat.factorization_mul (by decide) (by decide)]
  simp [Nat.prime_three.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬3∣2)]

theorem root_six_three {N : ℕ} (h : ¬2∣N) (f : ℕ → ℂ) :
    FinitenessNormalizedTwistProduct.root N f 6=FinitenessNormalizedTwistProduct.root N f 3 := by
  unfold FinitenessNormalizedTwistProduct.root
  rw [primeFactors_six,Nat.prime_three.primeFactors]
  norm_num [FinitenessNormalizedTwistLocal.sign,h,factorization_six_three,
    Nat.prime_three.factorization_self]

theorem root_six_two {N : ℕ} (h : ¬3∣N) (f : ℕ → ℂ) :
    FinitenessNormalizedTwistProduct.root N f 6=FinitenessNormalizedTwistProduct.root N f 2 := by
  unfold FinitenessNormalizedTwistProduct.root
  rw [primeFactors_six,Nat.prime_two.primeFactors]
  norm_num [FinitenessNormalizedTwistLocal.sign,h,factorization_six_two,
    Nat.prime_two.factorization_self]

theorem root_six_one {N : ℕ} (h2 : ¬2∣N) (h3 : ¬3∣N) (f : ℕ → ℂ) :
    FinitenessNormalizedTwistProduct.root N f 6=1 := by
  unfold FinitenessNormalizedTwistProduct.root
  rw [primeFactors_six]
  norm_num [FinitenessNormalizedTwistLocal.sign,h2,h3]

/-- A sign eigenlaw persists under inversion without dividing by an unknown scalar. -/
theorem eigen_inverse (F : ℍ → ℂ) (k : ℤ) (A : GL (Fin 2) ℝ)
    (hdet : (GeneralLinearGroup.det A:ℝ)=1) (δ : ℂ) (hδ : δ=1 ∨ δ= -1)
    (hA : F ∣[k] A=δ • F) : F ∣[k] A⁻¹=δ • F := by
  have h := congrArg (fun g : ℍ → ℂ => g ∣[k] A⁻¹) hA
  rw [← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one,
    det_one_smul _ (det_one_inv _ hdet)] at h
  rcases hδ with rfl|rfl
  · simpa only [one_smul] using h.symm
  · simpa only [neg_one_smul,neg_neg] using congrArg Neg.neg h.symm

theorem thirty_three_A {k : ℕ} (hk : 0<k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 k f) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] SmallLevelThirtyThree.A=
      FinitenessNormalizedTwistProduct.root 33 f 3 • SmallLevelOriginal.fourierFunction k f := by
  rw [SmallLevelThirtyThree.original_A hk hf,root_six_three (by decide)]

theorem thirty_three_B {k : ℕ} (hk : 0<k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 k f) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] SmallLevelThirtyThree.B=
      FinitenessNormalizedTwistProduct.root 33 f 3 • SmallLevelOriginal.fourierFunction k f := by
  rw [SmallLevelThirtyThree.B_inverse]
  exact eigen_inverse _ _ _ SmallLevelThirtyThree.A_det _
    (FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 3) (thirty_three_A hk hf)

theorem thirty_four_A {k : ℕ} (hk : 0<k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 k f) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] SmallLevelThirtyFour.A=
      FinitenessNormalizedTwistProduct.root 34 f 2 • SmallLevelOriginal.fourierFunction k f := by
  rw [SmallLevelThirtyFour.original_A hk hf,root_six_two (by decide)]

theorem thirty_four_B {k : ℕ} (hk : 0<k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 k f) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] SmallLevelThirtyFour.B=
      FinitenessNormalizedTwistProduct.root 34 f 2 • SmallLevelOriginal.fourierFunction k f := by
  rw [SmallLevelThirtyFour.B_inverse]
  exact eigen_inverse _ _ _ SmallLevelThirtyFour.A_det _
    (FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 2) (thirty_four_A hk hf)

theorem thirty_five_A {k : ℕ} (hk : 0<k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 k f) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] SmallLevelThirtyFive.A=
      SmallLevelOriginal.fourierFunction k f := by
  rw [SmallLevelThirtyFive.original_A hk hf,root_six_one (by decide) (by decide),one_smul]

theorem thirty_five_B {k : ℕ} (hk : 0<k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 k f) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] SmallLevelThirtyFive.B=
      SmallLevelOriginal.fourierFunction k f := by
  rw [SmallLevelThirtyFive.B_inverse]
  simpa only [one_smul] using eigen_inverse _ _ _ SmallLevelThirtyFive.A_det 1
    (Or.inl rfl) (by simpa only [one_smul] using thirty_five_A hk hf)

#print axioms root_six_three
#print axioms root_six_two
#print axioms root_six_one
#print axioms eigen_inverse
#print axioms thirty_three_A
#print axioms thirty_three_B
#print axioms thirty_four_A
#print axioms thirty_four_B
#print axioms thirty_five_A
#print axioms thirty_five_B

end SmallLevelSixEigen
