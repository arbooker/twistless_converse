module

public import SmallLevelThreePairV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelThree

open Matrix UpperHalfPlane
open scoped MatrixGroups ModularForm

def upperBranch (j : ℤ) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero !![1,(j:ℝ);0,3] (by norm_num [det_fin_two])

theorem upperBranch_det (j : ℤ) : (GeneralLinearGroup.det (upperBranch j):ℝ)=3 := by
  simp [upperBranch, det_fin_two]

theorem upperBranch_point (j : ℤ) (z : ℍ) :
    ((upperBranch j • z : ℍ):ℂ)=((z:ℂ)+j)/3 := by
  rw [coe_smul_of_det_pos (by rw [upperBranch_det]; norm_num)]
  change (1*(z:ℂ)+((j:ℝ):ℂ))/(0*(z:ℂ)+3)=_
  push_cast
  ring

theorem upperBranch_slash (k : ℤ) (j : ℤ) (F : ℍ → ℂ) (z : ℍ) :
    (F ∣[k] upperBranch j) z=F (upperBranch j • z)/3 := by
  rw [ModularForm.slash_apply]
  have hs : σ (upperBranch j)=ContinuousAlgEquiv.refl ℝ ℂ := by
    simp only [σ, upperBranch_det]; norm_num
  have hd : denom (upperBranch j) z=3 := by
    norm_num [denom, upperBranch, GeneralLinearGroup.mkOfDetNeZero]
  rw [hs, hd, upperBranch_det]
  norm_num only [ContinuousAlgEquiv.refl_apply, abs_of_pos (by norm_num : (0:ℝ)<3),
    Complex.ofReal_ofNat]
  rw [mul_assoc, ← zpow_add₀ (by norm_num : (3:ℂ)≠0)]
  rw [show k-1+-k=(-1:ℤ) by omega, zpow_neg_one]
  rfl

theorem lowerBranch_slash (k : ℕ) (N : ℕ) (j : ℤ) (F : ℍ → ℂ) (z : ℍ) :
    (F ∣[(k:ℤ)] lowerBranch N j) z=
      (3:ℂ)^k*(F (lowerBranch N j • z)/((j:ℂ)*N*(z:ℂ)+1)^k)/3 := by
  rw [ModularForm.slash_apply]
  have hs : σ (lowerBranch N j)=ContinuousAlgEquiv.refl ℝ ℂ := by
    simp only [σ, lowerBranch_det]; norm_num
  rw [hs, lowerBranch_denom, lowerBranch_det]
  norm_num only [ContinuousAlgEquiv.refl_apply, abs_of_pos (by norm_num : (0:ℝ)<3),
    Complex.ofReal_ofNat]
  rw [zpow_sub₀ (by norm_num : (3:ℂ)≠0), zpow_natCast, zpow_one,
    zpow_neg, zpow_natCast]
  ring

theorem original_pair_slash {N k : ℕ} (hN : 0<N) (hgood : ¬3∣N)
    {f : ℕ → ℂ} (hf : FinitenessOriginalInput.IsSolution N k f) :
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] upperBranch 1)+
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] upperBranch (-1))=
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] lowerBranch N 1)+
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] lowerBranch N (-1)) := by
  funext z
  simp only [Pi.add_apply, upperBranch_slash, lowerBranch_slash,
    SmallLevelOriginal.fourierFunction, upperBranch_point,
    Int.cast_one, Int.cast_neg, one_mul, neg_one_mul]
  have hh := original_pair hN hgood hf z
  simp only [sub_eq_add_neg] at hh
  linear_combination hh/3

#print axioms upperBranch_slash
#print axioms lowerBranch_slash
#print axioms original_pair_slash

end SmallLevelThree
