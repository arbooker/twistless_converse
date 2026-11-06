module

public import SmallLevelGoodHeckeTwoV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelGoodHeckeFive
open Matrix UpperHalfPlane FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open QuantitativeArithmeticRetainedReconstruction
open scoped MatrixGroups ModularForm

def heckeFinite (j : ℤ) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero !![1,(j:ℝ);0,5] (by norm_num [det_fin_two])
def heckeInfinity : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero !![5,0;0,1] (by norm_num [det_fin_two])
theorem heckeFinite_det (j : ℤ) : (heckeFinite j).det.val=5 := by
  simp [heckeFinite,det_fin_two]
theorem heckeInfinity_det : heckeInfinity.det.val=5 := by
  simp [heckeInfinity,det_fin_two]
theorem finite_branch_point (j : ℤ) (z : ℍ) :
    ((heckeFinite j • z : ℍ) : ℂ)=((z:ℂ)+j)/5 := by
  rw [coe_smul_of_det_pos (by rw [heckeFinite_det]; norm_num)]
  change ((1:ℂ)*(z:ℂ)+(((j:ℝ):ℝ):ℂ))/((0:ℂ)*(z:ℂ)+5)=_
  push_cast
  ring

theorem infinity_branch_point (z : ℍ) :
    ((heckeInfinity • z : ℍ) : ℂ)=5*(z:ℂ) := by
  rw [coe_smul_of_det_pos (by rw [heckeInfinity_det]; norm_num)]
  change ((5:ℂ)*(z:ℂ)+0)/((0:ℂ)*(z:ℂ)+1)=_
  ring

theorem finite_branch_slash (k : ℤ) (j : ℤ) (g : ℍ → ℂ) (z : ℍ) :
    (g ∣[k] heckeFinite j) z=g (heckeFinite j • z)/5 := by
  rw [ModularForm.slash_apply]
  have hs : σ (heckeFinite j)=ContinuousAlgEquiv.refl ℝ ℂ := by
    simp only [σ, heckeFinite_det]; norm_num
  have hd : denom (heckeFinite j) z=5 := by
    norm_num [denom, heckeFinite, GeneralLinearGroup.mkOfDetNeZero]
  rw [hs, hd, heckeFinite_det]
  norm_num only [ContinuousAlgEquiv.refl_apply, abs_of_pos (by norm_num : (0:ℝ)<5),
    Complex.ofReal_ofNat]
  rw [mul_assoc, ← zpow_add₀ (by norm_num : (5:ℂ)≠0)]
  rw [show k-1+-k=(-1:ℤ) by omega, zpow_neg_one]
  rfl

theorem infinity_branch_slash (k : ℕ) (g : ℍ → ℂ) (z : ℍ) :
    (g ∣[(k:ℤ)] heckeInfinity) z=(5:ℂ)^k*g (heckeInfinity • z)/5 := by
  rw [ModularForm.slash_apply]
  have hs : σ heckeInfinity=ContinuousAlgEquiv.refl ℝ ℂ := by
    simp only [σ, heckeInfinity_det]; norm_num
  have hd : denom heckeInfinity z=1 := by
    norm_num [denom, heckeInfinity, GeneralLinearGroup.mkOfDetNeZero]
  rw [hs, hd, heckeInfinity_det]
  norm_num only [ContinuousAlgEquiv.refl_apply, abs_of_pos (by norm_num : (0:ℝ)<5),
    Complex.ofReal_ofNat, one_zpow, mul_one]
  rw [zpow_sub₀ (by norm_num : (5:ℂ)≠0), zpow_natCast, zpow_one]
  ring


def heckeFive (k : ℤ) (g : ℍ → ℂ) : ℍ → ℂ :=
  (g ∣[k] heckeInfinity)+(g ∣[k] heckeFinite 0)+(g ∣[k] heckeFinite 1)+
    (g ∣[k] heckeFinite 2)+(g ∣[k] heckeFinite 3)+(g ∣[k] heckeFinite 4)

theorem original_hecke_five {N : ℕ} {f : ℕ → ℂ} (hgood : ¬5∣N)
    (hf : EulerData N f) (m : ℕ) :
    heckeFive ((2*m:ℕ):ℤ) (SmallLevelOriginal.fourierFunction (2*m) f)=
      (FinitenessAllLevelHeckePower.scale 5 m*f 5/5) • SmallLevelOriginal.fourierFunction (2*m) f := by
  funext z
  simp only [heckeFive,Pi.add_apply,finite_branch_slash,infinity_branch_slash,
    SmallLevelOriginal.fourierFunction,finite_branch_point,infinity_branch_point,
    Pi.smul_apply,smul_eq_mul]
  norm_num only [Int.cast_ofNat,Int.cast_zero,add_zero,Int.cast_one]
  have hh := FinitenessAllLevelHeckePower.original_relation
    (N:=N) (p:=5) (by decide) hgood m hf z.im_pos
  have hs : FinitenessAllLevelHeckePower.scale 5 m≠0 := by
    apply mul_ne_zero (pow_ne_zero _ (by norm_num))
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  have he := congrArg (fun v : ℂ => FinitenessAllLevelHeckePower.scale 5 m*v) hh
  simp only [mul_add,← mul_assoc,mul_inv_cancel₀ hs,one_mul] at he
  norm_num [completeTwist,Finset.sum_range_succ] at he
  ring_nf at he ⊢
  linear_combination -he/5


#print axioms original_hecke_five
end SmallLevelGoodHeckeFive
