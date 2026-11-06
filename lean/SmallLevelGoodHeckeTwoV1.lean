module

public import FinitenessAllLevelHeckePowerV1
public import SmallLevelOriginalV1
public import SmallLevelNormalizedMatricesV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke
open Matrix UpperHalfPlane
open scoped MatrixGroups ModularForm

def heckeFinite (j : ℤ) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero !![1,(j:ℝ);0,2] (by norm_num [det_fin_two])
def heckeInfinity : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero !![2,0;0,1] (by norm_num [det_fin_two])
theorem heckeFinite_det (j : ℤ) : (heckeFinite j).det.val=2 := by
  simp [heckeFinite,det_fin_two]
theorem heckeInfinity_det : heckeInfinity.det.val=2 := by
  simp [heckeInfinity,det_fin_two]
theorem finite_branch_point (j : ℤ) (z : ℍ) :
    ((heckeFinite j • z : ℍ) : ℂ)=((z:ℂ)+j)/2 := by
  rw [coe_smul_of_det_pos (by rw [heckeFinite_det]; norm_num)]
  change ((1:ℂ)*(z:ℂ)+(((j:ℝ):ℝ):ℂ))/((0:ℂ)*(z:ℂ)+2)=_
  push_cast
  ring

theorem infinity_branch_point (z : ℍ) :
    ((heckeInfinity • z : ℍ) : ℂ)=2*(z:ℂ) := by
  rw [coe_smul_of_det_pos (by rw [heckeInfinity_det]; norm_num)]
  change ((2:ℂ)*(z:ℂ)+0)/((0:ℂ)*(z:ℂ)+1)=_
  ring

theorem finite_branch_slash (k : ℤ) (j : ℤ) (g : ℍ → ℂ) (z : ℍ) :
    (g ∣[k] heckeFinite j) z=g (heckeFinite j • z)/2 := by
  rw [ModularForm.slash_apply]
  have hs : σ (heckeFinite j)=ContinuousAlgEquiv.refl ℝ ℂ := by
    simp only [σ, heckeFinite_det]; norm_num
  have hd : denom (heckeFinite j) z=2 := by
    norm_num [denom, heckeFinite, GeneralLinearGroup.mkOfDetNeZero]
  rw [hs, hd, heckeFinite_det]
  norm_num only [ContinuousAlgEquiv.refl_apply, abs_of_pos (by norm_num : (0:ℝ)<2),
    Complex.ofReal_ofNat]
  rw [mul_assoc, ← zpow_add₀ (by norm_num : (2:ℂ)≠0)]
  rw [show k-1+-k=(-1:ℤ) by omega, zpow_neg_one]
  rfl

theorem infinity_branch_slash (k : ℕ) (g : ℍ → ℂ) (z : ℍ) :
    (g ∣[(k:ℤ)] heckeInfinity) z=(2:ℂ)^k*g (heckeInfinity • z)/2 := by
  rw [ModularForm.slash_apply]
  have hs : σ heckeInfinity=ContinuousAlgEquiv.refl ℝ ℂ := by
    simp only [σ, heckeInfinity_det]; norm_num
  have hd : denom heckeInfinity z=1 := by
    norm_num [denom, heckeInfinity, GeneralLinearGroup.mkOfDetNeZero]
  rw [hs, hd, heckeInfinity_det]
  norm_num only [ContinuousAlgEquiv.refl_apply, abs_of_pos (by norm_num : (0:ℝ)<2),
    Complex.ofReal_ofNat, one_zpow, mul_one]
  rw [zpow_sub₀ (by norm_num : (2:ℂ)≠0), zpow_natCast, zpow_one]
  ring


def heckeTwo (k : ℤ) (g : ℍ → ℂ) : ℍ → ℂ :=
  (g ∣[k] heckeInfinity)+(g ∣[k] heckeFinite 0)+(g ∣[k] heckeFinite 1)

#print axioms finite_branch_slash
#print axioms infinity_branch_slash
end QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke

namespace SmallLevelGoodHeckeTwo
open Matrix UpperHalfPlane Complex FinitenessOriginalInput
open FinitenessOriginalFourier FinitenessFourierConstruction
open QuantitativeArithmeticRetainedReconstruction QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke
open scoped MatrixGroups ModularForm

theorem original_hecke_two {N : ℕ} {f : ℕ → ℂ} (hgood : ¬2∣N)
    (hf : EulerData N f) (m : ℕ) :
    heckeTwo ((2*m:ℕ):ℤ) (SmallLevelOriginal.fourierFunction (2*m) f)=
      (FinitenessAllLevelHeckePower.scale 2 m*f 2/2) • SmallLevelOriginal.fourierFunction (2*m) f := by
  funext z
  simp only [heckeTwo,Pi.add_apply,finite_branch_slash,infinity_branch_slash,
    SmallLevelOriginal.fourierFunction,finite_branch_point,infinity_branch_point,
    Pi.smul_apply,smul_eq_mul]
  norm_num only [Int.cast_ofNat,Int.cast_zero,add_zero,Int.cast_one]
  have hh := FinitenessAllLevelHeckePower.original_relation
    (N:=N) (p:=2) (by decide) hgood m hf z.im_pos
  have hs : FinitenessAllLevelHeckePower.scale 2 m≠0 := by
    apply mul_ne_zero (pow_ne_zero _ (by norm_num))
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  have he := congrArg (fun v : ℂ => FinitenessAllLevelHeckePower.scale 2 m*v) hh
  simp only [mul_add,← mul_assoc,mul_inv_cancel₀ hs,one_mul] at he
  norm_num [completeTwist,Finset.sum_range_succ] at he
  ring_nf at he ⊢
  linear_combination -he/2


#print axioms original_hecke_two
end SmallLevelGoodHeckeTwo
