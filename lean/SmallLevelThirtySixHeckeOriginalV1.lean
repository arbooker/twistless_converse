module

public import SmallLevelThirtySixHeckeWitnessV1
public import SmallLevelThirtySixOriginalV1
public import FinitenessAllLevelHeckePowerV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace SmallLevelThirtySix

open UpperHalfPlane Matrix FinitenessOriginalInput FinitenessOriginalFourier
  FinitenessFourierConstruction QuantitativeArithmeticRetainedReconstruction
open scoped ModularForm MatrixGroups

theorem finite_branch_point (j : ℤ) (z : ℍ) :
    ((heckeFinite j • z : ℍ) : ℂ)=((z:ℂ)+6*j)/5 := by
  rw [coe_smul_of_det_pos (by rw [heckeFinite_det]; norm_num)]
  change ((1:ℂ)*(z:ℂ)+((6*(j:ℝ):ℝ):ℂ))/((0:ℂ)*(z:ℂ)+5)=_
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

/-- Literal Euler-product input gives the six-branch relation after scaling
z by 1/6. All powers and square-root normalization are retained. -/
theorem scaled_hecke_five {f : ℕ → ℂ} (hf : EulerData 36 f) (m : ℕ)
    {z : ℂ} (hz : 0<z.im) :
    (5:ℂ)^(2*m)*scaledFourier (2*m) f (5*z)+
      scaledFourier (2*m) f (z/5)+scaledFourier (2*m) f ((z+6)/5)+
      scaledFourier (2*m) f ((z+12)/5)+scaledFourier (2*m) f ((z+18)/5)+
      scaledFourier (2*m) f ((z+24)/5)=
      FinitenessAllLevelHeckePower.scale 5 m*f 5*scaledFourier (2*m) f z := by
  have hh := FinitenessAllLevelHeckePower.original_relation
    (N:=36) (p:=5) (by decide) (by decide) m hf
    (z:=z/6) (by simpa using div_pos hz (by norm_num : (0:ℝ)<6))
  have hs : FinitenessAllLevelHeckePower.scale 5 m≠0 := by
    apply mul_ne_zero (pow_ne_zero _ (by norm_num))
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  have he := congrArg (fun v : ℂ => FinitenessAllLevelHeckePower.scale 5 m*v) hh
  simp only [mul_add, ← mul_assoc, mul_inv_cancel₀ hs, one_mul] at he
  norm_num [completeTwist, Finset.sum_range_succ] at he
  dsimp only [scaledFourier]
  ring_nf at he ⊢
  linear_combination -he

theorem original_hecke_five {f : ℕ → ℂ} (hf : EulerData 36 f) (m : ℕ) :
    heckeFive ((2*m:ℕ):ℤ) (scaledFunction (2*m) f)=
      (FinitenessAllLevelHeckePower.scale 5 m*f 5/5) • scaledFunction (2*m) f := by
  funext z
  simp only [heckeFive, Pi.add_apply, finite_branch_slash, infinity_branch_slash,
    scaledFunction, finite_branch_point, infinity_branch_point, Pi.smul_apply, smul_eq_mul]
  norm_num only [Int.cast_ofNat, Int.cast_zero, mul_zero, add_zero, mul_one]
  have hh := scaled_hecke_five hf m z.im_pos
  linear_combination hh/5

#print axioms finite_branch_point
#print axioms finite_branch_slash
#print axioms infinity_branch_slash
#print axioms scaled_hecke_five
#print axioms original_hecke_five

end SmallLevelThirtySix
