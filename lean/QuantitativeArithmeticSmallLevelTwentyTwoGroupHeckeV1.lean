module

public import QuantitativeArithmeticSmallLevelTwentyTwoReflectionLawsV1
public import QuantitativeArithmeticSmallLevelTwentyTwoFinishAlgebraV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix UpperHalfPlane SmallLevelNormalized FinitenessOriginalFourier
  FinitenessFourierConstruction QuantitativeArithmeticRetainedReconstruction
open scoped MatrixGroups ModularForm

def M (j : ℤ) : GL (Fin 2) ℝ := matrix (1/Real.sqrt 2) (j/Real.sqrt 2) 0 (Real.sqrt 2)
  (by field_simp; ring)

theorem M_det (j : ℤ) : (GeneralLinearGroup.det (M j):ℝ)=1 := matrix_det _ _ _ _ _
theorem M_point (j : ℤ) (z : ℍ) : ((M j • z:ℍ):ℂ)=((z:ℂ)+j)/2 := by
  rw [coe_smul_of_det_pos (by rw [M_det]; norm_num)]
  have hs : (Real.sqrt 2:ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hn : (Real.sqrt 2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  norm_num [num,denom,M,matrix,GeneralLinearGroup.mkOfDetNeZero]
  field_simp [hn]
  linear_combination -(z:ℂ)*hs-(j:ℂ)*hs

theorem M_slash (m : ℕ) (j : ℤ) (g : ℍ→ℂ) (z : ℍ) :
    (g ∣[((2*m:ℕ):ℤ)] M j) z=g (M j • z)/(2:ℂ)^m := by
  rw [det_one_slash _ (M_det j)]
  have hd : denom (M j) z=(Real.sqrt 2:ℂ) := by norm_num [denom,M,matrix,GeneralLinearGroup.mkOfDetNeZero]
  rw [hd,zpow_neg,zpow_natCast,pow_mul]
  have hs : (Real.sqrt 2:ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  rw [hs]
  rfl

/-- The original ramified Euler coefficient gives the actual determinant-one
slash sum, with the same root used by the normalized matrix E. -/
theorem original_ramified_slash (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) :
    let F:=SmallLevelOriginal.fourierFunction (2*m) f
    (F ∣[((2*m:ℕ):ℤ)] M 0)+(F ∣[((2*m:ℕ):ℤ)] M 1)=
      (-FinitenessNormalizedTwistProduct.root 22 f 2) • F := by
  funext z
  simp only [Pi.add_apply,M_slash,SmallLevelOriginal.fourierFunction,M_point,
    Pi.smul_apply,smul_eq_mul,Int.cast_zero,Int.cast_one,add_zero]
  have hz : 0<((z:ℂ)/2).im := by simpa using div_pos z.im_pos (by norm_num : (0:ℝ)<2)
  have hh:=QuantitativeArithmeticRamifiedFullTrace.original_complete_even hf.toEulerData
    (by decide : Nat.Prime 2) (by decide : 2∣22) hm hz
  norm_num [completeTwist,Finset.sum_range_succ,QuantitativeArithmeticRamifiedFullTrace.multiplier] at hh
  rw [show (2:ℂ)*((z:ℂ)/2)=(z:ℂ) by ring] at hh
  have ha : ((z:ℂ)+1)/2=(z:ℂ)/2+1/2 := by ring
  rw [ha,root_two,neg_neg,← add_div,hh]
  field_simp

#print axioms M_slash
#print axioms original_ramified_slash
end QuantitativeArithmeticSmallLevelTwentyTwo
