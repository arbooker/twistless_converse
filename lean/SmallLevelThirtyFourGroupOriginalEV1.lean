module

public import SmallLevelRamifiedTwoRootV1
public import SmallLevelSixRootsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourGroup
open Matrix UpperHalfPlane ModularGroup SmallLevelNormalized SmallLevelGenerators
  FinitenessPolynomialSeries FinitenessFourierConstruction Complex
open scoped MatrixGroups ModularForm

def E : GL (Fin 2) ℝ :=
  matrix (2/Real.sqrt 2) (-1/Real.sqrt 2) (-34/Real.sqrt 2) (18/Real.sqrt 2) (by
    have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
    field_simp [SmallLevelRamifiedTwo.sqrt_two_ne]
    nlinarith)

def W : GL (Fin 2) ℝ := fricke 34 (by decide)

theorem E_det : (GeneralLinearGroup.det E:ℝ)=1 := matrix_det _ _ _ _ _

theorem E_inverse : E=(SmallLevelRamifiedTwo.Q 34 18 (by decide))⁻¹ := by
  apply (eq_inv_iff_mul_eq_one).mpr
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [E,SmallLevelRamifiedTwo.Q,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two] <;>
    field_simp [SmallLevelRamifiedTwo.sqrt_two_ne] <;> nlinarith

theorem original_E {k : ℕ} {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 k f) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] E=
      FinitenessNormalizedTwistProduct.root 34 f 2 • SmallLevelOriginal.fourierFunction k f := by
  rw [E_inverse]
  exact SmallLevelSixEigen.eigen_inverse _ _ _ (SmallLevelRamifiedTwo.Q_det _ _ _)
    _ (FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 2)
    (SmallLevelRamifiedTwo.original_eigen_root (by decide : 0<34) (by decide : 2*18=34+2)
      (by decide : Nat.lcm 34 (2^2)=2*34) hf)


#print axioms original_E
end SmallLevelThirtyFourGroup
