module

public import QuantitativeArithmeticSmallLevelTwentyTwoEllipticV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm Manifold

/-- The first infinite-order elliptic matrix in the final level22 argument. -/
def Z : GL (Fin 2) ℝ := matrix (99/(15*Real.sqrt 11)) (38/(15*Real.sqrt 11))
    (-495/(15*Real.sqrt 11)) (-165/(15*Real.sqrt 11)) (by
      have hs : (Real.sqrt 11)^2=11 := Real.sq_sqrt (by norm_num)
      field_simp
      nlinarith)

/-- The signed representative of the second elliptic word K*L*A0. -/
def Vrat : SL(2,ℚ) := ⟨!![-10/3,-1;11,3],by norm_num [det_fin_two]⟩
def V : GL (Fin 2) ℝ := SpecialLinearGroup.mapGL ℝ Vrat

theorem Z_det : (GeneralLinearGroup.det Z:ℝ)=1 := matrix_det _ _ _ _ _
theorem V_det : (GeneralLinearGroup.det V:ℝ)=1 := by simp [V]

theorem Z_square : Z*Z=Zsquare.ellipticReal := by
  have hs : (Real.sqrt 11)^2=11 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 11≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Z,Zsquare.ellipticReal,Zsquare.elliptic,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,Matrix.mul_apply,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

theorem V_square : V*V=Vsquare.ellipticReal := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [V,Vrat,Vsquare.ellipticReal,Vsquare.elliptic,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,Matrix.mul_apply,Fin.sum_univ_two]

private theorem sign_square {k : ℤ} (H : ℍ→ℂ) (A : GL (Fin 2) ℝ)
    (hd : (GeneralLinearGroup.det A:ℝ)=1) (χ : ℂ) (hχ : χ=1 ∨ χ= -1)
    (he : H ∣[k] A=χ • H) : H ∣[k] (A*A)=H := by
  rw [SlashAction.slash_mul,he,det_one_smul _ hd,he,smul_smul]
  rcases hχ with rfl|rfl <;> simp

/-- Either sign of Z forces a positive-weight holomorphic function to vanish. -/
theorem Z_eigen_zero {k : ℕ} (hk : 0<k) (H : ℍ→ℂ) (hhol : MDiff H)
    (χ : ℂ) (hχ : χ=1 ∨ χ= -1) (he : H ∣[(k:ℤ)] Z=χ • H) : H=0 := by
  have hh:=sign_square H Z Z_det χ hχ he
  rw [Z_square] at hh
  exact Zsquare.invariant_zero hk H hhol hh

/-- Either sign of V forces a positive-weight holomorphic function to vanish. -/
theorem V_eigen_zero {k : ℕ} (hk : 0<k) (H : ℍ→ℂ) (hhol : MDiff H)
    (χ : ℂ) (hχ : χ=1 ∨ χ= -1) (he : H ∣[(k:ℤ)] V=χ • H) : H=0 := by
  have hh:=sign_square H V V_det χ hχ he
  rw [V_square] at hh
  exact Vsquare.invariant_zero hk H hhol hh

#print axioms Z_square
#print axioms V_square
#print axioms Z_eigen_zero
#print axioms V_eigen_zero
end QuantitativeArithmeticSmallLevelTwentyTwo
