module

public import QuantitativeArithmeticSmallLevelThirteenDiagonalV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentySix
open Matrix UpperHalfPlane SmallLevelNormalized
open QuantitativeArithmeticSmallLevelThirteen
open scoped MatrixGroups ModularForm Manifold

/-- Determinant-one representative of the level-26 hyperbolic defect matrix. -/
def hyperM : GL (Fin 2) ℝ :=
  matrix (10/3) (-1/2) (26/3) (-1) (by norm_num)

/-- Determinant-one representative of the square of the second symmetry. -/
def hyperZSquare : GL (Fin 2) ℝ :=
  matrix 25 (-9/2) 78 (-14) (by norm_num)

def hyperX : GL (Fin 2) ℝ :=
  matrix (23/3) (-4/3) (208/9) (-35/9) (by norm_num)

def hyperY : GL (Fin 2) ℝ :=
  matrix (-1) (1/2) (-26/3) (10/3) (by norm_num)

/-- The two columns are the common fixed points (13 ± √13)/52,
with the first column rescaled to determinant one. -/
def axisP : GL (Fin 2) ℝ :=
  matrix ((13+Real.sqrt 13)/(2*Real.sqrt 13)) ((13-Real.sqrt 13)/52)
    (26/Real.sqrt 13) 1 (by
      have hs : Real.sqrt 13≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
      field_simp
      ring)

theorem hyperY_mul_M : hyperY*hyperM=1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hyperY,hyperM,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two]

theorem hyperX_factor : hyperX=hyperZSquare*hyperY*hyperY := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hyperX,hyperZSquare,hyperY,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two]

theorem hyperX_axis : hyperX*axisP=axisP*diagScale scaleA scaleA_pos.ne' := by
  have hs : (Real.sqrt 13)^2=13 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 13≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have ha : 17+4*Real.sqrt 13≠0 := by positivity
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hyperX,axisP,diagScale,scaleA,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn,ha] <;> nlinarith

theorem hyperY_axis : hyperY*axisP=axisP*diagScale scaleB scaleB_pos.ne' := by
  have hs : (Real.sqrt 13)^2=13 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 13≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hb : 7-Real.sqrt 13≠0 := by
    have hh:=scaleB_pos
    dsimp [scaleB] at hh
    linarith
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hyperY,axisP,diagScale,scaleB,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn,hb] <;> nlinarith

/-- Two concrete level-26 symmetries classify any holomorphic defect.
The logarithmic independence is the already proved quadratic-unit argument
at level 13, after an exact change of generators. -/
theorem hyperbolic_classification (m : ℕ) (h : ℍ → ℂ) (hhol : MDiff h)
    (hM : h ∣[((2*m:ℕ):ℤ)] hyperM=h)
    (hZ : h ∣[((2*m:ℕ):ℤ)] hyperZSquare=h) :
    ∃ C : ℂ, ∀ z : ℍ, (z:ℂ)^m*(h ∣[((2*m:ℕ):ℤ)] axisP) z=C := by
  have hY : h ∣[((2*m:ℕ):ℤ)] hyperY=h := by
    have he : hyperY=hyperM⁻¹ := (eq_inv_iff_mul_eq_one).mpr hyperY_mul_M
    rw [he]
    have hh := congrArg (fun F : ℍ → ℂ => F ∣[((2*m:ℕ):ℤ)] hyperM⁻¹) hM
    simpa only [← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one] using hh.symm
  have hX : h ∣[((2*m:ℕ):ℤ)] hyperX=h := by
    rw [hyperX_factor,SlashAction.slash_mul,SlashAction.slash_mul,hZ,hY,hY]
  apply diagonal_classification
  · exact hhol.slash _ axisP
  · rw [← SlashAction.slash_mul,← hyperX_axis,SlashAction.slash_mul,hX]
  · rw [← SlashAction.slash_mul,← hyperY_axis,SlashAction.slash_mul,hY]

#print axioms hyperbolic_classification
end SmallLevelTwentySix
