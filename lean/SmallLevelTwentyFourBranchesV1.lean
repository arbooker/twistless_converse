module

public import SmallLevelTwentyFourFrickeV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace SmallLevelTwentyFour

open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

theorem sqrt_three_ne : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'

def A : GL (Fin 2) ℝ := matrix (3/Real.sqrt 3) (1/Real.sqrt 3)
    (6/Real.sqrt 3) (3/Real.sqrt 3) (by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  field_simp [sqrt_three_ne]
  nlinarith)

def B : GL (Fin 2) ℝ := matrix (3/Real.sqrt 3) (-1/Real.sqrt 3)
    (-6/Real.sqrt 3) (3/Real.sqrt 3) (by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  field_simp [sqrt_three_ne]
  nlinarith)

theorem A_det : (GeneralLinearGroup.det A:ℝ)=1 := matrix_det _ _ _ _ _
theorem B_det : (GeneralLinearGroup.det B:ℝ)=1 := matrix_det _ _ _ _ _

theorem sqrt_eighteen : Real.sqrt 18=Real.sqrt 6*Real.sqrt 3 := by
  rw [← Real.sqrt_mul (by norm_num : (0:ℝ)≤6)]
  norm_num

theorem fricke_branch_pos : fricke 6 (by decide)*B*translation (1/3)=
    translation (1/3)*fricke 18 (by decide) := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 6)^2=6 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 6≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke, B, translation, matrix, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply, Fin.sum_univ_two, sqrt_eighteen] <;>
    field_simp [sqrt_three_ne, hn] <;> norm_num [hs, ht]

theorem fricke_branch_neg : fricke 6 (by decide)*A*translation (-(1/3))=
    translation (-(1/3))*fricke 18 (by decide) := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 6)^2=6 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 6≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke, A, translation, matrix, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply, Fin.sum_univ_two, sqrt_eighteen] <;>
    field_simp [sqrt_three_ne, hn] <;> norm_num [hs, ht]

/-- The actual ramified-three pair, with the same original root sign on
both branches and no restriction on a Hecke eigenvalue. -/
theorem original_pair {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 24 k f) :
    ∃ δ : ℂ, (δ=1 ∨ δ= -1) ∧
    ((SmallLevelEvenScale.scaledFunction k f ∣[(k:ℤ)] B) ∣[(k:ℤ)] translation (1/3))+
      ((SmallLevelEvenScale.scaledFunction k f ∣[(k:ℤ)] A) ∣[(k:ℤ)] translation (-(1/3)))=
    δ • ((SmallLevelEvenScale.scaledFunction k f ∣[(k:ℤ)] translation (1/3))+
      (SmallLevelEvenScale.scaledFunction k f ∣[(k:ℤ)] translation (-(1/3)))) := by
  obtain ⟨δ,hδ,hh⟩ := original_pair_fricke hf
  refine ⟨δ,hδ,?_⟩
  have hp : (fricke 6 (by decide))⁻¹*translation (1/3)*fricke 18 (by decide)=B*translation (1/3) := by
    rw [mul_assoc, ← fricke_branch_pos]
    group
  have hn : (fricke 6 (by decide))⁻¹*translation (-(1/3))*fricke 18 (by decide)=A*translation (-(1/3)) := by
    rw [mul_assoc, ← fricke_branch_neg]
    group
  rw [hp, hn, SlashAction.slash_mul, SlashAction.slash_mul] at hh
  exact hh

#print axioms fricke_branch_pos
#print axioms fricke_branch_neg
#print axioms original_pair

end SmallLevelTwentyFour
