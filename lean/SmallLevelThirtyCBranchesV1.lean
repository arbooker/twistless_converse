module

public import SmallLevelThirtyCMatricesV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace SmallLevelThirtyC

open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

theorem sqrt_240 : Real.sqrt 240=2*Real.sqrt 30*Real.sqrt 2 := by
  rw [mul_assoc, ← Real.sqrt_mul (by norm_num : (0:ℝ)≤30)]
  rw [show (240:ℝ)=4*(30*2) by norm_num,Real.sqrt_mul (by norm_num)]
  norm_num

theorem fricke_branch_pos : fricke 30 (by decide)*C*translation (1/4)=
    translation (1/4)*fricke 240 (by decide) := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 30)^2=30 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke, C, translation, matrix, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply, Fin.sum_univ_two, sqrt_240] <;>
    field_simp [sqrt_2_ne, sqrt_30_ne] <;> norm_num [hs, ht]

theorem fricke_branch_neg : fricke 30 (by decide)*Cp*translation (-(1/4))=
    translation (-(1/4))*fricke 240 (by decide) := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 30)^2=30 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke, Cp, translation, matrix, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply, Fin.sum_univ_two, sqrt_240] <;>
    field_simp [sqrt_2_ne, sqrt_30_ne] <;> norm_num [hs, ht]

theorem original_pair {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 30 k f) :
    ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] C) ∣[(k:ℤ)] translation (1/4))+
      ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] Cp) ∣[(k:ℤ)] translation (-(1/4)))=
    FinitenessNormalizedTwistProduct.root 30 f 4 •
      ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (1/4))+
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-(1/4)))) := by
  have hh := SmallLevelThirty.original_pair_four_exact hf
  have hp : (fricke 30 (by decide))⁻¹*translation (1/4)*fricke 240 (by decide)=C*translation (1/4) := by
    rw [mul_assoc, ← fricke_branch_pos]
    group
  have hn : (fricke 30 (by decide))⁻¹*translation (-(1/4))*fricke 240 (by decide)=Cp*translation (-(1/4)) := by
    rw [mul_assoc, ← fricke_branch_neg]
    group
  rw [hp, hn, SlashAction.slash_mul, SlashAction.slash_mul] at hh
  exact hh

#print axioms original_pair

end SmallLevelThirtyC
