module

public import AsymptoticClassicalLocalAtkinOperatorV1
public import AsymptoticClassicalPeterssonNormalizerV1
public import Mathlib.Analysis.InnerProductSpace.Symmetric

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane Matrix AsymptoticAtkinLehner AsymptoticClassicalPetersson
open AsymptoticClassicalDiscriminant AsymptoticCongruenceLabels
open scoped ModularForm MatrixGroups InnerProduct

variable (M p : ℕ) (hp : 0 < p) (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)

/-- The two determinant-p representatives are adjugates. -/
theorem heckeNormalizer_localAtkin :
    heckeNormalizerReal M p hp A B hAB * localAtkinReal M p hp A B hAB =
      positiveScalarReal p hp := by
  let U := SpecialLinearGroup.mapGL ℝ (heckeSL M p A B hAB)
  have hd : dilationReal p hp * upperDilationReal p hp = positiveScalarReal p hp := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dilationReal, dilationGL, upperDilationReal, upperDilationGL,
        GeneralLinearGroup.map, positiveScalarReal, triangularGL,
        GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]
  rw [heckeNormalizerReal, localAtkinReal, map_inv]
  change U⁻¹ * dilationReal p hp * (upperDilationReal p hp * U) = _
  rw [mul_assoc, ← mul_assoc (dilationReal p hp), hd]
  rw [← scalar_eq_positiveScalarReal p hp, ← mul_assoc, ← GeneralLinearGroup.scalar_commute]
  group

/-- On the original level the adjugate representative has the same slash action. -/
theorem slash_localAtkin_eq_normalizer (k : ℤ) (f : CuspForm (level (p * M)) k) :
    (f : ℍ → ℂ) ∣[k] localAtkinReal M p hp A B hAB =
      (f : ℍ → ℂ) ∣[k] heckeNormalizerReal M p hp A B hAB := by
  have he : localAtkinReal M p hp A B hAB =
      SpecialLinearGroup.mapGL ℝ (localSquare M p A B hAB) * heckeNormalizerReal M p hp A B hAB := by
    apply mul_right_cancel (b := localAtkinReal M p hp A B hAB)
    rw [localAtkinReal_square, mul_assoc, heckeNormalizer_localAtkin,
      scalar_eq_positiveScalarReal p hp]
  rw [he, SlashAction.slash_mul]
  have hi : (f : ℍ → ℂ) ∣[k] SpecialLinearGroup.mapGL ℝ (localSquare M p A B hAB) = f :=
    f.slash_action_eq' _ ⟨_, localSquare_mem M p A B hAB, rfl⟩
  rw [hi]

/-- Petersson covariance for the actual unscaled local Atkin operator. -/
theorem localAtkinOperator_inner [NeZero M] [NeZero (p * M)] (k : ℤ)
    (f g : CuspForm (level (p * M)) k) :
    inner ℂ (localAtkinOperator M p hp A B hAB k f) (localAtkinOperator M p hp A B hAB k g) =
      (p : ℂ) ^ (k - 2) * inner ℂ f g := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hh := inner_slash_normalizer (p * M) k (heckeNormalizerLabel M p hp A B hAB)
    (heckeNormalizerReal M p hp A B hAB)
    (by rw [heckeNormalizerReal_det]; exact_mod_cast hp)
    (heckeNormalizer_action M p hp A B hAB)
    (fun _ ha => heckeNormalizer_conj_mem M p hp A B hAB hM ha)
    (fun _ ha => heckeNormalizer_inv_conj_mem M p hp A B hAB hM ha)
    f g (localAtkinOperator M p hp A B hAB k f) (localAtkinOperator M p hp A B hAB k g)
    (slash_localAtkin_eq_normalizer M p hp A B hAB k f)
    (slash_localAtkin_eq_normalizer M p hp A B hAB k g)
  simpa only [heckeNormalizerReal_det, Complex.ofReal_natCast] using hh

/-- Covariance and the scalar square imply symmetry without normalizing the operator. -/
theorem localAtkinOperator_isSymmetric [NeZero M] [NeZero (p * M)] (k : ℤ) :
    (localAtkinOperator M p hp A B hAB k).IsSymmetric := by
  intro f g
  have hh := localAtkinOperator_inner M p hp A B hAB k f
    (localAtkinOperator M p hp A B hAB k g)
  rw [localAtkinOperator_square, inner_smul_right] at hh
  exact mul_left_cancel₀ (zpow_ne_zero (k - 2) (show (p : ℂ) ≠ 0 by exact_mod_cast hp.ne')) hh

#print axioms heckeNormalizer_localAtkin
#print axioms slash_localAtkin_eq_normalizer
#print axioms localAtkinOperator_inner
#print axioms localAtkinOperator_isSymmetric

end AsymptoticClassicalCusp
