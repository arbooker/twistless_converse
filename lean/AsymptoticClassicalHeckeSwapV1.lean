module

public import AsymptoticClassicalHeckeNormalizerV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane Matrix AsymptoticAtkinLehner AsymptoticClassicalDiscriminant
open AsymptoticCongruenceLabels
open scoped ModularForm MatrixGroups

variable (N p : ℕ) (hp : 0 < p) (A B : ℤ) (hAB : (p : ℤ) * A + (N : ℤ) * B = 1)

def positiveScalarReal : GL (Fin 2) ℝ :=
  triangularGL p 0 p (by exact_mod_cast hp) (by exact_mod_cast hp)

/-- The scalar matrix p*I acts by the exact factor p^(k-2). -/
theorem slash_positiveScalarReal (k : ℤ) (f : ℍ → ℂ) :
    f ∣[k] positiveScalarReal p hp = (p : ℂ) ^ (k - 2) • f := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have ht : triangularFactor p p k = (p : ℂ) ^ (k - 2) := by
    simp only [triangularFactor, Complex.ofReal_mul, Complex.ofReal_natCast, mul_zpow]
    rw [← zpow_add₀ hpC, ← zpow_add₀ hpC]
    congr 1
    omega
  funext z
  rw [positiveScalarReal, slash_triangular, ht]
  have hz : affine ((p : ℝ) / p) (by positivity) (0 / p) z = z := by
    apply UpperHalfPlane.ext
    simp [affine, hpR]
  rw [hz]
  rfl

/-- The normalizer exchanges D_p with a scalar times a level-N matrix. -/
theorem heckeNormalizer_product :
    dilationReal p hp * heckeNormalizerReal N p hp A B hAB =
      positiveScalarReal p hp * SpecialLinearGroup.mapGL ℝ (traceSL N p A B hAB 0)⁻¹ := by
  let D := dilationReal p hp
  let U := SpecialLinearGroup.mapGL ℝ (heckeSL N p A B hAB)
  let T := SpecialLinearGroup.mapGL ℝ (traceSL N p A B hAB 0)
  let J := triangularGL 1 0 p (by norm_num) (by exact_mod_cast hp)
  have he : D * T = U * J := by
    simpa only [Int.cast_zero] using dilation_traceSL N p hp A B hAB 0
  have hj : D * J = positiveScalarReal p hp := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D, J, dilationReal, dilationGL, GeneralLinearGroup.map, positiveScalarReal,
        triangularGL, GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]
  have hr : heckeNormalizerReal N p hp A B hAB = U⁻¹ * D := by
    rw [heckeNormalizerReal, map_inv]
  change D * heckeNormalizerReal N p hp A B hAB = positiveScalarReal p hp * _
  rw [hr, map_inv]
  change D * (U⁻¹ * D) = positiveScalarReal p hp * T⁻¹
  calc
    D * (U⁻¹ * D) = (D * U⁻¹ * (D * T)) * T⁻¹ := by group
    _ = _ := by rw [he, mul_assoc D U⁻¹, inv_mul_cancel_left, hj]

/-- Slash by the determinant-p normalizer sends inclusion to slash dilation. -/
theorem slash_heckeNormalizer (k : ℤ) (f : CuspForm (level N) k) :
    (f : ℍ → ℂ) ∣[k] heckeNormalizerReal N p hp A B hAB =
      (f : ℍ → ℂ) ∣[k] dilationReal p hp := by
  rw [heckeNormalizerReal, SlashAction.slash_mul]
  have hi : (f : ℍ → ℂ) ∣[k] SpecialLinearGroup.mapGL ℝ (heckeSL N p A B hAB)⁻¹ =
      (f : ℍ → ℂ) := f.slash_action_eq' _
    ⟨_, (CongruenceSubgroup.Gamma0 N).inv_mem (heckeSL_mem N p A B hAB), rfl⟩
  rw [hi]

/-- In the opposite direction the normalizer produces the Petersson
 determinant factor, which will cancel in the adjointness calculation. -/
theorem slash_dilation_heckeNormalizer (k : ℤ) (f : CuspForm (level N) k) :
    ((f : ℍ → ℂ) ∣[k] dilationReal p hp) ∣[k] heckeNormalizerReal N p hp A B hAB =
      (p : ℂ) ^ (k - 2) • (f : ℍ → ℂ) := by
  rw [← SlashAction.slash_mul, heckeNormalizer_product, SlashAction.slash_mul,
    slash_positiveScalarReal]
  change ((p : ℂ) ^ (k - 2) • (f : ℍ → ℂ)) ∣[k] (traceSL N p A B hAB 0)⁻¹ = _
  rw [ModularForm.SL_smul_slash]
  have hi : (f : ℍ → ℂ) ∣[k] (traceSL N p A B hAB 0)⁻¹ = (f : ℍ → ℂ) :=
    f.slash_action_eq' _ ⟨_, (CongruenceSubgroup.Gamma0 N).inv_mem (traceSL_mem N p A B hAB 0), rfl⟩
  rw [hi]

#print axioms slash_positiveScalarReal
#print axioms heckeNormalizer_product
#print axioms slash_heckeNormalizer
#print axioms slash_dilation_heckeNormalizer

end AsymptoticClassicalCusp
