module

public import AsymptoticClassicalHeckeCosetsV1
public import AsymptoticAtkinLehnerSquareV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane Matrix AsymptoticAtkinLehner AsymptoticCongruenceLabels
open AsymptoticRationalGroup AsymptoticRationalFreeness AsymptoticFreshMatrices
open AsymptoticReconstructionBranch AsymptoticRationalBranches AsymptoticCongruenceStrip
open scoped ModularForm MatrixGroups

variable (N p : ℕ) (hp : 0 < p) (A B : ℤ) (hAB : (p : ℤ) * A + (N : ℤ) * B = 1)

/-- The positive determinant-p normalizer exchanging the two old directions. -/
def heckeNormalizerReal : GL (Fin 2) ℝ :=
  SpecialLinearGroup.mapGL ℝ (heckeSL N p A B hAB)⁻¹ * dilationReal p hp

def heckeNormalizerLabel : AsymptoticRationalGroup.Group :=
  integralLabel (heckeSL N p A B hAB)⁻¹ * dilationLabel p hp

theorem heckeNormalizerReal_det : (heckeNormalizerReal N p hp A B hAB).det.val = (p : ℝ) := by
  simp only [heckeNormalizerReal, map_mul, Units.val_mul]
  have hu : (SpecialLinearGroup.mapGL ℝ (heckeSL N p A B hAB)⁻¹).det.val = 1 := by simp
  rw [hu, one_mul]
  exact dilationReal_det p hp

theorem heckeNormalizer_action (z : ℍ) :
    heckeNormalizerReal N p hp A B hAB • z = heckeNormalizerLabel N p hp A B hAB • z := by
  change (SpecialLinearGroup.mapGL ℝ (heckeSL N p A B hAB)⁻¹ * dilationReal p hp) • z =
    (integralLabel (heckeSL N p A B hAB)⁻¹ * dilationLabel p hp) • z
  rw [mul_smul, mul_smul, integralLabel_action]
  change (heckeSL N p A B hAB)⁻¹ • (dilationReal p hp • z) =
    (heckeSL N p A B hAB)⁻¹ • (dilationLabel p hp • z)
  congr 1

/-- The normalizer is the inverse of the already established local
 Atkin--Lehner element in the faithful projective group. -/
theorem heckeNormalizerLabel_eq (hN : 0 < N) :
    heckeNormalizerLabel N p hp A B hAB = (localAtkin N p hN hp A B hAB)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  have hnp : ((p * N : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hp hN).ne'
  have hab : (p : ℚ) * A + (N : ℚ) * B = 1 := by exact_mod_cast hAB
  have he : (branch ((p * N : ℕ) : ℚ) 0 0 hnp * complementGL N p hN A B hAB) *
      rationalGL (heckeSL N p A B hAB)⁻¹ * dilationGL p hp =
        GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (-((p * N : ℕ) : ℚ)) (neg_ne_zero.mpr hnp)) := by
    apply Units.ext
    change ((branch ((p * N : ℕ) : ℚ) 0 0 hnp).val * (complementGL N p hN A B hAB).val) *
      ((heckeSL N p A B hAB)⁻¹.val.map (fun z : ℤ => (z : ℚ))) * (dilationGL p hp).val = _
    have hi : (heckeSL N p A B hAB)⁻¹.val.map (fun z : ℤ => (z : ℚ)) =
        !![(A : ℚ), -(B : ℚ); (N : ℚ), (p : ℚ)] := by
      rw [SpecialLinearGroup.SL2_inv_expl]
      ext i j
      fin_cases i <;> fin_cases j
      · rfl
      · change ((-B : ℤ) : ℚ) = -(B : ℚ)
        simp
      · change ((-(-(N : ℤ)) : ℤ) : ℚ) = (N : ℚ)
        simp
      · change ((p : ℤ) : ℚ) = (p : ℚ)
        simp
    rw [hi]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [branch, complementGL, AsymptoticFreshMatrices.representative, entries,
        dilationGL, GeneralLinearGroup.mkOfDetNeZero, GeneralLinearGroup.scalar,
        Matrix.scalar, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals ring_nf
    all_goals first
      | exact Or.inl True.intro
      | linear_combination -(N : ℚ) * (p : ℚ) * hab
  apply Subtype.ext
  apply Subtype.ext
  change (rationalMap (branch ((p * N : ℕ) : ℚ) 0 0 hnp) *
    rationalMap (complementGL N p hN A B hAB)) *
      (rationalMap (rationalGL (heckeSL N p A B hAB)⁻¹) * rationalMap (dilationGL p hp)) = 1
  rw [← mul_assoc, ← map_mul, ← map_mul, ← map_mul, he, rationalMap_scalar]

theorem heckeNormalizer_conj_mem (hN : 0 < N) {a : AsymptoticRationalGroup.Group}
    (ha : a ∈ gamma (p * N)) :
    heckeNormalizerLabel N p hp A B hAB * a * (heckeNormalizerLabel N p hp A B hAB)⁻¹ ∈
      gamma (p * N) := by
  rw [heckeNormalizerLabel_eq N p hp A B hAB hN, inv_inv]
  exact local_inv_conj_mem N p hN hp A B hAB ha

theorem heckeNormalizer_inv_conj_mem (hN : 0 < N) {a : AsymptoticRationalGroup.Group}
    (ha : a ∈ gamma (p * N)) :
    (heckeNormalizerLabel N p hp A B hAB)⁻¹ * a * heckeNormalizerLabel N p hp A B hAB ∈
      gamma (p * N) := by
  rw [heckeNormalizerLabel_eq N p hp A B hAB hN, inv_inv]
  exact local_conj_mem N p hN hp A B hAB ha

#print axioms heckeNormalizerReal_det
#print axioms heckeNormalizer_action
#print axioms heckeNormalizerLabel_eq
#print axioms heckeNormalizer_conj_mem
#print axioms heckeNormalizer_inv_conj_mem

end AsymptoticClassicalCusp
