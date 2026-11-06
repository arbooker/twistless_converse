module

public import AsymptoticClassicalIntegralTriangularV1
public import AsymptoticClassicalTriangularSlashV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalDiscriminant

open UpperHalfPlane Matrix AsymptoticClassicalCusp AsymptoticCongruenceLabels
open scoped MatrixGroups

/-- Triangular reduction of diag(N,1)*A, retaining the determinant and
 the lower-left entry needed to recover the congruence condition. -/
theorem dilation_triangular (N : ℕ) (hN : 0 < N) (A : SL(2, ℤ)) :
    ∃ (U : SL(2, ℤ)) (a b d : ℤ) (ha : 0 < a) (hd : 0 < d),
      a * d = (N : ℤ) ∧ A 1 0 = U 1 0 * a ∧
      dilationReal N hN * SpecialLinearGroup.mapGL ℝ A =
        SpecialLinearGroup.mapGL ℝ U *
          triangularGL (a : ℝ) (b : ℝ) (d : ℝ) (by exact_mod_cast ha) (by exact_mod_cast hd) := by
  let B : Matrix (Fin 2) (Fin 2) ℤ := !![(N : ℤ), 0; 0, 1] * A.val
  have hdet : B.det = (N : ℤ) := by
    change (!![(N : ℤ), 0; 0, 1] * A.val).det = _
    rw [Matrix.det_mul, A.property, mul_one]
    simp [Matrix.det_fin_two]
  obtain ⟨U, a, b, d, ha, hd, he⟩ := integral_triangular B (by rw [hdet]; exact_mod_cast hN)
  have had : a * d = (N : ℤ) := by
    have hh := congrArg Matrix.det he
    rw [hdet, Matrix.det_mul, U.property, one_mul] at hh
    simpa [Matrix.det_fin_two] using hh.symm
  have hc : A 1 0 = U 1 0 * a := by
    have hh := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℤ => X 1 0) he
    change (!![(N : ℤ), 0; 0, 1] * A.val) 1 0 = (U.val * !![a, b; 0, d]) 1 0 at hh
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at hh
    simpa using hh
  refine ⟨U, a, b, d, ha, hd, had, hc, ?_⟩
  apply Units.ext
  change (dilationReal N hN).val * A.val.map (Int.castRingHom ℝ) =
    U.val.map (Int.castRingHom ℝ) * !![(a : ℝ), (b : ℝ); 0, (d : ℝ)]
  ext i j
  have hh := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℤ => (X i j : ℝ)) he
  change (((!![(N : ℤ), 0; 0, 1] * A.val) i j : ℤ) : ℝ) =
    (((U.val * !![a, b; 0, d]) i j : ℤ) : ℝ) at hh
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add, Int.cast_mul] at hh
  fin_cases i <;> fin_cases j <;>
    simpa [dilationReal, dilationGL, GeneralLinearGroup.map, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply, Fin.sum_univ_two] using hh

#print axioms dilation_triangular

end AsymptoticClassicalDiscriminant
