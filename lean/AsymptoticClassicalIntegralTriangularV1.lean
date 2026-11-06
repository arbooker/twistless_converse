module

public import AsymptoticClassicalDegeneracyV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalDiscriminant

open Matrix
open scoped MatrixGroups

/-- An integral matrix of positive determinant can be triangularized on
 the left by SL(2,Z), with both diagonal entries positive. -/
theorem integral_triangular (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : 0 < B.det) :
    ∃ (U : SL(2, ℤ)) (a b d : ℤ), 0 < a ∧ 0 < d ∧ B = U.val * !![a, b; 0, d] := by
  have hg : 0 < Int.gcd (B 0 0) (B 1 0) := by
    apply Nat.pos_of_ne_zero
    intro he
    have hz := Int.gcd_eq_zero_iff.mp he
    rw [Matrix.det_fin_two, hz.1, hz.2] at hB
    norm_num at hB
  obtain ⟨u, v, huv, hu, hv⟩ := Int.exists_gcd_one hg
  obtain ⟨U, hU0, hU1⟩ := (Int.isCoprime_iff_gcd_eq_one.mpr huv).exists_SL2_col 0
  let a : ℤ := Int.gcd (B 0 0) (B 1 0)
  let V : Matrix (Fin 2) (Fin 2) ℤ := !![U 1 1, -U 0 1; -U 1 0, U 0 0]
  let T : Matrix (Fin 2) (Fin 2) ℤ := V * B
  have hd := U.property
  rw [Matrix.det_fin_two] at hd
  have hu' : B 0 0 = u * a := hu
  have hv' : B 1 0 = v * a := hv
  have h00 : T 0 0 = a := by
    dsimp [T]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    change U 1 1 * B 0 0 + -(U 0 1) * B 1 0 = a
    rw [hu', hv']
    have hda := congrArg (fun x : ℤ => x * a) hd
    rw [hU0, hU1] at hda
    nlinarith [hda]
  have h10 : T 1 0 = 0 := by
    dsimp [T]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    change -(U 1 0) * B 0 0 + U 0 0 * B 1 0 = 0
    rw [hu', hv', hU0, hU1]
    ring
  have ha : 0 < a := by
    change 0 < ((Int.gcd (B 0 0) (B 1 0)) : ℤ)
    exact_mod_cast hg
  have hV : V.det = 1 := by
    rw [Matrix.det_fin_two]
    change U 1 1 * U 0 0 - (-U 0 1) * (-U 1 0) = 1
    nlinarith [hd]
  have hdet : T.det = B.det := by
    change (V * B).det = _
    rw [Matrix.det_mul, hV, one_mul]
  have hdpos : 0 < T 1 1 := by
    rw [Matrix.det_fin_two, h00, h10] at hdet
    nlinarith [hdet]
  refine ⟨U, a, T 0 1, T 1 1, ha, hdpos, ?_⟩
  have hUV : U.val * V = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [V, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals nlinarith [hd]
  have hprod : B = U.val * T := by
    change B = U.val * (V * B)
    rw [← Matrix.mul_assoc, hUV, Matrix.one_mul]
  rw [hprod]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h10]

#print axioms integral_triangular

end AsymptoticClassicalDiscriminant
