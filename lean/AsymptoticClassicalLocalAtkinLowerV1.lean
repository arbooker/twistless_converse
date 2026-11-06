module

public import AsymptoticClassicalLocalAtkinOperatorV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane Matrix AsymptoticAtkinLehner AsymptoticCongruenceLabels
open scoped ModularForm MatrixGroups

variable (L q p : ℕ) (hp : 0 < p) (A B : ℤ)
variable (hAB : (p : ℤ) * A + ((q * L : ℕ) : ℤ) * B = 1)

include hAB in
theorem localAtkin_lower_bezout : (p : ℤ) * A + (L : ℤ) * ((q : ℤ) * B) = 1 := by
  have hh : (p : ℤ) * A + (q : ℤ) * L * B = 1 := by simpa only [Nat.cast_mul] using hAB
  linear_combination hh

/-- The integral change of representative when lowering a distinct prime. -/
def localAtkinLowerSL : SL(2, ℤ) :=
  ⟨!![(p : ℤ) * A + L * B, (1 - q) * B;
      (p : ℤ) * A * (L - q * L), (q : ℤ) ^ 2 * L * B + p * A], by
    rw [Matrix.det_fin_two]
    change ((p : ℤ) * A + L * B) * ((q : ℤ) ^ 2 * L * B + p * A) -
      ((1 - q) * B) * ((p : ℤ) * A * (L - q * L)) = 1
    have hh : (p : ℤ) * A + (q : ℤ) * L * B = 1 := by simpa only [Nat.cast_mul] using hAB
    linear_combination ((p : ℤ) * A + (q : ℤ) * L * B + 1) * hh⟩

theorem localAtkinLowerSL_mem :
    localAtkinLowerSL L q p A B hAB ∈ CongruenceSubgroup.Gamma0 (p * L) := by
  rw [gamma0_mem_dvd]
  refine ⟨A * (1 - q), ?_⟩
  change (p : ℤ) * A * (L - q * L) = ((p * L : ℕ) : ℤ) * (A * (1 - q))
  push_cast
  ring

/-- The raw local operator commutes with lowering q by ordinary inclusion. -/
theorem localAtkinReal_lower :
    localAtkinReal (q * L) p hp A B hAB =
      SpecialLinearGroup.mapGL ℝ (localAtkinLowerSL L q p A B hAB) *
        localAtkinReal L p hp A ((q : ℤ) * B) (localAtkin_lower_bezout L q p A B hAB) := by
  have hab : (p : ℝ) * A + (q : ℝ) * L * B = 1 := by exact_mod_cast hAB
  have hh : (localAtkinLowerSL L q p A B hAB).val.map (fun z : ℤ => (z : ℝ)) *
      (localAtkinReal L p hp A ((q : ℤ) * B) (localAtkin_lower_bezout L q p A B hAB)).val =
      ((p : ℝ) * A + (q : ℝ) * L * B) • (localAtkinReal (q * L) p hp A B hAB).val := by
    rw [localAtkinReal_val, localAtkinReal_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [localAtkinLowerSL, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals ring
  rw [hab, one_smul] at hh
  exact Units.ext hh.symm

/-- The raw local operator commutes with lowering q by the dilation direction. -/
theorem localAtkinReal_lower_dilation (hq : 0 < q) :
    dilationReal q hq * localAtkinReal (q * L) p hp A B hAB =
      localAtkinReal L p hp A ((q : ℤ) * B) (localAtkin_lower_bezout L q p A B hAB) *
        dilationReal q hq := by
  apply Units.ext
  change (dilationReal q hq).val * (localAtkinReal (q * L) p hp A B hAB).val =
    (localAtkinReal L p hp A ((q : ℤ) * B) (localAtkin_lower_bezout L q p A B hAB)).val *
      (dilationReal q hq).val
  rw [localAtkinReal_val, localAtkinReal_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dilationReal, dilationGL, GeneralLinearGroup.map, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

#print axioms localAtkin_lower_bezout
#print axioms localAtkinLowerSL_mem
#print axioms localAtkinReal_lower
#print axioms localAtkinReal_lower_dilation

end AsymptoticClassicalCusp
