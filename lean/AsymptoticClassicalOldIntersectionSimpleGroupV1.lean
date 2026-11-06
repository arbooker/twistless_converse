module

public import AsymptoticClassicalOldIntersectionLowerV1
public import AsymptoticClassicalOldIntersectionRepeatedV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane Matrix ConjAct AsymptoticCongruenceLabels AsymptoticRamifiedCosets
open scoped ModularForm Pointwise

/-- Integral multiples of the fractional period belong to the second old group. -/
theorem fractional_translation_int_mem_dilationLevel (M p : ℕ) (hp : 0 < p) (a : ℤ) :
    AsymptoticMobiusFold.translation ((a : ℝ) / p) ∈ dilationLevel M p hp := by
  have he : dilationReal p hp * AsymptoticMobiusFold.translation ((a : ℝ) / p) =
      SpecialLinearGroup.mapGL ℝ (upperSL a) * dilationReal p hp := by
    apply Units.ext
    change (dilationReal p hp).val * (AsymptoticMobiusFold.translation ((a : ℝ) / p)).val =
      (upperSL a).val.map (fun b : ℤ => (b : ℝ)) * (dilationReal p hp).val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dilationReal, dilationGL, AsymptoticMobiusFold.translation, upperSL,
        AsymptoticFreshCRT.upper, GeneralLinearGroup.map, GeneralLinearGroup.mkOfDetNeZero,
        Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  refine ⟨SpecialLinearGroup.mapGL ℝ (upperSL a), ?_, ?_⟩
  · exact ⟨upperSL a, by
      change upperSL a ∈ CongruenceSubgroup.Gamma0 M
      rw [gamma0_mem_dvd]
      simp [upperSL, AsymptoticFreshCRT.upper], rfl⟩
  · change (dilationReal p hp)⁻¹ * SpecialLinearGroup.mapGL ℝ (upperSL a) *
      ((dilationReal p hp)⁻¹)⁻¹ = _
    rw [inv_inv, mul_assoc, ← he, inv_mul_cancel_left]

/-- A lower triangular element contracting lower unipotents by p⁻². -/
def contractingLower (M p : ℕ) (hp : 0 < p) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero !![(p : ℝ), 0; (M : ℝ), 1 / (p : ℝ)] (by
    simp [Matrix.det_fin_two, hp.ne'])

theorem contractingLower_factor (M p : ℕ) (hp : 0 < p) (hc : p.Coprime M) :
    SpecialLinearGroup.mapGL ℝ (exceptional M p hc) *
        AsymptoticMobiusFold.translation ((Nat.gcdB p M : ℝ) / p) = contractingLower M p hp := by
  have hbez : (p : ℝ) * (Nat.gcdA p M : ℝ) + (M : ℝ) * (Nat.gcdB p M : ℝ) = 1 := by
    have hh := Nat.gcd_eq_gcd_ab p M
    rw [hc.gcd_eq_one] at hh
    exact_mod_cast hh.symm
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  apply Units.ext
  change (exceptional M p hc).val.map (fun a : ℤ => (a : ℝ)) *
    (AsymptoticMobiusFold.translation ((Nat.gcdB p M : ℝ) / p)).val = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exceptional, AsymptoticMobiusFold.translation, contractingLower,
      GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp
  all_goals nlinarith [hbez]

theorem contractingLower_mem_join (M p : ℕ) (hp : 0 < p) (hc : p.Coprime M) :
    contractingLower M p hp ∈ level M ⊔ dilationLevel M p hp := by
  rw [← contractingLower_factor M p hp hc]
  apply Subgroup.mul_mem
  · exact (show level M ≤ level M ⊔ dilationLevel M p hp from le_sup_left)
      ⟨exceptional M p hc, exceptional_mem M p hc, rfl⟩
  · exact (show dilationLevel M p hp ≤ level M ⊔ dilationLevel M p hp from le_sup_right)
      (fractional_translation_int_mem_dilationLevel M p hp (Nat.gcdB p M))

/-- Conjugation produces the smaller lower period, with no limiting group argument. -/
theorem contractingLower_conjugate (M p : ℕ) (hp : 0 < p) (r : ℝ) :
    contractingLower M p hp * lowerTranslation r * (contractingLower M p hp)⁻¹ =
      lowerTranslation (r * (1 / (p : ℝ)^2)) := by
  have he : contractingLower M p hp * lowerTranslation r =
      lowerTranslation (r * (1 / (p : ℝ)^2)) * contractingLower M p hp := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [contractingLower, lowerTranslation, GeneralLinearGroup.mkOfDetNeZero,
        Matrix.mul_apply, Fin.sum_univ_two]
    all_goals field_simp
    all_goals ring
  rw [he, mul_inv_cancel_right]

/-- The generated old group contains nonzero lower periods arbitrarily near zero. -/
theorem small_lower_mem_join (M p : ℕ) (hp : 0 < p) (hc : p.Coprime M) (n : ℕ) :
    lowerTranslation ((M : ℝ) * (1 / (p : ℝ)^2)^n) ∈ level M ⊔ dilationLevel M p hp := by
  induction n with
  | zero =>
    have he : lowerTranslation (M : ℝ) = SpecialLinearGroup.mapGL ℝ (lowerSL M 1) := by
      apply Units.ext
      change (lowerTranslation (M : ℝ)).val = (lowerSL M 1).val.map (fun a : ℤ => (a : ℝ))
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [lowerTranslation, lowerSL, AsymptoticFreshCRT.lower, GeneralLinearGroup.mkOfDetNeZero]
    simp only [pow_zero, mul_one, he]
    exact (show level M ≤ level M ⊔ dilationLevel M p hp from le_sup_left)
      ⟨lowerSL M 1, AsymptoticCongruenceLabels.lowerSL_mem M 1, rfl⟩
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ← contractingLower_conjugate M p hp]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (contractingLower_mem_join M p hp hc) ih)
      (Subgroup.inv_mem _ (contractingLower_mem_join M p hp hc))

#print axioms fractional_translation_int_mem_dilationLevel
#print axioms contractingLower_factor
#print axioms contractingLower_mem_join
#print axioms contractingLower_conjugate
#print axioms small_lower_mem_join

end AsymptoticClassicalCusp
