module

public import AsymptoticClassicalOldIntersectionIndexV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane ConjAct Matrix AsymptoticCongruenceLabels
open scoped ModularForm Pointwise

/-- A fractional translation belongs to the dilated lower-level group. -/
theorem fractional_translation_mem_dilationLevel (M p : ℕ) (hp : 0 < p) :
    AsymptoticMobiusFold.translation (1 / (p : ℝ)) ∈ dilationLevel M p hp := by
  have he : dilationReal p hp * AsymptoticMobiusFold.translation (1 / (p : ℝ)) =
      SpecialLinearGroup.mapGL ℝ (upperSL 1) * dilationReal p hp := by
    apply Units.ext
    change (dilationReal p hp).val * (AsymptoticMobiusFold.translation (1 / (p : ℝ))).val =
      (upperSL 1).val.map (fun a : ℤ => (a : ℝ)) * (dilationReal p hp).val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dilationReal, dilationGL, AsymptoticMobiusFold.translation, upperSL,
        AsymptoticFreshCRT.upper, GeneralLinearGroup.map, GeneralLinearGroup.mkOfDetNeZero,
        Matrix.mul_apply, Fin.sum_univ_two, hp.ne']
  refine ⟨SpecialLinearGroup.mapGL ℝ (upperSL 1), ?_, ?_⟩
  · exact ⟨upperSL 1, by
      change upperSL 1 ∈ CongruenceSubgroup.Gamma0 M
      rw [gamma0_mem_dvd]
      simp [upperSL, AsymptoticFreshCRT.upper], rfl⟩
  · change (dilationReal p hp)⁻¹ * SpecialLinearGroup.mapGL ℝ (upperSL 1) *
      ((dilationReal p hp)⁻¹)⁻¹ = _
    rw [inv_inv, mul_assoc, ← he, inv_mul_cancel_left]

/-- This translation is not integral for a prime denominator. -/
theorem fractional_translation_not_mem_level (M p : ℕ) (hp : p.Prime) :
    AsymptoticMobiusFold.translation (1 / (p : ℝ)) ∉ level M := by
  rintro ⟨A, _, he⟩
  have he' := congrArg (fun g : GL (Fin 2) ℝ => g.val 0 1) he
  change (A 0 1 : ℝ) = 1 / (p : ℝ) at he'
  have hm : (p : ℝ) * (A 0 1 : ℝ) = 1 := by
    rw [he', mul_one_div_cancel (by exact_mod_cast hp.ne_zero)]
  have hm' : (p : ℤ) * A 0 1 = 1 := by exact_mod_cast hm
  have hd : (p : ℤ) ∣ 1 := ⟨A 0 1, hm'.symm⟩
  have hd' : p ∣ 1 := by exact_mod_cast hd
  exact hp.not_dvd_one hd'

/-- At a repeated prime whose intervening index is prime, the two honest
 classical old groups generate the two-step dilation group. -/
theorem repeated_old_join_eq (L p : ℕ) (hL : 0 < L) (hp : p.Prime)
    (hr : ((level (p * L)).relIndex (level L)).Prime) :
    level (p * L) ⊔ dilationLevel (p * L) p hp.pos = dilationLevel L p hp.pos := by
  apply AsymptoticPrimeIndexJoin.sup_eq_of_prime_relIndex
    (level (p * L)) (dilationLevel (p * L) p hp.pos) (dilationLevel L p hp.pos)
    (level_le_dilation_conjugate L p hp.pos)
    (dilationLevel_mono hp.pos (Nat.dvd_mul_left L p))
  · rwa [lower_dilationLevel_index L p hL hp.pos]
  · intro hh
    exact fractional_translation_not_mem_level (p * L) p hp
      (hh (fractional_translation_mem_dilationLevel (p * L) p hp.pos))

/-- The two old images at a repeated prime overlap in precisely one copy
 of the two-step lower-level cusp space. -/
theorem repeated_old_intersection_finrank (L p : ℕ) (hL : 0 < L) (hp : p.Prime)
    (hr : ((level (p * L)).relIndex (level L)).Prime) (k : ℤ) :
    Module.finrank ℂ ↥(LinearMap.range (restrict k
      (level_antitone (Nat.dvd_mul_left (p * L) p))) ⊓
      LinearMap.range (restrict k (level_le_dilation_conjugate (p * L) p hp.pos))) =
        Module.finrank ℂ (CuspForm (level L) k) := by
  let : NeZero L := ⟨hL.ne'⟩
  let : NeZero (p * L) := ⟨(Nat.mul_pos hp.pos hL).ne'⟩
  let : NeZero (p * (p * L)) := ⟨(Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)).ne'⟩
  have he := restrict_intersection_finrank
    (G := level (p * (p * L))) (H := level (p * L))
    (L := dilationLevel (p * L) p hp.pos) (J := dilationLevel L p hp.pos) k
    (level_antitone (Nat.dvd_mul_left (p * L) p))
    (level_le_dilation_conjugate (p * L) p hp.pos)
    ((level_antitone (Nat.dvd_mul_left (p * L) p)).trans
      (level_le_dilation_conjugate L p hp.pos)) (repeated_old_join_eq L p hL hp hr)
  exact he.trans (dilationLevel_finrank L p hp.pos k)

#print axioms fractional_translation_mem_dilationLevel
#print axioms fractional_translation_not_mem_level
#print axioms repeated_old_join_eq
#print axioms repeated_old_intersection_finrank

end AsymptoticClassicalCusp
