module

public import AsymptoticClassicalLocalAtkinLowerV1
public import AsymptoticClassicalHeckeFormulaV1
public import AsymptoticClassicalDegeneracyRangeV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane Matrix AsymptoticAtkinLehner AsymptoticCongruenceLabels
open scoped ModularForm MatrixGroups

variable (M p : ℕ) (hp : 0 < p) (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)

theorem localAtkinReal_trace_dilation :
    localAtkinReal M p hp A B hAB =
      SpecialLinearGroup.mapGL ℝ (traceSL M p A B hAB 0) * dilationReal p hp := by
  apply Units.ext
  change (localAtkinReal M p hp A B hAB).val =
    (traceSL M p A B hAB 0).val.map (fun z : ℤ => (z : ℝ)) * (dilationReal p hp).val
  rw [localAtkinReal_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [traceSL, dilationReal, dilationGL, GeneralLinearGroup.map,
      GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

theorem localAtkin_restrict (k : ℤ) (f : CuspForm (level M) k) :
    localAtkinOperator M p hp A B hAB k (restrict k (level_antitone (dvd_mul_left M p)) f) =
      (p : ℂ) ^ (k - 1) • degeneracy M p hp k f := by
  apply DFunLike.coe_injective
  change (f : ℍ → ℂ) ∣[k] localAtkinReal M p hp A B hAB =
    (p : ℂ) ^ (k - 1) • (degeneracy M p hp k f : ℍ → ℂ)
  rw [scaled_degeneracy_coe, localAtkinReal_trace_dilation, SlashAction.slash_mul]
  have hi : (f : ℍ → ℂ) ∣[k] SpecialLinearGroup.mapGL ℝ (traceSL M p A B hAB 0) = f :=
    f.slash_action_eq' _ ⟨_, traceSL_mem M p A B hAB 0, rfl⟩
  rw [hi]

theorem localAtkin_degeneracy (k : ℤ) (f : CuspForm (level M) k) :
    localAtkinOperator M p hp A B hAB k (degeneracy M p hp k f) =
      (((p : ℂ) ^ (k - 1))⁻¹ * (p : ℂ) ^ (k - 2)) •
        restrict k (level_antitone (dvd_mul_left M p)) f := by
  have ha : (p : ℂ) ^ (k - 1) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hp.ne')
  have he := localAtkin_restrict M p hp A B hAB k f
  have hdeg : degeneracy M p hp k f = ((p : ℂ) ^ (k - 1))⁻¹ •
      localAtkinOperator M p hp A B hAB k (restrict k (level_antitone (dvd_mul_left M p)) f) := by
    rw [he, smul_smul, inv_mul_cancel₀ ha, one_smul]
  rw [hdeg, map_smul, localAtkinOperator_square, smul_smul]

/-- The ordinary lower-level image is preserved by the local operator at a distinct prime. -/
theorem localAtkin_slash_lower (L q : ℕ)
    (hAB : (p : ℤ) * A + ((q * L : ℕ) : ℤ) * B = 1) (k : ℤ)
    (f : CuspForm (level (p * L)) k) :
    (f : ℍ → ℂ) ∣[k] localAtkinReal (q * L) p hp A B hAB =
      (localAtkinOperator L p hp A ((q : ℤ) * B)
        (localAtkin_lower_bezout L q p A B hAB) k f : ℍ → ℂ) := by
  rw [localAtkinReal_lower, SlashAction.slash_mul]
  have hi : (f : ℍ → ℂ) ∣[k] SpecialLinearGroup.mapGL ℝ (localAtkinLowerSL L q p A B hAB) = f :=
    f.slash_action_eq' _ ⟨_, localAtkinLowerSL_mem L q p A B hAB, rfl⟩
  rw [hi]
  rfl

/-- The second lower-level image is preserved by the same local operator. -/
theorem localAtkin_slash_degeneracy_lower (L q : ℕ) (hq : 0 < q)
    (hAB : (p : ℤ) * A + ((q * L : ℕ) : ℤ) * B = 1) (k : ℤ)
    (f : CuspForm (level (p * L)) k) :
    (degeneracy (p * L) q hq k f : ℍ → ℂ) ∣[k] localAtkinReal (q * L) p hp A B hAB =
      (degeneracy (p * L) q hq k
        (localAtkinOperator L p hp A ((q : ℤ) * B)
          (localAtkin_lower_bezout L q p A B hAB) k f) : ℍ → ℂ) := by
  change ((q : ℂ) ^ (1 - k) • ((f : ℍ → ℂ) ∣[k] dilationReal q hq)) ∣[k]
    localAtkinReal (q * L) p hp A B hAB =
    (q : ℂ) ^ (1 - k) • (((f : ℍ → ℂ) ∣[k]
      localAtkinReal L p hp A ((q : ℤ) * B) (localAtkin_lower_bezout L q p A B hAB)) ∣[k]
        dilationReal q hq)
  rw [ModularForm.smul_slash, ← SlashAction.slash_mul, localAtkinReal_lower_dilation,
    SlashAction.slash_mul]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  simp only [σ, localAtkinReal_det, hpR, ite_true, ContinuousAlgEquiv.refl_apply]

/-- A range criterion that avoids transporting cusp forms across reassociated levels. -/
theorem mem_frickeOld_range_iff (N M q : ℕ) (hN : 0 < N) (hM : 0 < M) (hq : 0 < q)
    (he : N = q * M) (hMN : M ∣ N) (k : ℤ) (f : CuspForm (level N) k) :
    f ∈ LinearMap.range (restrict k (level_le_frickeOldLevel hN hMN)) ↔
      ∃ g : CuspForm (level M) k, (f : ℍ → ℂ) = (degeneracy M q hq k g : ℍ → ℂ) := by
  subst N
  rw [frickeOld_range_eq_degeneracy M q hM hq k]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, DFunLike.coe_injective hg.symm⟩

#print axioms localAtkinReal_trace_dilation
#print axioms localAtkin_restrict
#print axioms localAtkin_degeneracy
#print axioms localAtkin_slash_lower
#print axioms localAtkin_slash_degeneracy_lower
#print axioms mem_frickeOld_range_iff

end AsymptoticClassicalCusp
