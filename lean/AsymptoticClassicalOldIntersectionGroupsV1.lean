module

public import AsymptoticClassicalOldIntersectionV1
public import AsymptoticClassicalDegeneracyV1
public import AsymptoticRepeatedJoinIndexV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane ConjAct Matrix
open scoped ModularForm Pointwise

/-- The honest matrix group underlying the second degeneracy map. -/
def dilationLevel (M p : ℕ) (hp : 0 < p) : Subgroup (GL (Fin 2) ℝ) :=
  toConjAct (dilationReal p hp)⁻¹ • level M

instance dilationLevel_det (M p : ℕ) (hp : 0 < p) :
    (dilationLevel M p hp).HasDetOne := inferInstanceAs
      (toConjAct (dilationReal p hp)⁻¹ • level M).HasDetOne

instance dilationLevel_arithmetic (M p : ℕ) (hp : 0 < p) [NeZero M] :
    (dilationLevel M p hp).IsArithmetic := by
  change (toConjAct (dilationReal p hp)⁻¹ • level M).IsArithmetic
  have he : (dilationReal p hp)⁻¹ =
      GeneralLinearGroup.map (Rat.castHom ℝ) (AsymptoticCongruenceLabels.dilationGL p hp)⁻¹ :=
    (map_inv (GeneralLinearGroup.map (Rat.castHom ℝ)) _).symm
  rw [he]
  exact Subgroup.IsArithmetic.conj (level M) _

theorem dilationLevel_finrank (M p : ℕ) (hp : 0 < p) (k : ℤ) :
    Module.finrank ℂ (CuspForm (dilationLevel M p hp) k) =
      Module.finrank ℂ (CuspForm (level M) k) :=
  (translateEquiv (level M) k (dilationReal p hp)
    (by rw [dilationReal_det]; exact_mod_cast hp)).finrank_eq.symm

theorem dilationLevel_mono {M L p : ℕ} (hp : 0 < p) (hLM : L ∣ M) :
    dilationLevel M p hp ≤ dilationLevel L p hp := by
  rintro g ⟨a, ha, rfl⟩
  exact ⟨a, level_antitone hLM ha, rfl⟩

theorem scalar_conjugate_eq (u : ℝˣ) (a g : GL (Fin 2) ℝ) :
    (GeneralLinearGroup.scalar (Fin 2) u * a) * g *
      (GeneralLinearGroup.scalar (Fin 2) u * a)⁻¹ = a * g * a⁻¹ := by
  rw [_root_.mul_inv_rev]
  have hcomm := GeneralLinearGroup.scalar_commute u (a * g * a⁻¹)
  calc
    _ = GeneralLinearGroup.scalar (Fin 2) u * (a * g * a⁻¹) *
      (GeneralLinearGroup.scalar (Fin 2) u)⁻¹ := by group
    _ = _ := by rw [hcomm, mul_inv_cancel_right]

/-- The Fricke and dilation conjugations differ by a scalar matrix. -/
theorem dilation_fricke_factor (M p : ℕ) (hM : 0 < M) (hp : 0 < p) :
    dilationReal p hp * frickeReal (p * M) (Nat.mul_pos hp hM) =
      GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p : ℝ) (by exact_mod_cast hp.ne')) *
        frickeReal M hM := by
  apply Units.ext
  change (dilationReal p hp).val * (frickeReal (p * M) (Nat.mul_pos hp hM)).val =
    Matrix.diagonal (fun _ : Fin 2 => (p : ℝ)) * (frickeReal M hM).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dilationReal, AsymptoticCongruenceLabels.dilationGL, frickeReal, fricke,
      AsymptoticReconstructionBranch.branch, GeneralLinearGroup.map,
      GeneralLinearGroup.mkOfDetNeZero,
      Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_two]

/-- The actual Fricke old group is the usual dilation-conjugated group. -/
theorem frickeOldLevel_eq_dilationLevel (M p : ℕ) (hM : 0 < M) (hp : 0 < p) :
    frickeOldLevel (p * M) M (Nat.mul_pos hp hM) = dilationLevel M p hp := by
  have he (g : GL (Fin 2) ℝ) :
      toConjAct (frickeReal (p * M) (Nat.mul_pos hp hM)) • g =
        toConjAct (dilationReal p hp)⁻¹ • (toConjAct (frickeReal M hM) • g) := by
    have hf := dilation_fricke_factor M p hM hp
    have hf' : frickeReal (p * M) (Nat.mul_pos hp hM) =
        (dilationReal p hp)⁻¹ *
          (GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p : ℝ) (by exact_mod_cast hp.ne')) *
            frickeReal M hM) := by rw [← hf, inv_mul_cancel_left]
    rw [hf', toConjAct_mul, mul_smul]
    congr 1
    exact scalar_conjugate_eq _ _ _
  change toConjAct (frickeReal (p * M) (Nat.mul_pos hp hM)) • level M = _
  have hgroup : toConjAct (frickeReal (p * M) (Nat.mul_pos hp hM)) • level M =
      toConjAct (dilationReal p hp)⁻¹ • (toConjAct (frickeReal M hM) • level M) := by
    ext g
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨_, ⟨a, ha, rfl⟩, (he a).symm⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, he a⟩
  rw [hgroup]
  change toConjAct (dilationReal p hp)⁻¹ • frickeOldLevel M M hM = _
  rw [frickeOldLevel_self]
  rfl

#print axioms dilationLevel_finrank
#print axioms dilationLevel_mono
#print axioms scalar_conjugate_eq
#print axioms dilation_fricke_factor
#print axioms frickeOldLevel_eq_dilationLevel

end AsymptoticClassicalCusp
