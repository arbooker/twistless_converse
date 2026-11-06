module

public import AsymptoticClassicalNewCuspV1
public import AsymptoticFrickeNormalizerV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane Matrix ConjAct AsymptoticCongruenceLabels
open scoped ModularForm MatrixGroups Pointwise

theorem level_antitone {M N : ℕ} (h : M ∣ N) : level N ≤ level M := by
  apply Subgroup.map_mono
  intro A hA
  rw [gamma0_mem_dvd] at hA ⊢
  exact (show (M : ℤ) ∣ (N : ℤ) by exact_mod_cast h).trans hA

/-- The conjugating identity in honest GL matrices, before taking a
 projective quotient. -/
theorem fricke_reverse_intertwine (N : ℕ) (hN : 0 < N) (A : SL(2, ℤ))
    (c : ℤ) (hc : A 1 0 = (N : ℤ) * c) :
    (fricke N hN).map (Rat.castHom ℝ) *
      SpecialLinearGroup.mapGL ℝ (frickeConjugate N A c hc) =
    SpecialLinearGroup.mapGL ℝ A * (fricke N hN).map (Rat.castHom ℝ) := by
  apply Units.ext
  change ((fricke N hN).map (Rat.castHom ℝ)).val *
      (frickeConjugate N A c hc).val.map (fun z : ℤ => (z : ℝ)) =
    A.val.map (fun z : ℤ => (z : ℝ)) * ((fricke N hN).map (Rat.castHom ℝ)).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fricke, AsymptoticReconstructionBranch.branch, GeneralLinearGroup.map,
      GeneralLinearGroup.mkOfDetNeZero, frickeConjugate, Matrix.mul_apply,
      Fin.sum_univ_two, hc]
  all_goals ring

/-- Both lower-level trace targets are genuine overgroups of the level
 of the original cusp form. -/
theorem level_le_frickeOldLevel {N M : ℕ} (hN : 0 < N) (hM : M ∣ N) :
    level N ≤ frickeOldLevel N M hN := by
  rintro g ⟨A, hA, rfl⟩
  obtain ⟨c, hc⟩ := (gamma0_mem_dvd N A).mp hA
  have hb : SpecialLinearGroup.mapGL ℝ (frickeConjugate N A c hc) ∈ level M :=
    level_antitone hM ⟨frickeConjugate N A c hc, frickeConjugate_mem N A c hc, rfl⟩
  have he := fricke_reverse_intertwine N hN A c hc
  have he' : toConjAct ((fricke N hN).map (Rat.castHom ℝ)) •
      SpecialLinearGroup.mapGL ℝ (frickeConjugate N A c hc) =
      SpecialLinearGroup.mapGL ℝ A := by
    change (fricke N hN).map (Rat.castHom ℝ) *
      SpecialLinearGroup.mapGL ℝ (frickeConjugate N A c hc) *
      ((fricke N hN).map (Rat.castHom ℝ))⁻¹ = SpecialLinearGroup.mapGL ℝ A
    rw [he, mul_inv_cancel_right]
  rw [← he']
  exact Subgroup.smul_mem_pointwise_smul_iff.mpr hb

#print axioms level_antitone
#print axioms fricke_reverse_intertwine
#print axioms level_le_frickeOldLevel

end AsymptoticClassicalCusp
