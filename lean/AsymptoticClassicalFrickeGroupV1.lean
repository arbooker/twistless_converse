module

public import AsymptoticClassicalOldLevelsV1
public import AsymptoticClassicalCosetBridgeV1
public import AsymptoticFrickeOldGroupV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane Matrix ConjAct AsymptoticCongruenceLabels AsymptoticFreshMatrices
open scoped ModularForm MatrixGroups Pointwise

def frickeReal (N : ℕ) (hN : 0 < N) : GL (Fin 2) ℝ :=
  (fricke N hN).map (Rat.castHom ℝ)

/-- The forward conjugating identity, in the honest matrix group. -/
theorem fricke_forward_intertwine (N : ℕ) (hN : 0 < N) (A : SL(2, ℤ))
    (c : ℤ) (hc : A 1 0 = (N : ℤ) * c) :
    frickeReal N hN * SpecialLinearGroup.mapGL ℝ A =
      SpecialLinearGroup.mapGL ℝ (frickeConjugate N A c hc) * frickeReal N hN := by
  apply Units.ext
  change (frickeReal N hN).val * A.val.map (fun z : ℤ => (z : ℝ)) =
    (frickeConjugate N A c hc).val.map (fun z : ℤ => (z : ℝ)) * (frickeReal N hN).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frickeReal, fricke, AsymptoticReconstructionBranch.branch, GeneralLinearGroup.map,
      GeneralLinearGroup.mkOfDetNeZero, frickeConjugate, Matrix.mul_apply,
      Fin.sum_univ_two, hc]
  all_goals ring

/-- Global Fricke also normalizes the literal GL congruence group. -/
theorem frickeOldLevel_self (N : ℕ) (hN : 0 < N) : frickeOldLevel N N hN = level N := by
  apply le_antisymm
  · rintro g ⟨a, ⟨A, hA, rfl⟩, rfl⟩
    obtain ⟨c, hc⟩ := (gamma0_mem_dvd N A).mp hA
    have he : toConjAct (frickeReal N hN) • SpecialLinearGroup.mapGL ℝ A =
        SpecialLinearGroup.mapGL ℝ (frickeConjugate N A c hc) := by
      change frickeReal N hN * SpecialLinearGroup.mapGL ℝ A * (frickeReal N hN)⁻¹ = _
      rw [fricke_forward_intertwine N hN A c hc, mul_inv_cancel_right]
    change toConjAct (frickeReal N hN) • SpecialLinearGroup.mapGL ℝ A ∈ level N
    rw [he]
    exact ⟨frickeConjugate N A c hc, frickeConjugate_mem N A c hc, rfl⟩
  · exact level_le_frickeOldLevel hN (dvd_refl N)

/-- Integral representatives for the Fricke-conjugated matrix group. -/
def frickeMatrixLabel (N : ℕ) (hN : 0 < N) : SL(2, ℤ) →* GL (Fin 2) ℝ :=
  (MulAut.conj (frickeReal N hN)).toMonoidHom.comp (SpecialLinearGroup.mapGL ℝ)

def frickeProjectiveLabel (N : ℕ) (hN : 0 < N) : SL(2, ℤ) →* AsymptoticRationalGroup.Group :=
  (MulAut.conj (frickeLabel N hN)).toMonoidHom.comp integralLabel

theorem frickeMatrixLabel_image (N M : ℕ) (hN : 0 < N) :
    (CongruenceSubgroup.Gamma0 M).map (frickeMatrixLabel N hN) = frickeOldLevel N M hN := by
  rw [frickeMatrixLabel, ← Subgroup.map_map]
  rfl

theorem frickeProjectiveLabel_image (N M : ℕ) (hN : 0 < N) :
    (CongruenceSubgroup.Gamma0 M).map (frickeProjectiveLabel N hN) =
      AsymptoticCongruenceStrip.frickeOldGroup N M hN := by
  rw [frickeProjectiveLabel, ← Subgroup.map_map]
  rfl

theorem frickeMatrixLabel_small (N : ℕ) (hN : 0 < N) :
    (CongruenceSubgroup.Gamma0 N).map (frickeMatrixLabel N hN) = level N :=
  (frickeMatrixLabel_image N N hN).trans (frickeOldLevel_self N hN)

theorem frickeProjectiveLabel_small (N : ℕ) (hN : 0 < N) :
    (CongruenceSubgroup.Gamma0 N).map (frickeProjectiveLabel N hN) =
      AsymptoticCongruenceStrip.gamma N := by
  rw [frickeProjectiveLabel, ← Subgroup.map_map]
  exact AsymptoticCongruenceStrip.gamma_map_fricke N hN

theorem frickeMatrixLabel_injective (N : ℕ) (hN : 0 < N) :
    Function.Injective (frickeMatrixLabel N hN) :=
  (MulAut.conj (frickeReal N hN)).injective.comp SpecialLinearGroup.mapGL_injective

theorem frickeProjectiveLabel_ker_le (N : ℕ) (hN : 0 < N) :
    (frickeProjectiveLabel N hN).ker ≤ CongruenceSubgroup.Gamma0 N := by
  intro A hA
  apply integralLabel_ker_le N
  apply (MulAut.conj (frickeLabel N hN)).injective
  exact hA.trans (map_one (MulAut.conj (frickeLabel N hN))).symm

#print axioms fricke_forward_intertwine
#print axioms frickeOldLevel_self
#print axioms frickeMatrixLabel_image
#print axioms frickeProjectiveLabel_image
#print axioms frickeMatrixLabel_small
#print axioms frickeProjectiveLabel_small
#print axioms frickeMatrixLabel_injective
#print axioms frickeProjectiveLabel_ker_le

end AsymptoticClassicalCusp
