module

public import AsymptoticClassicalBadHeckeGroupV1
public import AsymptoticClassicalHeckeCosetsV1
public import AsymptoticAtkinLehnerSquareV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane Matrix ConjAct AsymptoticCongruenceLabels AsymptoticAtkinLehner
open scoped ModularForm MatrixGroups Pointwise

variable (M p : ℕ) (hp : 0 < p) (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)

/-- The literal determinant-p local Atkin--Lehner matrix. -/
def localAtkinReal : GL (Fin 2) ℝ :=
  upperDilationReal p hp * SpecialLinearGroup.mapGL ℝ (heckeSL M p A B hAB)

theorem localAtkinReal_val : (localAtkinReal M p hp A B hAB).val =
    !![(p : ℝ), (B : ℝ); -(p : ℝ) * M, (p : ℝ) * A] := by
  change (upperDilationReal p hp).val * (heckeSL M p A B hAB).val.map (fun z : ℤ => (z : ℝ)) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperDilationReal, upperDilationGL, heckeSL, GeneralLinearGroup.map,
      GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]

theorem localAtkinReal_det : (localAtkinReal M p hp A B hAB).det.val = (p : ℝ) := by
  simp only [localAtkinReal, map_mul, Units.val_mul]
  have hu : (SpecialLinearGroup.mapGL ℝ (heckeSL M p A B hAB)).det.val = 1 := by simp
  rw [hu, mul_one, upperDilationReal_det]

/-- The already constructed integral conjugate is also the literal GL conjugate. -/
theorem localAtkinReal_intertwine (g : SL(2, ℤ)) (c : ℤ)
    (hc : g 1 0 = (p : ℤ) * (M : ℤ) * c) :
    localAtkinReal M p hp A B hAB * SpecialLinearGroup.mapGL ℝ g =
      SpecialLinearGroup.mapGL ℝ (localConjugate M p A B hAB g c hc) *
        localAtkinReal M p hp A B hAB := by
  have hab : (p : ℝ) * A + (M : ℝ) * B = 1 := by exact_mod_cast hAB
  have hm : (localConjugate M p A B hAB g c hc).val.map (fun z : ℤ => (z : ℝ)) *
      (localAtkinReal M p hp A B hAB).val =
      ((p : ℝ) * A + (M : ℝ) * B) •
        ((localAtkinReal M p hp A B hAB).val * g.val.map (fun z : ℤ => (z : ℝ))) := by
    rw [localAtkinReal_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [localConjugate, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, hc]
    all_goals ring
  rw [hab, one_smul] at hm
  exact Units.ext hm.symm

theorem localAtkinReal_conj_mem {g : GL (Fin 2) ℝ} (hg : g ∈ level (p * M)) :
    localAtkinReal M p hp A B hAB * g * (localAtkinReal M p hp A B hAB)⁻¹ ∈ level (p * M) := by
  obtain ⟨a, ha, rfl⟩ := hg
  obtain ⟨c, hc⟩ := (gamma0_mem_dvd (p * M) a).mp ha
  have hc' : a 1 0 = (p : ℤ) * (M : ℤ) * c := by simpa only [Nat.cast_mul] using hc
  rw [localAtkinReal_intertwine M p hp A B hAB a c hc', mul_inv_cancel_right]
  exact ⟨_, localConjugate_mem M p A B hAB a c hc', rfl⟩

/-- Squaring gives p times an integral matrix at the original level. -/
theorem localAtkinReal_square :
    localAtkinReal M p hp A B hAB * localAtkinReal M p hp A B hAB =
      SpecialLinearGroup.mapGL ℝ (localSquare M p A B hAB) *
        GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p : ℝ) (by exact_mod_cast hp.ne')) := by
  apply Units.ext
  change (localAtkinReal M p hp A B hAB).val * (localAtkinReal M p hp A B hAB).val =
    (localSquare M p A B hAB).val.map (fun z : ℤ => (z : ℝ)) *
      Matrix.diagonal (fun _ : Fin 2 => (p : ℝ))
  rw [localAtkinReal_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [localSquare, Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

theorem localAtkinReal_inv_conj_mem {g : GL (Fin 2) ℝ} (hg : g ∈ level (p * M)) :
    (localAtkinReal M p hp A B hAB)⁻¹ * g * localAtkinReal M p hp A B hAB ∈ level (p * M) := by
  let V := localAtkinReal M p hp A B hAB
  let s := SpecialLinearGroup.mapGL ℝ (localSquare M p A B hAB)
  let u := Units.mk0 (p : ℝ) (show (p : ℝ) ≠ 0 by exact_mod_cast hp.ne')
  have hs : s ∈ level (p * M) := ⟨_, localSquare_mem M p A B hAB, rfl⟩
  have hh := (level (p * M)).mul_mem
    ((level (p * M)).mul_mem ((level (p * M)).inv_mem hs)
      (localAtkinReal_conj_mem M p hp A B hAB hg)) hs
  have hsquare : V * V = s * GeneralLinearGroup.scalar (Fin 2) u := localAtkinReal_square M p hp A B hAB
  have he : s⁻¹ * (V * g * V⁻¹) * s = V⁻¹ * g * V := by
    have hs' : s = V * V * (GeneralLinearGroup.scalar (Fin 2) u)⁻¹ := by rw [hsquare, mul_inv_cancel_right]
    rw [hs']
    calc
      _ = GeneralLinearGroup.scalar (Fin 2) u * (V⁻¹ * g * V) *
          (GeneralLinearGroup.scalar (Fin 2) u)⁻¹ := by group
      _ = _ := by rw [GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]
  change s⁻¹ * (V * g * V⁻¹) * s ∈ level (p * M) at hh
  rwa [he] at hh

theorem localAtkinReal_normalizes :
    toConjAct (localAtkinReal M p hp A B hAB)⁻¹ • level (p * M) = level (p * M) := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact localAtkinReal_inv_conj_mem M p hp A B hAB hg
  · intro g hg
    refine ⟨_, localAtkinReal_conj_mem M p hp A B hAB hg, ?_⟩
    change (localAtkinReal M p hp A B hAB)⁻¹ *
      (localAtkinReal M p hp A B hAB * g * (localAtkinReal M p hp A B hAB)⁻¹) *
      ((localAtkinReal M p hp A B hAB)⁻¹)⁻¹ = g
    group

#print axioms localAtkinReal_val
#print axioms localAtkinReal_det
#print axioms localAtkinReal_intertwine
#print axioms localAtkinReal_conj_mem
#print axioms localAtkinReal_square
#print axioms localAtkinReal_inv_conj_mem
#print axioms localAtkinReal_normalizes
end AsymptoticClassicalCusp
