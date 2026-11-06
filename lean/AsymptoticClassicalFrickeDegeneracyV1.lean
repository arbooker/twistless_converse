module

public import AsymptoticClassicalFrickeSquareV1
public import AsymptoticClassicalDegeneracyV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane Complex AsymptoticClassicalLSeries
open scoped ModularForm

theorem dilationReal_action_coe (p : ℕ) (hp : 0 < p) (z : ℍ) :
    ((dilationReal p hp • z : ℍ) : ℂ) = (p : ℂ) * z := by
  rw [coe_smul_of_det_pos (by rw [dilationReal_det]; exact_mod_cast hp), dilationReal_denom]
  simp [num, dilationReal, AsymptoticCongruenceLabels.dilationGL,
    Matrix.GeneralLinearGroup.map, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem fricke_dilation_action (N p : ℕ) (hN : 0 < N) (hp : 0 < p) (z : ℍ) :
    frickeReal N hN • (dilationReal p hp • z) = frickeReal (p*N) (Nat.mul_pos hp hN) • z := by
  apply UpperHalfPlane.ext
  rw [frickeReal_action, frickeReal_action, dilationReal_action_coe, Nat.cast_mul]
  congr 1
  ring

theorem dilation_fricke_action (N p : ℕ) (hN : 0 < N) (hp : 0 < p) (z : ℍ) :
    dilationReal p hp • (frickeReal (p*N) (Nat.mul_pos hp hN) • z) = frickeReal N hN • z := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  apply UpperHalfPlane.ext
  rw [dilationReal_action_coe, frickeReal_action, frickeReal_action, Nat.cast_mul]
  field_simp

/-- Global Fricke exchanges the two level-raising embeddings, with its exact
half-weight normalization. -/
theorem fricke_restrict_degeneracy (N p : ℕ) (hN : 0 < N) (hp : 0 < p) (k : ℤ)
    (f : CuspForm (level N) k) :
    frickeOperator (p*N) (Nat.mul_pos hp hN) k
      (restrict k (level_antitone (dvd_mul_left N p)) f) =
      (p : ℂ)^((k : ℂ)/2) • degeneracy N p hp k (frickeOperator N hN k f) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hprod : ((p*N : ℕ) : ℂ)^(-(k : ℂ)/2) =
      (p : ℂ)^(-(k : ℂ)/2) * (N : ℂ)^(-(k : ℂ)/2) := by
    rw [Nat.cast_mul]
    exact Complex.mul_cpow_ofReal_nonneg (by positivity : 0 ≤ (p : ℝ)) (by positivity) _
  have hpow : (p : ℂ)^((k : ℂ)/2) * (p : ℂ)^(-k) = (p : ℂ)^(-(k : ℂ)/2) := by
    rw [← Complex.cpow_intCast, ← Complex.cpow_add _ _ hpC]
    congr 1
    push_cast
    ring
  apply CuspForm.ext
  intro z
  rw [frickeOperator_apply]
  change _ = (p : ℂ)^((k : ℂ)/2) * degeneracy N p hp k (frickeOperator N hN k f) z
  rw [degeneracy_apply, frickeOperator_apply, fricke_dilation_action,
    dilationReal_action_coe, mul_zpow, hprod]
  change _ * _ * f _ = _
  calc
    _ = ((p : ℂ)^((k : ℂ)/2) * (p : ℂ)^(-k)) *
      (N : ℂ)^(-(k : ℂ)/2) * (z : ℂ)^(-k) * f _ := by rw [hpow]
    _ = _ := by ring

theorem fricke_degeneracy_restrict (N p : ℕ) (hN : 0 < N) (hp : 0 < p) (k : ℤ)
    (f : CuspForm (level N) k) :
    frickeOperator (p*N) (Nat.mul_pos hp hN) k (degeneracy N p hp k f) =
      (p : ℂ)^(-(k : ℂ)/2) •
        restrict k (level_antitone (dvd_mul_left N p)) (frickeOperator N hN k f) := by
  have hprod : ((p*N : ℕ) : ℂ)^(-(k : ℂ)/2) =
      (p : ℂ)^(-(k : ℂ)/2) * (N : ℂ)^(-(k : ℂ)/2) := by
    rw [Nat.cast_mul]
    exact Complex.mul_cpow_ofReal_nonneg (by positivity : 0 ≤ (p : ℝ)) (by positivity) _
  apply CuspForm.ext
  intro z
  rw [frickeOperator_apply, degeneracy_apply, dilation_fricke_action N p hN hp, hprod]
  change _ = (p : ℂ)^(-(k : ℂ)/2) * frickeOperator N hN k f z
  rw [frickeOperator_apply]
  ring

#print axioms fricke_restrict_degeneracy
#print axioms fricke_degeneracy_restrict

end AsymptoticClassicalCusp
