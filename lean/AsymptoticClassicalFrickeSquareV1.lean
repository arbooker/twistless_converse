module

public import AsymptoticClassicalFrickeOperatorV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane Complex AsymptoticClassicalLSeries

theorem fricke_action_twice (N : ℕ) (hN : 0 < N) (z : ℍ) :
    frickeReal N hN • (frickeReal N hN • z) = z := by
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  apply UpperHalfPlane.ext
  rw [frickeReal_action, frickeReal_action]
  field_simp

theorem frickeOperator_square (N : ℕ) (hN : 0 < N) (k : ℤ)
    (f : CuspForm (level N) k) :
    frickeOperator N hN k (frickeOperator N hN k f) = (-1 : ℂ)^k • f := by
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hc : ((N : ℂ)^(-(k : ℂ)/2))^2 * (N : ℂ)^k = 1 := by
    rw [← Complex.cpow_intCast, pow_two, ← Complex.cpow_add _ _ hNC,
      ← Complex.cpow_add _ _ hNC]
    rw [show -(k : ℂ)/2 + -(k : ℂ)/2 + (k : ℂ) = 0 by ring, Complex.cpow_zero]
  apply CuspForm.ext
  intro z
  rw [frickeOperator_apply, frickeOperator_apply, fricke_action_twice, frickeReal_action]
  change _ = (-1 : ℂ)^k * f z
  have hz : (z : ℂ) ≠ 0 := ne_zero z
  have hpow : (z : ℂ)^(-k) * (z : ℂ)^k = 1 := by
    rw [← zpow_add₀ hz, neg_add_cancel, zpow_zero]
  have hn : ((-1 : ℂ)^k)⁻¹ = (-1 : ℂ)^k := by
    rw [← inv_zpow, inv_neg, inv_one]
  have hWpow : (-1 / ((N : ℂ) * (z : ℂ)))^(-k) =
      (-1 : ℂ)^k * (N : ℂ)^k * (z : ℂ)^k := by
    rw [zpow_neg, div_zpow, mul_zpow, inv_div, div_eq_mul_inv, hn]
    ring
  rw [hWpow]
  calc
    _ = (((N : ℂ)^(-(k : ℂ)/2))^2 * (N : ℂ)^k) *
        ((z : ℂ)^(-k) * (z : ℂ)^k) * (-1 : ℂ)^k * f z := by ring
    _ = _ := by rw [hc, hpow, one_mul, one_mul]

/-- At even weights the normalized global Fricke operator is an involution. -/
theorem frickeOperator_involutive (N : ℕ) (hN : 0 < N) (k : ℕ) (hk : Even k) :
    Function.Involutive (frickeOperator N hN (k : ℤ)) := by
  intro f
  rw [frickeOperator_square, zpow_natCast, hk.neg_one_pow, one_smul]

#print axioms fricke_action_twice
#print axioms frickeOperator_square
#print axioms frickeOperator_involutive

end AsymptoticClassicalCusp
