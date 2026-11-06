module

public import AsymptoticClassicalEigenFrickeV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalLSeries

open UpperHalfPlane Complex AsymptoticClassicalCusp
open scoped ModularForm

/-- Mathlib's GL slash normalization at the global Fricke matrix. -/
theorem slash_fricke (N : ℕ) (hN : 0 < N) (k : ℤ) (f : ℍ → ℂ) (z : ℍ) :
    (f ∣[k] frickeReal N hN) z = (N : ℂ)^(-1 : ℤ) * (z : ℂ)^(-k) *
      f (frickeReal N hN • z) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hd : denom (frickeReal N hN) z = (N : ℂ) * (z : ℂ) := by
    simp [denom, frickeReal, fricke, AsymptoticReconstructionBranch.branch,
      Matrix.GeneralLinearGroup.map, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  rw [ModularForm.slash_apply, hd]
  simp only [σ, frickeReal_det, hNR, ite_true, ContinuousAlgEquiv.refl_apply,
    abs_of_pos hNR, Complex.ofReal_natCast, mul_zpow]
  have hn : (N : ℂ)^(k-1) * (N : ℂ)^(-k) = (N : ℂ)^(-1 : ℤ) := by
    rw [← zpow_add₀ hNC]
    congr 1
    omega
  calc
    _ = ((N : ℂ)^(k-1) * (N : ℂ)^(-k)) * (z : ℂ)^(-k) *
      f (frickeReal N hN • z) := by ring
    _ = _ := by rw [hn]

/-- The pointwise Fricke definition is exactly the usual
`det^(1-k/2)` rescaling of the existing GL slash action. -/
theorem normalizedFricke_eq_slash (N : ℕ) (hN : 0 < N) (k : ℤ) (f : ℍ → ℂ) :
    normalizedFricke N hN k f =
      (N : ℂ)^(1-(k : ℂ)/2) • (f ∣[k] frickeReal N hN) := by
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  funext z
  rw [Pi.smul_apply, slash_fricke]
  change (N : ℂ)^(-(k : ℂ)/2) * (z : ℂ)^(-k) * f (frickeReal N hN • z) = _
  have hscale : (N : ℂ)^(1-(k : ℂ)/2) * (N : ℂ)^(-1 : ℤ) =
      (N : ℂ)^(-(k : ℂ)/2) := by
    rw [← Complex.cpow_intCast, ← Complex.cpow_add _ _ hNC]
    congr 1
    push_cast
    ring
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← mul_assoc, hscale]

/-- For even weights, a Fricke sign gives one of the two root numbers
allowed in the paper's continuation predicate. -/
theorem fricke_root_sign (k : ℕ) (hk : Even k) {eigenvalue : ℂ} (heigenvalue : eigenvalue = 1 ∨ eigenvalue = -1) :
    Complex.I^(k : ℤ) * eigenvalue = 1 ∨ Complex.I^(k : ℤ) * eigenvalue = -1 := by
  obtain ⟨m, rfl⟩ := hk
  have hi : Complex.I^((m+m : ℕ) : ℤ) = (-1 : ℂ)^m := by
    rw [zpow_natCast, ← two_mul, pow_mul, Complex.I_sq]
  rw [hi]
  rcases neg_one_pow_eq_or ℂ m with hm | hm <;>
    rcases heigenvalue with rfl | rfl <;> simp [hm]

#print axioms slash_fricke
#print axioms normalizedFricke_eq_slash
#print axioms fricke_root_sign

end AsymptoticClassicalLSeries
