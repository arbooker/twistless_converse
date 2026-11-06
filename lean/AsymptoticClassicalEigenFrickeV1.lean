module

public import AsymptoticClassicalLSeriesFrickeV1
public import AsymptoticClassicalOldDimensionV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalLSeries

open UpperHalfPlane Complex AsymptoticClassicalCusp

/-- The classical determinant-half-weight normalization of global
Fricke, written as its literal holomorphic formula. -/
def normalizedFricke (N : ℕ) (hN : 0 < N) (k : ℤ) (f : ℍ → ℂ) (z : ℍ) : ℂ :=
  (N : ℂ)^(-(k : ℂ)/2) * (z : ℂ)^(-k) * f (frickeReal N hN • z)

theorem frickeReal_action (N : ℕ) (hN : 0 < N) (z : ℍ) :
    ((frickeReal N hN • z : ℍ) : ℂ) = -1 / ((N : ℂ) * (z : ℂ)) := by
  rw [coe_smul_of_det_pos (by rw [frickeReal_det]; exact_mod_cast hN)]
  simp [num, denom, frickeReal, fricke, AsymptoticReconstructionBranch.branch,
    Matrix.GeneralLinearGroup.map, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem frickeReal_axis (N : ℕ) (hN : 0 < N) (t : ℝ) (ht : 0 < t) :
    frickeReal N hN • ofComplex (Complex.I*t) =
      ofComplex (Complex.I * ((N : ℝ)*t)⁻¹) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  apply UpperHalfPlane.ext
  rw [frickeReal_action, ofComplex_apply_of_im_pos (by simpa using ht),
    ofComplex_apply_of_im_pos (by simpa using inv_pos.mpr (mul_pos hNreal ht))]
  push_cast
  have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  simp [Complex.I_sq]

/-- A scalar normalized Fricke eigenrelation gives the corresponding
root number `i^k * η` on the positive imaginary axis. -/
theorem axial_fricke_of_eigen (N : ℕ) (hN : 0 < N) (k : ℤ)
    (f : ℍ → ℂ) (η : ℂ) (heigen : normalizedFricke N hN k f = η • f)
    (t : ℝ) (ht : 0 < t) :
    f (ofComplex (Complex.I * ((N : ℝ)*t)⁻¹)) =
      (Complex.I^k * η) * (N : ℂ)^((k : ℂ)/2) * (t : ℂ)^(k : ℂ) *
        f (ofComplex (Complex.I*t)) := by
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hzC : Complex.I * (t : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero htC
  have he := congrFun heigen (ofComplex (Complex.I*t))
  change (N : ℂ)^(-(k : ℂ)/2) *
      ((ofComplex (Complex.I*t) : ℍ) : ℂ)^(-k) *
      f (frickeReal N hN • ofComplex (Complex.I*t)) = η * f (ofComplex (Complex.I*t)) at he
  rw [frickeReal_axis N hN t ht] at he
  have hzt : ((ofComplex (Complex.I*t) : ℍ) : ℂ) = Complex.I*t := by
    rw [ofComplex_apply_of_im_pos (show 0 < (Complex.I * (t : ℂ)).im by simpa using ht)]
  rw [hzt] at he
  have hpow : (N : ℂ)^((k : ℂ)/2) * (N : ℂ)^(-(k : ℂ)/2) = 1 := by
    rw [← Complex.cpow_add _ _ hNC, show (k : ℂ)/2 + -(k : ℂ)/2 = 0 by ring,
      Complex.cpow_zero]
  have hzpow : (Complex.I * (t : ℂ))^k * (Complex.I * (t : ℂ))^(-k) = 1 := by
    rw [← zpow_add₀ hzC, add_neg_cancel, zpow_zero]
  have H := congrArg (fun x : ℂ => (N : ℂ)^((k : ℂ)/2) *
    (Complex.I * (t : ℂ))^k * x) he
  have hc : (N : ℂ)^((k : ℂ)/2) * (Complex.I * (t : ℂ))^k *
      ((N : ℂ)^(-(k : ℂ)/2) * (Complex.I * (t : ℂ))^(-k)) = 1 := by
    calc
      _ = ((N : ℂ)^((k : ℂ)/2) * (N : ℂ)^(-(k : ℂ)/2)) *
          ((Complex.I * (t : ℂ))^k * (Complex.I * (t : ℂ))^(-k)) := by ring
      _ = 1 := by rw [hpow, hzpow, one_mul]
  rw [← mul_assoc, hc, one_mul] at H
  rw [H, mul_zpow, Complex.cpow_intCast]
  ring

/-- The actual normalized Fricke eigenrelation implies the paper's
functional equation for the entire completion. -/
theorem entireCompletion_fricke_eigen (N k : ℕ) [NeZero N] (hN : 0 < N) (hk : 0 < k)
    (f : CuspForm (level N) (k : ℤ)) (η : ℂ)
    (heigen : normalizedFricke N hN (k : ℤ) f = η • (f : ℍ → ℂ)) (s : ℂ) :
    entireCompletion N k hk f s = (Complex.I^(k : ℤ) * η) *
      entireCompletion N k hk f (1-s) := by
  apply entireCompletion_reflection N k hk f (Complex.I^(k : ℤ) * η)
  intro t ht
  simpa only [Int.cast_natCast] using axial_fricke_of_eigen N hN (k : ℤ) f η heigen t ht

#print axioms frickeReal_action
#print axioms frickeReal_axis
#print axioms axial_fricke_of_eigen
#print axioms entireCompletion_fricke_eigen

end AsymptoticClassicalLSeries
