module

public import AsymptoticClassicalDiscriminantAffineV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalDiscriminant

open UpperHalfPlane Matrix
open scoped ModularForm

/-- A positive upper-triangular real matrix. -/
def triangularGL (a b d : ℝ) (ha : 0 < a) (hd : 0 < d) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d] (by
    simpa [Matrix.det_fin_two] using mul_ne_zero ha.ne' hd.ne')

theorem triangularGL_det (a b d : ℝ) (ha : 0 < a) (hd : 0 < d) :
    (triangularGL a b d ha hd).det.val = a * d := by
  simp [triangularGL, GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two]

theorem triangularGL_denom (a b d : ℝ) (ha : 0 < a) (hd : 0 < d) (z : ℍ) :
    denom (triangularGL a b d ha hd) z = (d : ℂ) := by
  simp [denom, triangularGL, GeneralLinearGroup.mkOfDetNeZero]

theorem triangularGL_action (a b d : ℝ) (ha : 0 < a) (hd : 0 < d) (z : ℍ) :
    triangularGL a b d ha hd • z = affine (a / d) (div_pos ha hd) (b / d) z := by
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (by rw [triangularGL_det]; exact mul_pos ha hd), triangularGL_denom]
  change ((a : ℂ) * z + b) / (d : ℂ) = ((a / d : ℝ) : ℂ) * z + ((b / d : ℝ) : ℂ)
  rw [Complex.ofReal_div, Complex.ofReal_div]
  ring

def triangularFactor (a d : ℝ) (k : ℤ) : ℂ := (a * d : ℝ) ^ (k - 1) * (d : ℂ) ^ (-k)

theorem triangularFactor_ne_zero (a d : ℝ) (ha : 0 < a) (hd : 0 < d) (k : ℤ) :
    triangularFactor a d k ≠ 0 := by
  unfold triangularFactor
  apply mul_ne_zero
  · exact zpow_ne_zero _ (Complex.ofReal_ne_zero.mpr (mul_ne_zero ha.ne' hd.ne'))
  · exact zpow_ne_zero _ (Complex.ofReal_ne_zero.mpr hd.ne')

/-- Exact affine formula for the GL slash action, retaining Mathlib's
 determinant normalization. -/
theorem slash_triangular (a b d : ℝ) (ha : 0 < a) (hd : 0 < d) (k : ℤ)
    (f : ℍ → ℂ) (z : ℍ) :
    (f ∣[k] triangularGL a b d ha hd) z =
      triangularFactor a d k * f (affine (a / d) (div_pos ha hd) (b / d) z) := by
  simp only [ModularForm.slash_def]
  rw [triangularGL_denom, triangularGL_det, triangularGL_action]
  simp only [σ, triangularGL_det, mul_pos ha hd, ite_true,
    ContinuousAlgEquiv.refl_apply, abs_of_pos (mul_pos ha hd)]
  simp only [triangularFactor]
  ring

#print axioms triangularGL_det
#print axioms triangularGL_denom
#print axioms triangularGL_action
#print axioms triangularFactor_ne_zero
#print axioms slash_triangular

end AsymptoticClassicalDiscriminant
