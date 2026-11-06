module

public import AsymptoticHyperbolicSlashV1
public import FinitenessComplexGeometryV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticReconstructionBranch

open UpperHalfPlane Matrix

/-- The literal branch T_d W_L T_b of the finite reconstruction. Its
entries remain rational when L, b and d are rational. -/
def branch {K : Type*} [Field K] (L b d : K) (hL : L≠0) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![d*L,d*L*b-1;L,L*b] (by
    have hd : Matrix.det !![d*L,d*L*b-1;L,L*b]=L := by
      rw [Matrix.det_fin_two]
      change (d*L)*(L*b)-(d*L*b-1)*L=L
      ring
    rw [hd]
    exact hL)

theorem branch_det {K : Type*} [Field K] (L b d : K) (hL : L≠0) :
    (branch L b d hL).det.val=L := by
  change Matrix.det !![d*L,d*L*b-1;L,L*b]=L
  rw [Matrix.det_fin_two]
  change (d*L)*(L*b)-(d*L*b-1)*L=L
  ring

theorem branch_action {L : ℝ} (hL : 0<L) (b d : ℝ) (z : ℍ) :
    ((branch L b d hL.ne' • z : ℍ) : ℂ)= -1/((L:ℂ)*((z:ℂ)+(b:ℂ)))+(d:ℂ) := by
  rw [coe_smul_of_det_pos (by rw [branch_det]; exact hL)]
  change (((d*L:ℝ):ℂ)*(z:ℂ)+((d*L*b-1:ℝ):ℂ))/
    ((L:ℂ)*(z:ℂ)+((L*b:ℝ):ℂ))=_
  have hz : (z:ℂ)+(b:ℂ)≠0 := by
    intro he
    have hi := congrArg Complex.im he
    exact z.im_ne_zero (by simpa using hi)
  have hL' : (L:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hL.ne'
  have hd : (L:ℂ)*(z:ℂ)+(L:ℂ)*(b:ℂ)≠0 := by
    rw [← mul_add]
    exact mul_ne_zero hL' hz
  push_cast
  field_simp
  ring

theorem branch_im {L : ℝ} (hL : 0<L) (b d : ℝ) (z : ℍ) :
    (branch L b d hL.ne' • z).im=
      z.im/(L*((z.re+b)^2+z.im^2)) := by
  have he := congrArg Complex.im (branch_action hL b d z)
  have hi := FinitenessComplexGeometry.translated_reflected_im hL
    (show 0<((z:ℂ)+(b:ℂ)).im by simpa using z.im_pos) d
  simpa [FinitenessComplexGeometry.denominator] using he.trans hi

/-- Solving the literal Fricke branch gives the inverse-height formula
used for every integer fold, without discarding any inverse images. -/
theorem inverse_height {L : ℝ} (hL : 0<L) (b d : ℝ) (z : ℍ) :
    z.im=(branch L b d hL.ne' • z).im/
      (L*(((branch L b d hL.ne' • z).re-d)^2+(branch L b d hL.ne' • z).im^2)) := by
  let w : ℍ := branch L b d hL.ne' • z
  have hz : (z:ℂ)+(b:ℂ)≠0 := by
    intro he
    have hi := congrArg Complex.im he
    exact z.im_ne_zero (by simpa using hi)
  have hL' : (L:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hL.ne'
  have he : (z:ℂ)+(b:ℂ)= -1/((L:ℂ)*((w:ℂ)-(d:ℂ))) := by
    rw [show (w:ℂ)= -1/((L:ℂ)*((z:ℂ)+(b:ℂ)))+(d:ℂ) from branch_action hL b d z]
    simp only [add_sub_cancel_right]
    field_simp
  have hi := congrArg Complex.im he
  rw [FinitenessComplexGeometry.reflected_im hL
    (show 0<((w:ℂ)-(d:ℂ)).im by simpa using w.im_pos)] at hi
  simpa [FinitenessComplexGeometry.denominator,w] using hi

theorem folded_ratio {L : ℝ} (hL : 0<L) (b d : ℝ) (n : ℤ) (z : ℍ) :
    z.im/(branch L b (d-n) hL.ne' • z).im=
      (L*(((n:ℝ)+(branch L b (d-n) hL.ne' • z).re-d)^2+
        (branch L b (d-n) hL.ne' • z).im^2))⁻¹ := by
  let w : ℍ := branch L b (d-n) hL.ne' • z
  have hh := inverse_height hL b (d-n) z
  change z.im=w.im/(L*((w.re-(d-n))^2+w.im^2)) at hh
  change z.im/w.im=(L*(((n:ℝ)+w.re-d)^2+w.im^2))⁻¹
  have he : w.re-(d-(n:ℝ))=(n:ℝ)+w.re-d := by ring
  rw [hh,he]
  field_simp

theorem ratio_forward {L : ℝ} (hL : 0<L) (b d : ℝ) (z : ℍ) :
    z.im/(branch L b d hL.ne' • z).im=L*((z.re+b)^2+z.im^2) := by
  rw [branch_im hL]
  field_simp

#print axioms branch_action
#print axioms inverse_height
#print axioms folded_ratio
#print axioms ratio_forward

end AsymptoticReconstructionBranch
