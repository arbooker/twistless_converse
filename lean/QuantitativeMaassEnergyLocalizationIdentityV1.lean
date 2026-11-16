module

public import QuantitativeMaassLocalizationMassV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- Exact local energy identity for a real smooth multiplier. This is the
literal gradient calculation underlying the form-locality estimate. -/
theorem hyperbolicEnergy_localization_identity {u b : Point→ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2}) (hr : ∀ Z, star (b Z)=b Z)
    {Z : Point} (hZ : 0<Z.2) :
    (hyperbolicEnergy (fun W => b W*u W) (fun W => b W*u W) Z).re=
      (hyperbolicEnergy u (fun W => b W*(b W*u W)) Z).re+
      ‖u Z‖^2*(hyperbolicEnergy b b Z).re := by
  have hs : IsOpen {Z : Point | 0<Z.2} := isOpen_lt continuous_const continuous_snd
  have hbStar : (fun W => star (b W))=b := funext hr
  have hxStar : star (X b Z)=X b Z := by
    change star (dir e₁ b Z)=dir e₁ b Z
    rw [← dir_star,hbStar]
  have hyStar : star (Y b Z)=Y b Z := by
    change star (dir e₂ b Z)=dir e₂ b Z
    rw [← dir_star,hbStar]
  have hbIm : (b Z).im=0 := by
    have h := congrArg Complex.im (hr Z)
    simp only [Complex.star_def,Complex.conj_im] at h
    linarith
  have hxIm : (X b Z).im=0 := by
    have h := congrArg Complex.im hxStar
    simp only [Complex.star_def,Complex.conj_im] at h
    linarith
  have hyIm : (Y b Z).im=0 := by
    have h := congrArg Complex.im hyStar
    simp only [Complex.star_def,Complex.conj_im] at h
    linarith
  have hx := dir_mul_smooth hs hb hu hZ e₁
  have hy := dir_mul_smooth hs hb hu hZ e₂
  have hxx := dir_mul_smooth hs hb (hb.mul hu) hZ e₁
  have hyy := dir_mul_smooth hs hb (hb.mul hu) hZ e₂
  change X (fun W => b W*u W) Z=X b Z*u Z+b Z*X u Z at hx
  change Y (fun W => b W*u W) Z=Y b Z*u Z+b Z*Y u Z at hy
  change X (fun W => b W*(b W*u W)) Z=
    X b Z*(b Z*u Z)+b Z*X (fun W => b W*u W) Z at hxx
  change Y (fun W => b W*(b W*u W)) Z=
    Y b Z*(b Z*u Z)+b Z*Y (fun W => b W*u W) Z at hyy
  unfold hyperbolicEnergy
  rw [hxx,hyy,hx,hy]
  simp only [Complex.star_def,Complex.mul_re,Complex.mul_im,Complex.add_re,
    Complex.add_im,Complex.conj_re,Complex.conj_im,← Complex.ofReal_pow,
    Complex.ofReal_re,Complex.ofReal_im,hbIm,hxIm,hyIm]
  rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  ring

#print axioms hyperbolicEnergy_localization_identity

end QuantitativeMaass
