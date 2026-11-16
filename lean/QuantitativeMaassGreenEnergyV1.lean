module

public import QuantitativeMaassGreenCylinderV1
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

def cylinderEnergy (w a b : ℝ) (u v : Point → ℂ) : ℂ :=
  ∫ Z, star (X u Z)*X v Z+star (Y u Z)*Y v Z ∂cylinderRectangle w a b

def cylinderLaplacianPairing (w a b : ℝ) (u v : Point → ℂ) : ℂ :=
  ∫ Z, star (u Z)*hyperbolic v Z/(Z.2:ℂ)^2 ∂cylinderRectangle w a b

theorem cylinderEnergy_integrable (w a b : ℝ) (ha : 0<a)
    {u v : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hv : ContDiffOn ℝ ∞ v {Z | 0<Z.2}) :
    Integrable (fun Z => star (X u Z)*X v Z+star (Y u Z)*Y v Z)
      (cylinderRectangle w a b) := by
  have hs : IsOpen {Z : Point | 0<Z.2} := isOpen_lt continuous_const continuous_snd
  have hc (F : Point → ℂ) (hF : ContDiffOn ℝ ∞ F {Z | 0<Z.2}) :
      ContinuousOn F (Icc 0 w ×ˢ Icc a b) :=
    hF.continuousOn.mono (fun _ hZ => lt_of_lt_of_le ha hZ.2.1)
  exact continuous_cylinderRectangle_integrable w a b
    (((hc _ (dir_contDiffOn hu hs e₁)).star.mul (hc _ (dir_contDiffOn hv hs e₁))).add
      ((hc _ (dir_contDiffOn hu hs e₂)).star.mul (hc _ (dir_contDiffOn hv hs e₂))))

theorem cylinderEnergy_conj (w a b : ℝ) (u v : Point → ℂ) :
    cylinderEnergy w a b u v=star (cylinderEnergy w a b v u) := by
  unfold cylinderEnergy
  simp only [← starRingEnd_apply]
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun Z => by simp [mul_comm]

theorem cylinderEnergy_nonneg (w a b : ℝ) (ha : 0<a)
    {u : Point → ℂ} (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2}) :
    0≤(cylinderEnergy w a b u u).re := by
  have hi := cylinderEnergy_integrable w a b ha hu hu
  change 0≤RCLike.re (∫ Z, star (X u Z)*X u Z+star (Y u Z)*Y u Z
    ∂cylinderRectangle w a b)
  rw [← integral_re hi]
  apply integral_nonneg
  intro Z
  change 0≤(star (X u Z)*X u Z+star (Y u Z)*Y u Z).re
  simp only [Complex.add_re,Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im]
  nlinarith [sq_nonneg (X u Z).re,sq_nonneg (X u Z).im,
    sq_nonneg (Y u Z).re,sq_nonneg (Y u Z).im]

/-- Actual symmetry of the cusp-cylinder hyperbolic Laplacian on smooth
periodic representatives with zero height-boundary values. -/
theorem cylinderLaplacianPairing_symmetric (w a b : ℝ)
    (hw : 0<w) (ha : 0<a) (hab : a≤b) {u v : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hv : ContDiffOn ℝ ∞ v {Z | 0<Z.2})
    (hpu : ∀ y, 0<y → Function.Periodic (fun x => u (x,y)) w)
    (hpv : ∀ y, 0<y → Function.Periodic (fun x => v (x,y)) w)
    (hua : ∀ x, u (x,a)=0) (hub : ∀ x, u (x,b)=0)
    (hva : ∀ x, v (x,a)=0) (hvb : ∀ x, v (x,b)=0) :
    cylinderLaplacianPairing w a b u v=star (cylinderLaplacianPairing w a b v u) := by
  unfold cylinderLaplacianPairing
  rw [green_cylinder w a b hw ha hab hu hv hpu hpv hua hub,
    green_cylinder w a b hw ha hab hv hu hpv hpu hva hvb]
  exact cylinderEnergy_conj w a b u v

theorem cylinderLaplacianPairing_nonneg (w a b : ℝ)
    (hw : 0<w) (ha : 0<a) (hab : a≤b) {u : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hpu : ∀ y, 0<y → Function.Periodic (fun x => u (x,y)) w)
    (hua : ∀ x, u (x,a)=0) (hub : ∀ x, u (x,b)=0) :
    0≤(cylinderLaplacianPairing w a b u u).re := by
  unfold cylinderLaplacianPairing
  rw [green_cylinder w a b hw ha hab hu hu hpu hpu hua hub]
  exact cylinderEnergy_nonneg w a b ha hu

#print axioms cylinderLaplacianPairing_symmetric
#print axioms cylinderLaplacianPairing_nonneg

end QuantitativeMaass
