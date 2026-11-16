module

public import QuantitativeMaassLaplacianSupportV1
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Star

set_option autoImplicit false
@[expose] public noncomputable section

open Set
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

theorem dir_mul_smooth {u v : Point → ℂ} {s : Set Point} (hs : IsOpen s)
    (hu : ContDiffOn ℝ ∞ u s) (hv : ContDiffOn ℝ ∞ v s)
    {Z : Point} (hZ : Z∈s) (w : Point) :
    dir w (fun W => u W*v W) Z=dir w u Z*v Z+u Z*dir w v Z := by
  unfold dir D
  rw [fderiv_fun_mul ((hu.contDiffAt (hs.mem_nhds hZ)).differentiableAt (by simp))
    ((hv.contDiffAt (hs.mem_nhds hZ)).differentiableAt (by simp))]
  simp [mul_comm,add_comm]

theorem dir_star (u : Point → ℂ) (w Z : Point) :
    dir w (fun W => star (u W)) Z=star (dir w u Z) := by
  unfold dir D
  rw [fderiv_star (𝕜 := ℝ)]
  rfl

theorem dir_add_smooth {u v : Point → ℂ} {s : Set Point} (hs : IsOpen s)
    (hu : ContDiffOn ℝ ∞ u s) (hv : ContDiffOn ℝ ∞ v s)
    {Z : Point} (hZ : Z∈s) (w : Point) :
    dir w (fun W => u W+v W) Z=dir w u Z+dir w v Z := by
  unfold dir D
  rw [fderiv_fun_add ((hu.contDiffAt (hs.mem_nhds hZ)).differentiableAt (by simp))
    ((hv.contDiffAt (hs.mem_nhds hZ)).differentiableAt (by simp))]
  rfl

theorem dir2_mul_smooth {u v : Point → ℂ} {s : Set Point} (hs : IsOpen s)
    (hu : ContDiffOn ℝ ∞ u s) (hv : ContDiffOn ℝ ∞ v s)
    {Z : Point} (hZ : Z∈s) (w : Point) :
    dir w (dir w (fun W => u W*v W)) Z=
      dir w (dir w u) Z*v Z+2*dir w u Z*dir w v Z+u Z*dir w (dir w v) Z := by
  have hu' := dir_contDiffOn hu hs w
  have hv' := dir_contDiffOn hv hs w
  rw [dir_congr hs (fun W hW => dir_mul_smooth hs hu hv hW w) hZ w,
    dir_add_smooth hs (hu'.mul hv) (hu.mul hv') hZ w,
    dir_mul_smooth hs hu' hv hZ w,dir_mul_smooth hs hu hv' hZ w]
  ring

theorem dir2_star (u : Point → ℂ) (w Z : Point) :
    dir w (dir w (fun W => star (u W))) Z=star (dir w (dir w u) Z) := by
  have he : dir w (fun W => star (u W))=(fun W => star (dir w u W)) :=
    funext (fun W => dir_star u w W)
  rw [he,dir_star]

theorem hyperbolic_eq_dir2 {u : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2}) {Z : Point} (hZ : 0<Z.2) :
    hyperbolic u Z=-(Z.2:ℂ)^2*(dir e₁ (dir e₁ u) Z+dir e₂ (dir e₂ u) Z) := by
  have hs : IsOpen {Z : Point | 0<Z.2} := isOpen_lt continuous_const continuous_snd
  rw [show dir e₁ (dir e₁ u) Z=X (X u) Z from rfl,
    show dir e₂ (dir e₂ u) Z=Y (Y u) Z from rfl,
    XX_eq_deriv hu hs hZ,YY_eq_deriv hu hs hZ]
  simp only [hyperbolic,euclidean,Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_pow]

/-- The actual first-order hyperbolic energy density. -/
def hyperbolicEnergy (u v : Point → ℂ) (Z : Point) : ℂ :=
  (Z.2:ℂ)^2*(star (X u Z)*X v Z+star (Y u Z)*Y v Z)

/-- Exact carré-du-champ identity, derived from the literal real
derivatives. This will transfer energy covariance from Laplace covariance. -/
theorem hyperbolic_product_star {u v : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hv : ContDiffOn ℝ ∞ v {Z | 0<Z.2}) {Z : Point} (hZ : 0<Z.2) :
    hyperbolic (fun W => star (u W)*v W) Z=
      star (hyperbolic u Z)*v Z+star (u Z)*hyperbolic v Z-2*hyperbolicEnergy u v Z := by
  have hs : IsOpen {Z : Point | 0<Z.2} := isOpen_lt continuous_const continuous_snd
  have huS : ContDiffOn ℝ ∞ (fun W => star (u W)) {Z | 0<Z.2} :=
    (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn hu
  rw [hyperbolic_eq_dir2 (huS.mul hv) hZ,hyperbolic_eq_dir2 hu hZ,
    hyperbolic_eq_dir2 hv hZ,dir2_mul_smooth hs huS hv hZ e₁,
    dir2_mul_smooth hs huS hv hZ e₂]
  rw [dir2_star,dir2_star,dir_star,dir_star]
  unfold hyperbolicEnergy X Y
  simp only [star_add,star_mul,star_neg,star_pow,Complex.star_def,Complex.conj_ofReal]
  ring

theorem hyperbolicEnergy_self_nonneg (u : Point → ℂ) (Z : Point) :
    0≤(hyperbolicEnergy u u Z).re := by
  unfold hyperbolicEnergy
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul]
  apply mul_nonneg (sq_nonneg Z.2)
  simp only [Complex.add_re,Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im]
  nlinarith [sq_nonneg (X u Z).re,sq_nonneg (X u Z).im,
    sq_nonneg (Y u Z).re,sq_nonneg (Y u Z).im]

#print axioms hyperbolic_product_star
#print axioms hyperbolicEnergy_self_nonneg

end QuantitativeMaass
