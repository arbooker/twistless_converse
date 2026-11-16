module

public import QuantitativeMaassEnergyDifferentialV1
public import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false
@[expose] public noncomputable section

open Set
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

theorem dir2_add_smooth {u v : Point → ℂ} {s : Set Point} (hs : IsOpen s)
    (hu : ContDiffOn ℝ ∞ u s) (hv : ContDiffOn ℝ ∞ v s)
    {Z : Point} (hZ : Z∈s) (w : Point) :
    dir w (dir w (fun W => u W+v W)) Z=dir w (dir w u) Z+dir w (dir w v) Z := by
  rw [dir_congr hs (fun W hW => dir_add_smooth hs hu hv hW w) hZ w]
  exact dir_add_smooth hs (dir_contDiffOn hu hs w) (dir_contDiffOn hv hs w) hZ w

theorem hyperbolic_add_smooth {u v : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hv : ContDiffOn ℝ ∞ v {Z | 0<Z.2}) {Z : Point} (hZ : 0<Z.2) :
    hyperbolic (u+v) Z=hyperbolic u Z+hyperbolic v Z := by
  have hs : IsOpen {Z : Point | 0<Z.2} := isOpen_lt continuous_const continuous_snd
  change hyperbolic (fun W => u W+v W) Z=_
  rw [hyperbolic_eq_dir2 (hu.add hv) hZ,hyperbolic_eq_dir2 hu hZ,hyperbolic_eq_dir2 hv hZ]
  change -(Z.2:ℂ)^2*(dir e₁ (dir e₁ (fun W => u W+v W)) Z+
    dir e₂ (dir e₂ (fun W => u W+v W)) Z)=_
  rw [dir2_add_smooth hs hu hv hZ e₁,dir2_add_smooth hs hu hv hZ e₂]
  ring

theorem hyperbolic_const_smul (c : ℂ) (u : Point → ℂ) (Z : Point) :
    hyperbolic (c•u) Z=c*hyperbolic u Z := by
  simp only [hyperbolic,euclidean,Pi.smul_apply,smul_eq_mul,deriv_const_mul_field',
    deriv_const_mul_field,Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_pow]
  ring

#print axioms hyperbolic_add_smooth
#print axioms hyperbolic_const_smul

end QuantitativeMaass
